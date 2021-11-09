#include "LemmasIterators.hpp"

#include "AnalysisPreComputation.hpp"
#include "Formula.hpp"
#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {

void IntermediateValueLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {

  static bool integerIts = util::Configuration::instance().integerIterations();

  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);
  auto it2Symbol = logic::Signature::varSymbol("it", logic::Sorts::iterSort());
  auto it2 = logic::Terms::var(it2Symbol);

  auto lStartIt = timepointForLoopStatement(statement, it);
  auto lStartIt2 = timepointForLoopStatement(statement, it2);
  auto lStartSuccOfIt =
      timepointForLoopStatement(statement, logic::Theory::succ(it));
  auto lStartSuccOfIt2 =
      timepointForLoopStatement(statement, logic::Theory::succ(it2));
  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::zero());

  auto posSymbol = posVarSymbol();
  auto pos = logic::Terms::var(posSymbol);
  auto xSymbol = logic::Signature::varSymbol("xInt", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSymbol);

  auto assignedVars =
      AnalysisPreComputation::computeAssignedVars(statement, false);

  // add lemma for each intVar and each intArrayVar
  for (const auto& v :
       locationToActiveVars.at(locationSymbolForStatement(statement)->name)) {
    if (!v->isConstant && assignedVars.find(v) != assignedVars.end()) {
      if (!v->isArray())  // We assume that loop counters are not array elements
                          // and therefore only add iterator-lemmas for
                          // non-array-vars
      {
        for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
             traceNumber++) {
          auto trace = traceTerm(traceNumber);
          auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);
          auto lStartN = timepointForLoopStatement(statement, n);

          auto nameSuffix =
              v->name + "-" + statement->location +
              (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");
          auto name = "iterator-intermediateValue-" + nameSuffix;
          auto nameShort = "Intermed-" + nameSuffix;
          auto inductionAxiomName = "induction-axiom-" + name;
          auto inductionAxiomNameShort = "Ax-" + nameShort;

          // PART 1: Add induction-axiom
          // IH(it): v(l(it1,...,itk,it)    ) <= x or
          //         v(l(it1,...,itk,it),pos) <= x

          auto inductionHypothesis =
              [&](std::shared_ptr<const logic::Term> arg) {
                auto lStartArg = timepointForLoopStatement(statement, arg);

                auto lhs = toTerm(v, lStartArg, trace);
                lhs = v->isArray() ? logic::Terms::arraySelect(lhs, pos) : lhs;
                return logic::Theory::intLessEqual(lhs, x);
              };

          auto freeVarSymbols1 = enclosingIteratorsSymbols(statement);
          if (v->isArray()) {
            freeVarSymbols1.push_back(posSymbol);
          }
          auto freeVarSymbols2 = freeVarSymbols1;
          freeVarSymbols2.push_back(xSymbol);

          auto [inductionAxBCDef, inductionAxICDef, inductionAxiomConDef,
                inductionAxiom] =
              logic::inductionAxiom1(inductionAxiomName,
                                     inductionAxiomNameShort,
                                     inductionHypothesis, freeVarSymbols2);
          items.push_back(inductionAxBCDef);
          items.push_back(inductionAxICDef);
          items.push_back(inductionAxiomConDef);
          items.push_back(inductionAxiom);

          // PART 2: Add trace lemma
          std::vector<std::shared_ptr<const logic::Term>> freeVars2 = {};

          for (const auto& symbol : freeVarSymbols2) {
            freeVars2.push_back(logic::Terms::var(symbol));
          }

          // PART 2A: Add definition for dense
          auto dense = getDensityFormula(freeVarSymbols1, nameSuffix, true);
          // Dense_v: forall it. (it<n => ( v(l(s(it))    )=v(l(it)    ) or
          // v(l(s(it))    )=v(l(it)    )+1 ) )         , or
          //          forall it. (it<n => ( v(l(s(it)),pos)=v(l(it),pos) or
          //          v(l(s(it)),pos)=v(l(it),pos)+1 ) )

          auto denseDefinition = getDensityDefinition(
              freeVarSymbols1, v, nameSuffix, itSymbol, it, lStartIt,
              lStartSuccOfIt, n, trace, true);

          auto denseDef = std::make_shared<logic::Definition>(
              denseDefinition, "Dense for " + nameSuffix,
              logic::ProblemItem::Visibility::Implicit);

          items.push_back(denseDef);

          // PART 2B: Add definition for premise
          auto premise =
              logic::Formulas::lemmaPredicate("Prem-" + nameShort, freeVars2);
          // Premise: v(l(zero))<=x     & x<v(l(n))     & Dense_v         , or
          //          v(l(zero),pos)<=x & x<v(l(n),pos) & Dense_v
          auto premiseFormula = logic::Formulas::conjunction(
              {logic::Theory::intLessEqual(
                    toTerm(v, lStartZero, trace), x),
               logic::Theory::intLess(
                   x, toTerm(v, lStartN, trace)),
               dense});
          auto premiseDef = std::make_shared<logic::Definition>(
              logic::Formulas::universal(
                  freeVarSymbols2,
                  logic::Formulas::equivalence(premise, premiseFormula)),
              "Premise for " + name, logic::ProblemItem::Visibility::Implicit);

          // only add named premise if we don't use inlined lemmas
          if (!util::Configuration::instance().inlineLemmas()) {
            items.push_back(premiseDef);
          }

          // PART 2C: Add lemma
          // Conclusion: exists it2. (it2<n & v(l(it2)    )=x & v(l(s(it2))
          // )=v(l(it2)    )+1) or
          //             exists it2. (it2<n & v(l(it2),pos)=x &
          //             v(l(s(it2)),pos)=v(l(it2),pos)+1)

          auto lhs1 = toTerm(v, lStartIt2, trace);
          auto lhs2 = toTerm(v, lStartSuccOfIt2, trace);
          auto rhs = toTerm(v, lStartIt2, trace);

          auto conjunctFirst = integerIts ? 
              logic::Theory::intLessEqual(logic::Theory::intZero(), it) :
              logic::Theory::boolTrue();

          auto conclusion = logic::Formulas::existential(
              {it2Symbol},
              logic::Formulas::conjunctionSimp({
                  conjunctFirst,
                  logic::Theory::less(it2, n),
                  logic::Formulas::equality(lhs1, x),
                  logic::Formulas::equality(
                      lhs2, logic::Theory::intAddition(
                                rhs, logic::Theory::intConstant(1))),
              }));
          // forall enclosingIterators. forall x. (premise => conclusion) or
          // forall enclosingIterators. forall x,pos. (premise => conclusion)
          auto lemma = logic::Formulas::universal(
              freeVarSymbols2,
              logic::Formulas::implication(premise, conclusion));
          std::vector<std::string> fromItems = {inductionAxBCDef->name,
                                                inductionAxICDef->name,
                                                inductionAxiomConDef->name,
                                                inductionAxiom->name,
                                                denseDef->name,
                                                premiseDef->name};

          if (util::Configuration::instance().inlineLemmas()) {
            lemma = logic::Formulas::universal(
                freeVarSymbols2,
                logic::Formulas::implication(premiseFormula, conclusion));
            fromItems = {inductionAxBCDef->name, inductionAxICDef->name,
                         inductionAxiomConDef->name, inductionAxiom->name,
                         denseDef->name};
          }

          items.push_back(std::make_shared<logic::Lemma>(
              lemma, name, logic::ProblemItem::Visibility::Implicit,
              fromItems));

          if(integerIts){
            // Note for integer encoding it makes sense to add a second notion of
            // strict density to derive i(l(0)) + it = i(l(it)) PART 2A: Add
            // definition for strict dense
            auto denseStrict =
                getDensityFormula(freeVarSymbols1, "strict-" + nameSuffix, true);

            // Dense_v: forall it. (0≤it<n => ( v(l(s(it))    )=v(l(it)    )+1 ) )
            // , or
            //          forall it. (0≤it<n => ( v(l(s(it)),pos)=v(l(it),pos)+1 ) )
            auto denseStrictFormula = logic::Formulas::universal(
                {itSymbol},
                logic::Formulas::implication(
                    logic::Formulas::conjunction({
                        logic::Theory::intLessEqual(logic::Theory::intZero(), it),
                        logic::Theory::intLess(it, n),
                    }),
                    logic::Formulas::equality(toTerm(v, lStartSuccOfIt, trace),
                        logic::Theory::intAddition(toTerm(v, lStartIt, trace),
                            logic::Theory::intConstant(1)))
                        ));
            auto denseStrictDef = std::make_shared<logic::Definition>(
                logic::Formulas::universal(freeVarSymbols1,
                                           logic::Formulas::equivalence(
                                               denseStrict, denseStrictFormula)),
                "Dense-strict for " + nameSuffix,
                logic::ProblemItem::Visibility::Implicit);

            items.push_back(denseStrictDef);

            // PART 3B: Add lemma
            // Dense-strict-v-l => forall it. (0≤it<n => ( v(l(it)) = v(l(0)) + it
            // ) )
            auto lemmaStrict = logic::Formulas::implication(
                denseStrict,
                logic::Formulas::universal(
                    {itSymbol},
                    logic::Formulas::implication(
                        logic::Formulas::conjunction({
                            logic::Theory::intLessEqual(logic::Theory::intZero(), it),
                            logic::Theory::intLess(it, n),
                        }),
                        logic::Formulas::equality(toTerm(v, lStartIt, trace),
                            logic::Theory::intAddition(toTerm(v, lStartIt, trace),
                                it)))));

            items.push_back(std::make_shared<logic::Definition>(
                lemmaStrict, "Strict density for " + nameSuffix,
                logic::ProblemItem::Visibility::Implicit));
          }
        }
      }
    }
  }
} 


void IterationInjectivityLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {

  static bool integerIts = util::Configuration::instance().integerIterations();

  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);
  auto it1Symbol =
      logic::Signature::varSymbol("it1", logic::Sorts::iterSort());
  auto it1 = logic::Terms::var(it1Symbol);
  auto it2Symbol =
      logic::Signature::varSymbol("it2", logic::Sorts::iterSort());
  auto it2 = logic::Terms::var(it2Symbol);

  auto lStartIt = timepointForLoopStatement(statement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(statement, logic::Theory::succ(it));
  auto lStartIt1 = timepointForLoopStatement(statement, it1);
  auto lStartSuccOfIt1 =
      timepointForLoopStatement(statement, logic::Theory::succ(it1));
  auto lStartIt2 = timepointForLoopStatement(statement, it2);

  auto assignedVars = AnalysisPreComputation::computeAssignedVars(statement);

  // add lemma for each intVar
  for (const auto& v :
       locationToActiveVars.at(locationSymbolForStatement(statement)->name)) {
    if (!v->isConstant && assignedVars.find(v) != assignedVars.end()) {
      if (!v->isArray())  // We assume that loop counters are not array elements
                        // and therefore only add iterator-lemmas for
                        // non-array-vars
      {
        for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
             traceNumber++) {
          auto trace = traceTerm(traceNumber);
          auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);

          auto nameSuffix =
              v->name + "-" + statement->location +
              (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");
          auto name = "iterator-injectivity-" + nameSuffix;
          auto nameShort = "Injec-" + nameSuffix;
          auto inductionAxiomName = "induction-axiom-" + name;
          auto inductionAxiomNameShort = "Ax-" + nameShort;

          auto freeVarSymbols = enclosingIteratorsSymbols(statement);

          auto freeVarSymbolsInd = freeVarSymbols;
          freeVarSymbolsInd.push_back(it1Symbol);

          // PART 1: Add induction-axiom
          // IH(arg): v(l(it1)) < v(l(arg))
          auto inductionHypothesis =
              [&](std::shared_ptr<const logic::Term> arg) {
                auto lStartArg = timepointForLoopStatement(statement, arg);
                return logic::Theory::intLess(toTerm(v, lStartIt1, trace),
                                              toTerm(v, lStartArg, trace));
              };

          auto [inductionAxBCDef, inductionAxICDef, inductionAxiomConDef,
                inductionAxiom] =
              logic::inductionAxiom1(inductionAxiomName,
                                     inductionAxiomNameShort,
                                     inductionHypothesis, freeVarSymbolsInd);
          items.push_back(inductionAxBCDef);
          items.push_back(inductionAxICDef);
          items.push_back(inductionAxiomConDef);
          items.push_back(inductionAxiom);

          // PART 2: Add trace lemma

          // PART 2A: Add definition for stronglyDense
          auto dense = getDensityFormula(freeVarSymbols, nameSuffix, true);

          // TODO: refactor, currently depends on the following facts
          // - the dense-definition is generated as part of the
          // intermediate-value lemma
          // - the intermediate-value-lemma is generated before the
          // corresponding injectivity-lemma is generated
          // - the name of the definition matches the name used here.
          auto denseDefName = "Dense for " + nameSuffix;

          auto conjunct = integerIts ? 
              logic::Theory::intLessEqual(logic::Theory::intZero(), it) :
              logic::Theory::boolTrue();

          /* Premise:
           *    and
           *       Dense_v
           *       v(l(s(it1))) = v(l(it1)) + 1
           *       it1<it2
           *       it2<=n
           */
          auto premise = logic::Formulas::conjunctionSimp({
              dense,
              logic::Formulas::equality(
                  toTerm(v, lStartSuccOfIt1, trace),
                  logic::Theory::intAddition(toTerm(v, lStartIt1, trace),
                                             logic::Theory::intConstant(1))),
              conjunct,
              logic::Theory::less(it1, it2),
              logic::Theory::lessEq(it2, n),
          });

          // Conclusion: v(l(it1))!=v(l(it2))
          auto conclusion = logic::Formulas::disequality(
              toTerm(v, lStartIt1, trace), toTerm(v, lStartIt2, trace));

          // forall enclosingIterators. forall it1,it2. (premise =>
          // conclusion)
          auto lemma = logic::Formulas::universal(
              freeVarSymbols,
              logic::Formulas::universal(
                  {it1Symbol, it2Symbol},
                  logic::Formulas::implication(premise, conclusion)));

          std::vector<std::string> fromItems = {
              inductionAxBCDef->name, inductionAxICDef->name,
              inductionAxiomConDef->name, inductionAxiom->name, denseDefName};
          items.push_back(std::make_shared<logic::Lemma>(
              lemma, name, logic::ProblemItem::Visibility::Implicit,
              fromItems));
        }
      }
    }
  }
}

}  // namespace analysis
