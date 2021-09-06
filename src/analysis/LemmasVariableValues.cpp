#include "LemmasVariableValues.hpp"

#include <cassert>
#include <utility>

#include "AnalysisPreComputation.hpp"
#include "Formula.hpp"
#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {

void ValueEvolutionLemmas::generateOutputFor(
    const program::WhileStatement* whileStatement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto boundLSymbol =
      logic::Signature::varSymbol("boundL", logic::Sorts::natSort());
  auto boundRSymbol =
      logic::Signature::varSymbol("boundR", logic::Sorts::natSort());

  auto boundL = logic::Terms::var(boundLSymbol);
  auto boundR = logic::Terms::var(boundRSymbol);
  auto it = iteratorTermForLoop(whileStatement);

  auto lStartBoundL = timepointForLoopStatement(whileStatement, boundL);
  auto lStartboundR = timepointForLoopStatement(whileStatement, boundR);
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(whileStatement, logic::Theory::natSucc(it));

  auto posSymbol = posVarSymbol();
  auto pos = posVar();

  auto predicates = {
      std::make_pair(logic::Formulas::equality, std::string("eq")),
      std::make_pair(logic::Theory::intLessEqual, std::string("leq")),
      std::make_pair(logic::Theory::intGreaterEqual, std::string("geq"))};

  auto assignedVars =
      AnalysisPreComputation::computeAssignedVars(whileStatement);

  // add lemma for each intVar and each intArrayVar, for each variant
  for (const auto& v : locationToActiveVars.at(
           locationSymbolForStatement(whileStatement)->name)) {
    if (!(v->isConstant) && assignedVars.find(v) != assignedVars.end()) {
      for (const auto predicate : predicates) {
        auto predicateFunctor = predicate.first;
        auto predicateString = predicate.second;

        for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
             traceNumber++) {
          auto trace = traceTerm(traceNumber);

          auto nameSuffix =
              "-" + predicateString + "-" + v->name + "-" +
              whileStatement->location +
              (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");
          auto name = "value-evolution" + nameSuffix;
          auto nameShort = "Evol" + nameSuffix;
          auto inductionAxiomName = "induction-axiom-" + name;
          auto inductionAxiomNameShort = "Ax" + nameShort;

          // PART 1: Add induction-axiom
          // IH(it): v(l(it1,...,itk,boundL)    ) C v(l(it1,...,itk,it)    ),
          // where C in {=,<=,>=} or
          //         v(l(it1,...,itk,boundL),pos) C v(l(it1,...,itk,it),pos),
          //         where C in {=,<=,>=}
          auto inductionHypothesis =
              [&](std::shared_ptr<const logic::Term> arg) {
                auto lStartArg = timepointForLoopStatement(whileStatement, arg);
                return predicateFunctor(
                    v->isArray ? toTerm(v, lStartBoundL, pos, trace)
                               : toTerm(v, lStartBoundL, trace),
                    v->isArray ? toTerm(v, lStartArg, pos, trace)
                               : toTerm(v, lStartArg, trace),
                    "");
              };

          auto freeVars = enclosingIteratorsSymbols(whileStatement);
          if (v->isArray) {
            freeVars.push_back(posSymbol);
          }

          auto [inductionAxBCDef, inductionAxICDef, inductionAxiomConDef,
                inductionAxiom] =
              inductionAxiom1(inductionAxiomName, inductionAxiomNameShort,
                              inductionHypothesis, freeVars);
          items.push_back(inductionAxBCDef);
          items.push_back(inductionAxICDef);
          items.push_back(inductionAxiomConDef);
          items.push_back(inductionAxiom);

          // PART 2: Add trace lemma
          auto argSymbols = freeVars;
          argSymbols.push_back(boundLSymbol);
          argSymbols.push_back(boundRSymbol);

          std::vector<std::shared_ptr<const logic::Term>> args = {};
          for (const auto& symbol : argSymbols) {
            args.push_back(logic::Terms::var(symbol));
          }

          // Part 2A: Add definition for premise:
          auto premise =
              logic::Formulas::lemmaPredicate("Prem" + nameShort, args);
          // forall it. (( boundL<=it<boundR and IH(it) ) => IH(s(it)) ), where
          // C in {=,<=,>=}
          auto premiseFormula = logic::Formulas::universal(
              {it->symbol},
              logic::Formulas::implication(
                  logic::Formulas::conjunction(
                      {logic::Theory::natSubEq(boundL, it),
                       logic::Theory::natSub(it, boundR),
                       predicateFunctor(
                           v->isArray ? toTerm(v, lStartBoundL, pos, trace)
                                      : toTerm(v, lStartBoundL, trace),
                           v->isArray ? toTerm(v, lStartIt, pos, trace)
                                      : toTerm(v, lStartIt, trace),
                           "")}),
                  predicateFunctor(
                      v->isArray ? toTerm(v, lStartBoundL, pos, trace)
                                 : toTerm(v, lStartBoundL, trace),
                      v->isArray ? toTerm(v, lStartSuccOfIt, pos, trace)
                                 : toTerm(v, lStartSuccOfIt, trace),
                      "")));
          auto premiseDef = std::make_shared<logic::Definition>(
              logic::Formulas::universal(
                  argSymbols,
                  logic::Formulas::equivalence(premise, premiseFormula)),
              "Premise for " + name, logic::ProblemItem::Visibility::Implicit);
          items.push_back(premiseDef);

          // Part 2B: Define lemma:
          // boundL<=boundR => IH(boundR)
          auto conclusionFormula = logic::Formulas::implication(
              logic::Theory::natSubEq(boundL, boundR),
              inductionHypothesis(boundR));
          // forall enclosingIterators: forall boundL,boundR. (Premise =>
          // Conclusion) or forall enclosingIterators: forall boundL,boundR.
          // forall pos. (Premise => Conclusion)
          auto lemma = logic::Formulas::universal(
              argSymbols,
              logic::Formulas::implication(premise, conclusionFormula));
          std::vector<std::string> fromItems = {
              inductionAxBCDef->name, inductionAxICDef->name,
              inductionAxiomConDef->name, inductionAxiom->name,
              premiseDef->name};
          items.push_back(std::make_shared<logic::Lemma>(
              lemma, name, logic::ProblemItem::Visibility::Implicit,
              fromItems));
        }
      }
    }
  }
}

void StaticAnalysisLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);

  auto lStartIt = timepointForLoopStatement(statement, it);
  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::natZero());

  auto posSymbol = posVarSymbol();
  auto pos = posVar();

  auto activeVars = locationToActiveVars.at(statement->location);
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(statement);

  // for each active var, which is not constant but not assigned to in any
  // statement of the loop, add a lemma asserting that var is the same in each
  // iteration as in the first iteration.
  for (const auto& v : activeVars) {
    if (!v->isConstant && assignedVars.find(v) == assignedVars.end()) {
      for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
           traceNumber++) {
        auto trace = traceTerm(traceNumber);

        auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);
        auto lStartN = timepointForLoopStatement(statement, n);

        auto nameSuffix =
            "-" + v->name + "-" + statement->location +
            (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");
        auto name = "value-static" + nameSuffix;
        auto nameShort = "Static" + nameSuffix;
        auto inductionAxiomName = "induction-axiom-" + name;
        auto inductionAxiomNameShort = "Ax" + nameShort;

        // IH(it): v(l(it1,...,itk,zero)    ) = v(l(it1,...,itk,it)    ) or
        //         v(l(it1,...,itk,zero),pos) = v(l(it1,...,itk,it),pos)
        auto inductionHypothesis = [&](std::shared_ptr<const logic::Term> arg) {
          auto lStartArg = timepointForLoopStatement(statement, arg);
          return logic::Formulas::equality(
              v->isArray ? toTerm(v, lStartZero, pos, trace)
                         : toTerm(v, lStartZero, trace),
              v->isArray ? toTerm(v, lStartArg, pos, trace)
                         : toTerm(v, lStartArg, trace));
        };

        auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement);

        // add lemma for each intVar and each intArrayVar, for each variant
        for (const auto& v : locationToActiveVars.at(locationSymbolForStatement(whileStatement)->name))
        {
            if (!(v->isConstant) && v->type() != program::ValueType::Bool && assignedVars.find(v) != assignedVars.end())
            {
                for (const auto predicate : predicates)
                {
                    auto predicateFunctor = predicate.first;
                    auto predicateString = predicate.second;

                    for (unsigned traceNumber = 1; traceNumber < numberOfTraces+1; traceNumber++)
                    {
                        auto trace = traceTerm(traceNumber);

                        auto nameSuffix = "-" + predicateString + "-" + v->name + "-" + whileStatement->location + (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");
                        auto name = "value-evolution" + nameSuffix;
                        auto nameShort = "Evol" + nameSuffix;
                        auto inductionAxiomName = "induction-axiom-" + name;
                        auto inductionAxiomNameShort = "Ax" + nameShort;

                        // PART 1: Add induction-axiom
                        // IH(it): v(l(it1,...,itk,boundL)    ) C v(l(it1,...,itk,it)    ), where C in {=,<=,>=} or
                        //         v(l(it1,...,itk,boundL),pos) C v(l(it1,...,itk,it),pos), where C in {=,<=,>=}
                        auto inductionHypothesis = [&](std::shared_ptr<const logic::Term> arg)
                        {
                            auto lStartArg = timepointForLoopStatement(whileStatement, arg);
                            return predicateFunctor(
                                v->isArray ? toTerm(v, lStartBoundL, pos, trace) : toTerm(v,lStartBoundL,trace),
                                v->isArray ? toTerm(v, lStartArg, pos, trace) : toTerm(v,lStartArg, trace),
                                ""
                            );
                        };

                        auto freeVars = enclosingIteratorsSymbols(whileStatement);
                        if (v->isArray)
                        {
                            freeVars.push_back(posSymbol);
                        }

                        auto [inductionAxBCDef, inductionAxICDef,inductionAxiomConDef, inductionAxiom] = inductionAxiom1(inductionAxiomName, inductionAxiomNameShort, inductionHypothesis, freeVars);
                        items.push_back(inductionAxBCDef);
                        items.push_back(inductionAxICDef);
                        items.push_back(inductionAxiomConDef);
                        items.push_back(inductionAxiom);

                        // PART 2: Add trace lemma
                        auto argSymbols = freeVars;
                        argSymbols.push_back(boundLSymbol);
                        argSymbols.push_back(boundRSymbol);

                        std::vector<std::shared_ptr<const logic::Term>> args = {};
                        for (const auto& symbol : argSymbols)
                        {
                            args.push_back(logic::Terms::var(symbol));
                        }

                        // Part 2A: Add definition for premise:
                        auto premise = logic::Formulas::lemmaPredicate("Prem" + nameShort, args);
                        // forall it. (( boundL<=it<boundR and IH(it) ) => IH(s(it)) ), where C in {=,<=,>=}
                        auto premiseFormula =
                            logic::Formulas::universal({it->symbol},
                                logic::Formulas::implication(
                                    logic::Formulas::conjunction({
                                        logic::Theory::natSubEq(boundL, it),
                                        logic::Theory::natSub(it, boundR),
                                        predicateFunctor(
                                            v->isArray ? toTerm(v,lStartBoundL,pos,trace) : toTerm(v,lStartBoundL,trace),
                                            v->isArray ? toTerm(v,lStartIt,pos,trace) : toTerm(v,lStartIt,trace),
                                            ""
                                        )
                                    }),
                                    predicateFunctor(
                                        v->isArray ? toTerm(v,lStartBoundL,pos,trace) : toTerm(v,lStartBoundL,trace),
                                        v->isArray ? toTerm(v,lStartSuccOfIt,pos,trace) : toTerm(v,lStartSuccOfIt,trace),
                                        ""
                                    )
                                )
                            );
                        auto premiseDef =
                            std::make_shared<logic::Definition>(
                                logic::Formulas::universal(argSymbols,
                                    logic::Formulas::equivalence(
                                        premise,
                                        premiseFormula
                                    )
                                ),
                                "Premise for " + name,
                                logic::ProblemItem::Visibility::Implicit
                            );
                        items.push_back(premiseDef);

                        // Part 2B: Define lemma:
                        //boundL<=boundR => IH(boundR)
                        auto conclusionFormula =
                            logic::Formulas::implication(
                                logic::Theory::natSubEq(boundL, boundR),
                                inductionHypothesis(boundR)
                            );
                        // forall enclosingIterators: forall boundL,boundR. (Premise => Conclusion) or
                        // forall enclosingIterators: forall boundL,boundR. forall pos. (Premise => Conclusion)
                        auto lemma =
                            logic::Formulas::universal(argSymbols,
                                logic::Formulas::implication(premise, conclusionFormula)
                            );
                        std::vector<std::string> fromItems = {inductionAxBCDef->name, inductionAxICDef->name, inductionAxiomConDef->name, inductionAxiom->name, premiseDef->name};
                        items.push_back(std::make_shared<logic::Lemma>(lemma, name, logic::ProblemItem::Visibility::Implicit, fromItems));
                    }
                }
            }
        }

        auto [inductionAxBCDef, inductionAxICDef, inductionAxiomConDef,
              inductionAxiom] =
            logic::inductionAxiom1(inductionAxiomName, inductionAxiomNameShort,
                                   inductionHypothesis, freeVars);
        items.push_back(inductionAxBCDef);
        items.push_back(inductionAxICDef);
        items.push_back(inductionAxiomConDef);
        items.push_back(inductionAxiom);

        // PART 2: Add trace lemma
        auto argSymbols = freeVars;
        argSymbols.push_back(itSymbol);

        // forall enclosing iterators. {forall pos.} forall it. (it<=n =>
        // IH(it))
        auto lemma = logic::Formulas::universal(
            argSymbols,
            logic::Formulas::implication(logic::Theory::natSubEq(it, n),
                                         inductionHypothesis(it)));

        std::vector<std::string> fromItems = {
            inductionAxBCDef->name, inductionAxICDef->name,
            inductionAxiomConDef->name, inductionAxiom->name};
        for (auto& item : programSemantics) {
          fromItems.push_back(item->name);
        }

        items.push_back(std::make_shared<logic::Lemma>(
            lemma, name, logic::ProblemItem::Visibility::Implicit, fromItems));
      }
    }
  }
}
}  // namespace analysis
