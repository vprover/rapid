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

  static bool integerIts = util::Configuration::instance().integerIterations();

  auto boundLSymbol =
      logic::Signature::varSymbol("boundL", logic::Sorts::iterSort());
  auto boundRSymbol =
      logic::Signature::varSymbol("boundR", logic::Sorts::iterSort());

  auto boundL = logic::Terms::var(boundLSymbol);
  auto boundR = logic::Terms::var(boundRSymbol);
  auto it = iteratorTermForLoop(whileStatement);

  auto lStartBoundL = timepointForLoopStatement(whileStatement, boundL);
  auto lStartboundR = timepointForLoopStatement(whileStatement, boundR);
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(whileStatement, logic::Theory::succ(it));

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

        if (v->isPointer() && predicateString != "eq") {
          // only equality makes sense for pointer variables
          break;
        }

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
                auto lhs = toTerm(v, lStartBoundL, trace);
                auto rhs = toTerm(v, lStartArg, trace);
                if (v->isArray()) {
                  lhs = logic::Terms::arraySelect(lhs, pos);
                  rhs = logic::Terms::arraySelect(rhs, pos);
                }

                return predicateFunctor(lhs, rhs, "");
              };

          auto freeVars = enclosingIteratorsSymbols(whileStatement);
          if (v->isArray()) {
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

          auto lhs = toTerm(v, lStartBoundL, trace);
          auto rhs1 = toTerm(v, lStartIt, trace);
          auto rhs2 = toTerm(v, lStartSuccOfIt, trace);
          if (v->isArray()) {
            lhs = logic::Terms::arraySelect(lhs, pos);
            rhs1 = logic::Terms::arraySelect(rhs1, pos);
            rhs2 = logic::Terms::arraySelect(rhs2, pos);
          }

          auto conjunct = integerIts ? 
              logic::Theory::intLessEqual(logic::Theory::intZero(), boundL) :
              logic::Theory::boolTrue();

          auto premiseFormula = logic::Formulas::universal(
              {it->symbol}, logic::Formulas::implication(
                                logic::Formulas::conjunctionSimp(
                                    {conjunct,
                                     logic::Theory::lessEq(boundL, it),
                                     logic::Theory::less(it, boundR),
                                     predicateFunctor(lhs, rhs1, "")}),
                                predicateFunctor(lhs, rhs2, "")));
          auto premiseDef = std::make_shared<logic::Definition>(
              logic::Formulas::universal(
                  argSymbols,
                  logic::Formulas::equivalence(premise, premiseFormula)),
              "Premise for " + name, logic::ProblemItem::Visibility::Implicit);
          
          // only add named premise if we don't use inlined lemmas
          if (!util::Configuration::instance().inlineLemmas()) {
            items.push_back(premiseDef);
          }

          // Part 2B: Define lemma:
          // boundL<=boundR => IH(boundR)
          auto conclusionFormula = logic::Formulas::implication(
              logic::Formulas::conjunctionSimp({
                logic::Theory::lessEq(boundL, boundR),
                conjunct
              }),
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

          if (util::Configuration::instance().inlineLemmas()) {
            lemma = logic::Formulas::universal(
                argSymbols, logic::Formulas::implication(premiseFormula,
                                                         conclusionFormula));
            fromItems = {inductionAxBCDef->name, inductionAxICDef->name,
                         inductionAxiomConDef->name, inductionAxiom->name};
          }

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
  static bool integerIts = util::Configuration::instance().integerIterations();  
  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);

  auto lStartIt = timepointForLoopStatement(statement, it);
  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::natZero());

  auto posSymbol = posVarSymbol();
  auto pos = posVar();

  auto activeVars = locationToActiveVars.at(statement->location);
  auto [p2p, p2i] = derefAssignementsInLoop(statement);
  auto assignedVars =
      AnalysisPreComputation::computeAssignedVars(statement, true);

  auto notAssignedTo = [&, p2p = p2p,
                        p2i = p2i](std::shared_ptr<const program::Variable> v) {
    // over approximation that should be improved
    if (!v->isPointer() && p2i) {
      return false;
    }
    if (v->isPointer() && p2p) {
      return false;
    }

    return assignedVars.find(v) == assignedVars.end();
  };

  // for each active var, which is not constant but not assigned to in any
  // statement of the loop, add a lemma asserting that var is the same in each
  // iteration as in the first iteration.
  for (const auto& v : activeVars) {
    if (!v->isConstant && notAssignedTo(v)) {
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
          auto lhs = toTerm(v, lStartZero, trace);
          if (v->isArray()) {
            lhs = logic::Terms::arraySelect(lhs, pos);
          }

          auto rhs = toTerm(v, lStartArg, trace);
          if (v->isArray()) {
            rhs = logic::Terms::arraySelect(rhs, pos);
          }

          return logic::Formulas::equality(lhs, rhs);
        };

        // PART 1: Add induction-axiom
        auto freeVars = enclosingIteratorsSymbols(statement);
        if (v->isArray()) {
          freeVars.push_back(posSymbol);
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
            logic::Formulas::implication(logic::Theory::lessEq(it, n),
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

std::pair<bool, bool> StaticAnalysisLemmas::derefAssignementsInLoop(
    const program::Statement* statement) {
  bool p2pDerefAssigned = false;
  bool p2iDerefAssigned = false;

  switch (statement->type()) {
    case program::Statement::Type::Assignment: {
      auto casted = static_cast<const program::Assignment*>(statement);
      if (casted->lhs->type() == program::Type::PointerDeref) {
        if(casted->lhs->exprType()->isPointerToPointer()){
          p2pDerefAssigned = true;
        } else {
          p2iDerefAssigned = true; 
        }
      }
      break;
    }
    case program::Statement::Type::IfElse: {
      auto castedStatement = static_cast<const program::IfElse*>(statement);
      for (const auto& statement : castedStatement->ifStatements) {
        auto [b1, b2] = derefAssignementsInLoop(statement.get());
        if (b1) {
          p2pDerefAssigned = true;
        }
        if (b2) {
          p2iDerefAssigned = true;
        }
      }
      for (const auto& statement : castedStatement->elseStatements) {
        auto [b1, b2] = derefAssignementsInLoop(statement.get());
        if (b1) {
          p2pDerefAssigned = true;
        }
        if (b2) {
          p2iDerefAssigned = true;
        }

      }
      break;
    }
    case program::Statement::Type::WhileStatement: {
      auto castedStatement =
          static_cast<const program::WhileStatement*>(statement);
      for (const auto& statement : castedStatement->bodyStatements) {
        auto [b1, b2] = derefAssignementsInLoop(statement.get());
        if (b1) {
          p2pDerefAssigned = true;
        }
        if (b2) {
          p2iDerefAssigned = true;
        }
      }
      break;
    }
    case program::Statement::Type::VarDecl:
    case program::Statement::Type::SkipStatement: {
      break;
    }
  }
  return std::make_pair(p2pDerefAssigned, p2iDerefAssigned);
}

}  // namespace analysis

