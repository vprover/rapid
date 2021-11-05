#include "LemmasVariableDiffs.hpp"

#include <cassert>
#include <iostream>

#include "AnalysisPreComputation.hpp"
#include "Formula.hpp"
#include "Options.hpp"
#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {

void VariableDiffLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  bool toIntUsed = false;
  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::natZero());

  // auto assignedVars = AnalysisPreComputation::computeAssignedVars(statement);

  // add lemma for each intVar and each intArrayVar
  for (const auto& v :
       locationToActiveVars.at(locationSymbolForStatement(statement)->name)) {
    // we could do something clever with arrays perhaps
    if (v->isConstant || v->isArray()) {
      continue;
    }

    for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
         traceNumber++) {
      auto trace = traceTerm(traceNumber);
      auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);
      auto lStartN = timepointForLoopStatement(statement, n);

      int diff = 0;
      if (!getDiff(v, statement, diff, true)) {
        break;
      }

      auto varAtStart = toTerm(v, lStartZero, trace);
      auto varAtEnd = toTerm(v, lStartN, trace);

      bool subtract = false;
      if (diff < 0) {
        diff = -1 * diff;
        subtract = true;
      }

      if (diff) {
        addToIntAxs = true;
        auto diffTerm = logic::Theory::intConstant(diff);
        auto toIntN = logic::Theory::toInt(n);

        // 1 * n = n
        auto diffTermXMaxLoops =
            diff == 1 ? toIntN
                      : logic::Theory::intMultiplication(diffTerm, toIntN);
        auto rhs =
            subtract
                ? logic::Theory::intSubtraction(varAtStart, diffTermXMaxLoops)
                : logic::Theory::intAddition(varAtStart, diffTermXMaxLoops);

        auto formula = logic::Formulas::equality(varAtEnd, rhs);

        // TODO do we really want an Axiom here?
        items.push_back(std::make_shared<logic::Axiom>(formula));
      } else {
        auto formula = logic::Formulas::equality(varAtEnd, varAtStart);
        items.push_back(std::make_shared<logic::Axiom>(formula));
      }
    }
  }
}

void VariableDiffLemmas::addToIntAxioms(
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto natSym1 = logic::Signature::varSymbol("n1", logic::Sorts::natSort());
  auto natSym2 = logic::Signature::varSymbol("n2", logic::Sorts::natSort());
  auto n1 = logic::Terms::var(natSym1);
  auto n2 = logic::Terms::var(natSym2);

  // TODO add more axioms

  auto injectivityAxiom = logic::Formulas::universal(
      {natSym1, natSym2},
      logic::Formulas::implication(
          logic::Formulas::equality(n1, n2),
          logic::Formulas::equality(logic::Theory::toInt(n1),
                                    logic::Theory::toInt(n2))));

  // TODO do we really want an Axiom here?
  items.push_back(std::make_shared<logic::Axiom>(injectivityAxiom));
}

}  // namespace analysis