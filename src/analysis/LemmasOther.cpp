#include "LemmasOther.hpp"

#include <cassert>

#include "Formula.hpp"
#include "Options.hpp"
#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {

void AtLeastOneIterationLemmas::generateOutputFor(
  const program::WhileStatement* statement,
  std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {

  static bool integerIts = util::Configuration::instance().integerIterations();

  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);

  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::zero());

  auto conjunctLeft = integerIts ? 
      logic::Theory::intLessEqual(logic::Theory::intZero(), it) :
      logic::Theory::boolTrue();


  for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
       traceNumber++) {
    auto trace = traceTerm(traceNumber);
    auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);

    auto name = "atLeastOneIteration-" + statement->location +
                (numberOfTraces > 1 ? ("-" + trace->symbol->name) : "");

    // forall enclosingIterators. (Cond(l(0)) => exists it. s(it)=n)
    auto bareLemma = logic::Formulas::universal(
        enclosingIteratorsSymbols(statement),
        logic::Formulas::implication(
            util::Configuration::instance().inlineSemantics()
                ? inlinedVarValues.toInlinedFormula(
                      statement, statement->condition, lStartZero, trace)
                : toFormula(statement->condition, lStartZero, trace),
            logic::Formulas::existential(
                {itSymbol},
                logic::Formulas::conjunctionSimp(
                  {conjunctLeft,
                   logic::Formulas::equality(logic::Theory::succ(it), n)}))));

    std::vector<std::string> fromItems;
    for (auto& item : programSemantics) {
      fromItems.push_back(item->name);
    }
    items.push_back(std::make_shared<logic::Lemma>(
        bareLemma, name, logic::ProblemItem::Visibility::Implicit,
        fromItems));
  } 
}

void LoopConditionAnalysisLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(statement);

  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);

  auto lStartIt = timepointForLoopStatement(statement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(statement, logic::Theory::succ(it));
  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::zero());

  auto cond = statement->condition;

  for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
       traceNumber++) {
    auto trace = traceTerm(traceNumber);
    auto n = lastIterationTermForLoop(statement, numberOfTraces, trace);
    auto lStartN = timepointForLoopStatement(statement, n);


    if (cond->type() == program::BoolExpression::Type::ArithmeticComparison) {

      auto condCasted =
          std::static_pointer_cast<const program::ArithmeticComparison>(cond);
      if (condCasted->kind != program::ArithmeticComparison::Kind::EQ) {
        auto left = condCasted->child1;
        auto right = condCasted->child2;
        if (AnalysisPreComputation::doNotOccurIn(assignedVars, right)) {
          auto newLeft = toTerm(left, lStartZero, trace);
          auto newRight = toTerm(right, lStartZero, trace);

          auto concLeft = toTerm(left, lStartN, trace);
          auto concRight = toTerm(right, lStartN, trace);

          auto op = condCasted->kind;
          bool lessThan = false;

          switch (op) {
            case program::ArithmeticComparison::Kind::LT: {
              lessThan = true;
              break;
            }

            case program::ArithmeticComparison::Kind::LE: {
              lessThan = true;
              auto one = logic::Theory::intConstant(1);
              newRight = logic::Theory::intAddition(newRight, one);
              break;
            }

            case program::ArithmeticComparison::Kind::GT: {
              break;
            }

            default: {
              // the equality case should never occur
              auto one = logic::Theory::intConstant(1);
              newRight = logic::Theory::intSubtraction(newRight, one);
              break;
            }
          }

          auto freeVarSymbols = enclosingIteratorsSymbols(statement);

          auto prem1 =
              lessThan ? logic::Theory::intLessEqual(newLeft, newRight)
                       : logic::Theory::intGreaterEqual(newLeft, newRight);

          auto leftStr = left->toString();
          auto rightStr = right->toString();

          leftStr.erase(std::remove(leftStr.begin(), leftStr.end(), ' '),
                        leftStr.end());
          leftStr.erase(std::remove(leftStr.begin(), leftStr.end(), ')'),
                        leftStr.end());
          leftStr.erase(std::remove(leftStr.begin(), leftStr.end(), '('),
                        leftStr.end());

          rightStr.erase(std::remove(rightStr.begin(), rightStr.end(), ' '),
                         rightStr.end());
          rightStr.erase(std::remove(rightStr.begin(), rightStr.end(), ')'),
                         rightStr.end());
          rightStr.erase(std::remove(rightStr.begin(), rightStr.end(), '('),
                         rightStr.end());

          auto nameSuffix = leftStr + "-" + statement->location;

          auto densityDef = getDensityDefinition(
              freeVarSymbols, left, nameSuffix, itSymbol, it, lStartIt,
              lStartSuccOfIt, n, trace, lessThan);

          std::string direction = lessThan ? "increasing" : "decreasing";
          auto denseDef = std::make_shared<logic::Definition>(
              densityDef, "Dense-" + direction + " for " + nameSuffix,
              logic::ProblemItem::Visibility::Implicit);

          items.push_back(denseDef);

          auto dense =
              getDensityFormula(freeVarSymbols, nameSuffix, lessThan);
          auto prem = logic::Formulas::conjunction({dense, prem1});
          auto conc = logic::Formulas::equality(concLeft, concRight);

          auto lemma = logic::Formulas::universal(
              freeVarSymbols, logic::Formulas::implication(prem, conc));

          // TODO don't understand all this implicit explicit business
          items.push_back(std::make_shared<logic::Lemma>(
              lemma, leftStr + "-" + rightStr + "-" + "equality-axiom",
              logic::ProblemItem::Visibility::Implicit));
        }
      }
    }
  }
}


}  // namespace analysis
