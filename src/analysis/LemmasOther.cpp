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
  if (util::Configuration::instance().integerIterations()) {
    AtLeastOneIterationLemmas::generateOutputForInteger(statement, items);
  } else {
    auto itSymbol = iteratorSymbol(statement);
    auto it = iteratorTermForLoop(statement);

    auto lStartZero =
        timepointForLoopStatement(statement, logic::Theory::natZero());

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
                  logic::Formulas::equality(logic::Theory::natSucc(it), n))));

      std::vector<std::string> fromItems;
      for (auto& item : programSemantics) {
        fromItems.push_back(item->name);
      }
      items.push_back(std::make_shared<logic::Lemma>(
          bareLemma, name, logic::ProblemItem::Visibility::Implicit,
          fromItems));
    }
  }
}

void AtLeastOneIterationLemmas::generateOutputForInteger(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto itSymbol = iteratorSymbol(statement);
  auto it = iteratorTermForLoop(statement);

  auto lStartZero =
      timepointForLoopStatement(statement, logic::Theory::intZero());

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
                logic::Formulas::conjunction(
                    {logic::Theory::intLessEqual(logic::Theory::intZero(), it),
                     logic::Formulas::equality(logic::Theory::intSucc(it),
                                               n)}))));

    std::vector<std::string> fromItems;
    for (auto& item : programSemantics) {
      fromItems.push_back(item->name);
    }
    items.push_back(std::make_shared<logic::Lemma>(
        bareLemma, name, logic::ProblemItem::Visibility::Implicit, fromItems));
  }
}

bool LoopConditionAnalysisLemmas::doesNotChangeInLoop(
    std::unordered_set<std::shared_ptr<const program::Variable>>& assignedVars,
    std::shared_ptr<const program::IntExpression> expr) {
  switch (expr->type()) {
    case program::IntExpression::Type::IntVariableAccess: {
      auto var =
          std::static_pointer_cast<const program::IntVariableAccess>(expr);
      return assignedVars.find(var->var) == assignedVars.end();
    }
    case program::IntExpression::Type::Addition: {
      auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
      return doesNotChangeInLoop(assignedVars, castedExpr->summand1) &&
             doesNotChangeInLoop(assignedVars, castedExpr->summand2);
    }
    case program::IntExpression::Type::Subtraction: {
      auto castedExpr =
          std::static_pointer_cast<const program::Subtraction>(expr);
      return doesNotChangeInLoop(assignedVars, castedExpr->child1) &&
             doesNotChangeInLoop(assignedVars, castedExpr->child2);
    }
    case program::IntExpression::Type::Modulo: {
      auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
      return doesNotChangeInLoop(assignedVars, castedExpr->child1) &&
             doesNotChangeInLoop(assignedVars, castedExpr->child2);
    }
    case program::IntExpression::Type::Multiplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::Multiplication>(expr);
      return doesNotChangeInLoop(assignedVars, castedExpr->factor1) &&
             doesNotChangeInLoop(assignedVars, castedExpr->factor2);
    }
    case program::IntExpression::Type::ArithmeticConstant: {
      return true;
    }
    case program::IntExpression::Type::IntArrayApplication: {
      auto var =
          std::static_pointer_cast<const program::IntArrayApplication>(expr);
      return assignedVars.find(var->array) == assignedVars.end();
    }
    default:
      // should never happen
      return false;
  }
}

void LoopConditionAnalysisLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(statement);

  if (util::Configuration::instance().integerIterations()) {
    // TODO add for integers
    // AtLeastOneIterationLemmas::generateOutputForInteger(statement, items);
  } else {
    auto itSymbol = iteratorSymbol(statement);
    auto it = iteratorTermForLoop(statement);

    auto lStartIt = timepointForLoopStatement(statement, it);
    auto lStartSuccOfIt =
        timepointForLoopStatement(statement, logic::Theory::natSucc(it));
    auto lStartZero =
        timepointForLoopStatement(statement, logic::Theory::natZero());

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
          if (doesNotChangeInLoop(assignedVars, right)) {
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
                lemma, leftStr + "-" + rightStr + "-" + "equality-axiom" + std::to_string(rand()),
                logic::ProblemItem::Visibility::Implicit));
          }
        }
      }
    }
  }
}

void OrderingSynchronizationLemmas::generateOutputFor(
    const program::WhileStatement* statement,
    std::vector<std::shared_ptr<const logic::ProblemItem>>& items) {
  // assert(numberOfTraces > 1);

  // auto t1 = traceTerm(1);
  // auto t2 = traceTerm(2);

  // auto iSymbol = iteratorSymbol(statement);
  // auto it = iteratorTermForLoop(statement);
  // auto it1Symbol = logic::Signature::varSymbol("it1",
  // logic::Sorts::natSort()); auto it1 = logic::Terms::var(it1Symbol); auto
  // it2Symbol = logic::Signature::varSymbol("it2", logic::Sorts::natSort());
  // auto it2 = logic::Terms::var(it2Symbol);

  // auto lStartIt = timepointForLoopStatement(statement, it);
  // auto lStartZero = timepointForLoopStatement(statement,
  // logic::Theory::natZero()); auto lStartSuccOfIt =
  // timepointForLoopStatement(statement, logic::Theory::natSucc(it)); auto
  // lStartIt1 = timepointForLoopStatement(statement, it1); auto lStartIt2 =
  // timepointForLoopStatement(statement, it2);

  // auto trSymbol = traceVarSymbol();
  // auto tr = traceVar();
  // auto tr3Symbol = logic::Signature::varSymbol("tr3",
  // logic::Sorts::traceSort()); auto tr3 = logic::Terms::var(tr3Symbol);

  // // add lemma for each intVar
  // // Lemma:
  // // forall ((tr : Trace) (it1 : Nat) (it2 : Nat))
  // //    =>
  // //       and
  // //          it1 < it2
  // //          v(l(zero),t1) = v(l(zero),t2)
  // //          forall ((it : Nat))
  // //             v(l(s(it))) = v(l(it)) + 1
  // //       i(l(it1),tr) < i(l(it2),tr)
  // for (const auto& v :
  // locationToActiveVars.at(locationSymbolForStatement(statement)->name))
  // {
  //     if (!v->isConstant)
  //     {
  //         if (!v->isArray)
  //         {
  //             // Premise: it1<it2 & v(l(zero),t1)=v(l(zero),t2) & forall it.
  //             v(l(s(it)))=v(l(it))+1 auto premise =
  //                 logic::Formulas::conjunction({
  //                     logic::Theory::natSub(it1,it2),
  //                     logic::Formulas::equality(
  //                         toTerm(v,lStartZero,t1),
  //                         toTerm(v,lStartZero,t2)
  //                     ),
  //                     logic::Formulas::universal({tr3Symbol,iSymbol},
  //                         logic::Formulas::equality(
  //                             toTerm(v,lStartSuccOfIt,tr3),
  //                             logic::Theory::intAddition(
  //                                 toTerm(v,lStartIt,tr3),
  //                                 logic::Theory::intConstant(1)
  //                             )
  //                         )
  //                     )
  //                 });

  //             // Conclusion: i(l(it1),tr) < i(l(it2),tr)
  //             auto conclusion =
  //                 logic::Theory::intLess(
  //                     toTerm(v,lStartIt1,tr),
  //                     toTerm(v,lStartIt2,tr)
  //                 );

  //             // forall enclosingIterators. forall tr,it1,it2. (premise =>
  //             conclusion) auto bareLemma =
  //                 logic::Formulas::universal(enclosingIteratorsSymbols(statement),
  //                     logic::Formulas::universal({trSymbol,it1Symbol,it2Symbol},
  //                         logic::Formulas::implication(premise,conclusion)
  //                     )
  //                 );

  //             auto name = "synchronization-orderings-" + v->name + "-" +
  //             statement->location;
  //             items.push_back(std::make_shared<logic::Lemma>(bareLemma,
  //             name));
  //         }
  //     }
  // }
}
}  // namespace analysis
