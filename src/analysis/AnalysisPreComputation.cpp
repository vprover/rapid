#include "AnalysisPreComputation.hpp"

#include <cassert>
#include <memory>

#include "Options.hpp"
#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {
EndTimePointMap AnalysisPreComputation::computeEndTimePointMap(
    const program::Program &program) {
  EndTimePointMap endTimePointMap;
  for (const auto &function : program.functions) {
    // for each statement except the first, set the end-location of the previous
    // statement to the begin-location of this statement
    for (int i = 1; i < function->statements.size(); ++i) {
      auto lastStatement = function->statements[i - 1].get();
      auto nextTimepoint =
          startTimepointForStatement(function->statements[i].get());
      addEndTimePointForStatement(lastStatement, nextTimepoint,
                                  endTimePointMap);
    }
    // for the last statement, set the end-location to be the end-location of
    // the function.
    auto lastStatement = function->statements.back().get();
    auto nextTimepoint =
        logic::Terms::func(locationSymbolEndLocation(function.get()), {});
    addEndTimePointForStatement(lastStatement, nextTimepoint, endTimePointMap);
  }
  return endTimePointMap;
}

void AnalysisPreComputation::addEndTimePointForStatement(
    program::Statement *statement,
    const std::shared_ptr<const logic::Term> nextTimepoint,
    EndTimePointMap &endTimePointMap) {
  // for an ifElse statement, set endTimepoint and recurse
  if (typeid(*statement) == typeid(program::IfElseStatement)) {
    endTimePointMap[statement] = nextTimepoint;
    auto castedStatement = static_cast<program::IfElseStatement*>(statement);
    addEndTimePointForIfElseStatement(castedStatement, nextTimepoint,
                                      endTimePointMap);
  }
  // for a while statement, set endTimepoint and recurse
  else if (typeid(*statement) == typeid(program::WhileStatement)) {
    endTimePointMap[statement] = nextTimepoint;

    auto castedStatement = static_cast<program::WhileStatement*>(statement);
    addEndTimePointForWhileStatement(castedStatement, nextTimepoint,
                                     endTimePointMap);
  }
  // set endTimepoint for atomic statement
  else {
    assert(typeid(*statement) == typeid(program::Assignment) ||
           typeid(*statement) == typeid(program::SkipStatement));
    endTimePointMap[statement] = nextTimepoint;
  }
}

void AnalysisPreComputation::addEndTimePointForIfElseStatement(
    program::IfElseStatement *ifElse,
    const std::shared_ptr<const logic::Term> nextTimepoint,
    EndTimePointMap &endTimePointMap) {
  // for each statement in the left branch except the first, set the
  // end-location of the previous statement to the begin-location of this
  // statement
  for (int i = 1; i < ifElse->ifStatements.size(); ++i) {
    auto lastStatement = ifElse->ifStatements[i - 1].get();
    auto nextTimepointForStatement =
        startTimepointForStatement(ifElse->ifStatements[i].get());
    addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                                endTimePointMap);
  }
  // for each statement in the right branch except the first, set the
  // end-location of the previous statement to the begin-location of this
  // statement
  for (int i = 1; i < ifElse->elseStatements.size(); ++i) {
    auto lastStatement = ifElse->elseStatements[i - 1].get();
    auto nextTimepointForStatement =
        startTimepointForStatement(ifElse->elseStatements[i].get());
    addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                                endTimePointMap);
  }
  // for both left and right branch, set the endTimePoint of the
  // ifElse-statement as endTimePoint for the last statement
  auto lastStatementLeft = ifElse->ifStatements.back().get();
  auto lastStatementRight = ifElse->elseStatements.back().get();
  addEndTimePointForStatement(lastStatementLeft, nextTimepoint,
                              endTimePointMap);
  addEndTimePointForStatement(lastStatementRight, nextTimepoint,
                              endTimePointMap);
}

void AnalysisPreComputation::addEndTimePointForWhileStatement(
    program::WhileStatement *whileStatement,
    const std::shared_ptr<const logic::Term> nextTimepoint,
    EndTimePointMap &endTimePointMap) {
  // for each statement in the body except the first, set the end-location of
  // the previous statement to the begin-location of this statement
  for (int i = 1; i < whileStatement->bodyStatements.size(); ++i) {
    auto lastStatement = whileStatement->bodyStatements[i - 1].get();
    auto nextTimepointForStatement =
        startTimepointForStatement(whileStatement->bodyStatements[i].get());
    addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                                endTimePointMap);
  }

  // for the last statement in the body, set as end-timepoint the start-location
  // of the while-statement in the next iteration
  auto lastStatement = whileStatement->bodyStatements.back().get();
  auto nextTimepointForStatement = timepointForLoopStatement(
      whileStatement, logic::Theory::succ(iteratorTermForLoop(whileStatement)));
  addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                              endTimePointMap);
}

std::unordered_set<std::shared_ptr<program::Variable>>
AnalysisPreComputation::computeAssignedVars(program::Statement *statement) {
  std::unordered_set<std::shared_ptr<program::Variable>> assignedVars;

  if (typeid(*statement) == typeid(program::Assignment)) {
    auto castedStatement = static_cast<program::Assignment *>(statement);
    // add variable on lhs to assignedVars, independently from whether those
    // vars are simple ones or arrays.
    if (typeid(*castedStatement->lhs) == typeid(program::VariableAccess)) {
      auto access =
          static_cast<program::VariableAccess *>(castedStatement->lhs.get());
      assignedVars.insert(access->var);
    } else {
      assert(typeid(*castedStatement->lhs) ==
             typeid(program::ArrayApplication));
      auto arrayAccess =
          static_cast<program::ArrayApplication *>(castedStatement->lhs.get());
      assignedVars.insert(arrayAccess->array);
    }
  } else if (typeid(*statement) == typeid(program::IfElseStatement)) {
    auto castedStatement = static_cast<program::IfElseStatement *>(statement);
    // collect assignedVars from both branches
    for (const auto &statement : castedStatement->ifStatements) {
      auto res = computeAssignedVars(statement.get());
      assignedVars.insert(res.begin(), res.end());
    }
    for (const auto &statement : castedStatement->elseStatements) {
      auto res = computeAssignedVars(statement.get());
      assignedVars.insert(res.begin(), res.end());
    }
  } else if (typeid(*statement) == typeid(program::WhileStatement)) {
    auto castedStatement = static_cast<program::WhileStatement *>(statement);
    // collect assignedVars from body
    for (const auto &statement : castedStatement->bodyStatements) {
      auto res = computeAssignedVars(statement.get());
      assignedVars.insert(res.begin(), res.end());
    }
  } else {
    assert(typeid(*statement) == typeid(program::SkipStatement));
  }
  return assignedVars;
}

void AnalysisPreComputation::computeVariablesContainedInLoopCondition(
    std::shared_ptr<program::Expression> expr,
    std::unordered_set<std::shared_ptr<program::Variable>> &variables) {
  assert(expr != nullptr);
  if (typeid(*expr) == typeid(program::Addition)) {
    auto castedExpr = std::static_pointer_cast<program::Addition>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::Subtraction)) {
    auto castedExpr = std::static_pointer_cast<program::Subtraction>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::Multiplication)) {
    auto castedExpr = std::static_pointer_cast<program::Multiplication>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::Modulo)) {
    auto castedExpr = std::static_pointer_cast<program::Modulo>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::VariableAccess)) {
    auto castedExpr = std::static_pointer_cast<program::VariableAccess>(expr);
    variables.insert(castedExpr->var);
    return;
  } else if (typeid(*expr) == typeid(program::ArrayApplication)) {
    auto castedExpr = std::static_pointer_cast<program::ArrayApplication>(expr);
    variables.insert(castedExpr->array);
    computeVariablesContainedInLoopCondition(castedExpr->index, variables);
    return;
  } else if (typeid(*expr) == typeid(program::BooleanAnd)) {
    auto castedExpr = std::static_pointer_cast<program::BooleanAnd>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::BooleanOr)) {
    auto castedExpr = std::static_pointer_cast<const program::BooleanOr>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::BooleanNot)) {
    auto castedExpr = std::static_pointer_cast<const program::BooleanNot>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child, variables);
    return;
  } else if (typeid(*expr) == typeid(program::ArithmeticComparison)) {
    auto castedExpr =
        std::static_pointer_cast<const program::ArithmeticComparison>(expr);
    computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
    computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
    return;
  } else if (typeid(*expr) == typeid(program::ArithmeticConstant) ||
             typeid(*expr) == typeid(program::BooleanConstant)) {
    // do nothing
    return;
  } else {
    assert(0);
  }
}
}  // namespace analysis
