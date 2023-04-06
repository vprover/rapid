#include "AnalysisPreComputation.hpp"

#include <cassert>
#include <memory>

#include "SemanticsHelper.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

namespace analysis {

const program::Statement*
AnalysisPreComputation::getNextProperStatement(
  std::vector<std::shared_ptr<const program::Statement>> statements,
  unsigned currPos){

  auto type = statements[currPos].get()->type();

  while (type == program::Statement::Type::VarDecl ||
         type == program::Statement::Type::Assertion ||
         type == program::Statement::Type::Assumption) {
    currPos = currPos + 1;
    if(currPos >= statements.size()){
      return 0;
    }
    type = statements[currPos].get()->type();
  }
  assert(currPos < statements.size());
  return statements[currPos].get();  
}


EndTimePointMap AnalysisPreComputation::computeEndTimePointMap(
    const program::Program& program) {

  EndTimePointMap endTimePointMap;
  for (const auto& function : program.functions) {
    // for each statement except the first, set the end-location of the previous
    // statement to the begin-location of this statement

    auto tpEndOfBlock = 
      logic::Terms::func(locationSymbolEndLocation(function.get()), {});

    for (int i = 1; i < function->statements.size(); ++i) {
      auto lastStatement = function->statements[i - 1].get();

      auto nextStatement = getNextProperStatement(function->statements, i);
      auto nextTimepoint = nextStatement ? startTimepointForStatement(nextStatement) :
                                           tpEndOfBlock;
      addEndTimePointForStatement(lastStatement, nextTimepoint, endTimePointMap);
    }
    // for the last statement, set the end-location to be the end-location of
    // the function.
    auto lastStatement = function->statements.back().get();
    auto nextTimepoint =
        logic::Terms::func(locationSymbolEndLocation(function.get()), {});
    addEndTimePointForStatement(lastStatement, tpEndOfBlock, endTimePointMap);
  }
  return endTimePointMap;
}

void AnalysisPreComputation::addEndTimePointForStatement(
    const program::Statement* statement,
    const std::shared_ptr<const logic::Term> nextTimepoint,
    EndTimePointMap& endTimePointMap) {
  // for an ifElse statement, set endTimepoint and recurse
  if (statement->type() == program::Statement::Type::IfElse) {
    endTimePointMap[statement] = nextTimepoint;
    auto castedStatement = static_cast<const program::IfElse*>(statement);
    addEndTimePointForIfElseStatement(castedStatement, nextTimepoint,
                                      endTimePointMap);
  }
  // for a while statement, set endTimepoint and recurse
  else if (statement->type() == program::Statement::Type::WhileStatement) {
    endTimePointMap[statement] = nextTimepoint;

    auto castedStatement =
        static_cast<const program::WhileStatement*>(statement);
    addEndTimePointForWhileStatement(castedStatement, endTimePointMap);
  }
  // set endTimepoint for atomic statement
  else {
    assert(statement->type() == program::Statement::Type::Assignment ||
           statement->type() == program::Statement::Type::SkipStatement ||
           statement->type() == program::Statement::Type::VarDecl ||
           statement->type() == program::Statement::Type::Assertion ||
           statement->type() == program::Statement::Type::Assumption);
    endTimePointMap[statement] = nextTimepoint;
  }
}

void AnalysisPreComputation::addEndTimePointForIfElseStatement(
    const program::IfElse* ifElse,
    const std::shared_ptr<const logic::Term> nextTimepoint,
    EndTimePointMap& endTimePointMap) {
  // for each statement in the left branch except the first, set the
  // end-location of the previous statement to the begin-location of this
  // statement
  for (int i = 1; i < ifElse->ifStatements.size(); ++i) {
    auto lastStatement = ifElse->ifStatements[i - 1].get();
    auto nextStatement = getNextProperStatement(ifElse->ifStatements, i);
    auto nextTimepointForStatement = nextStatement ? 
      startTimepointForStatement(nextStatement) : nextTimepoint;
    addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                                endTimePointMap);
  }
  // for each statement in the right branch except the first, set the
  // end-location of the previous statement to the begin-location of this
  // statement
  for (int i = 1; i < ifElse->elseStatements.size(); ++i) {
    auto lastStatement = ifElse->elseStatements[i - 1].get();
    auto nextStatement = getNextProperStatement(ifElse->elseStatements, i);    
    auto nextTimepointForStatement = nextStatement ? 
      startTimepointForStatement(nextStatement) : nextTimepoint;
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
    const program::WhileStatement* whileStatement,
    EndTimePointMap& endTimePointMap) {

  auto tpEndOfBlock = 
    timepointForLoopStatement(
    whileStatement,
    logic::Theory::succ(iteratorTermForLoop(whileStatement)));

  // for each statement in the body except the first, set the end-location of
  // the previous statement to the begin-location of this statement
  for (int i = 1; i < whileStatement->bodyStatements.size(); ++i) {
    auto lastStatement = whileStatement->bodyStatements[i - 1].get();
    auto nextStatement = getNextProperStatement(whileStatement->bodyStatements, i);    
    auto nextTimepointForStatement = nextStatement ? 
      startTimepointForStatement(nextStatement) : tpEndOfBlock;
    addEndTimePointForStatement(lastStatement, nextTimepointForStatement,
                                endTimePointMap);
  }

  // for the last statement in the body, set as end-timepoint the start-location
  // of the while-statement in the next iteration
  auto lastStatement = whileStatement->bodyStatements.back().get();
  addEndTimePointForStatement(lastStatement, tpEndOfBlock,
                             endTimePointMap);
}

std::map<std::string, std::unordered_set<std::string>>
AnalysisPreComputation::computeAssignedFields(const program::Statement* statement) {
  std::map<std::string, std::unordered_set<std::string>> fields;

  auto customMerge = [](std::map<std::string, std::unordered_set<std::string>>& map1,
                        std::map<std::string, std::unordered_set<std::string>>& map2){

    for(auto& [key, value] : map2){
      if(map1.contains(key)){
        map1[key].merge(value);
      } else {
        map1[key] = value;
      }
    }
  };

  switch (statement->type()) {
    case program::Statement::Type::Assignment: {
      auto casted = static_cast<const program::Assignment*>(statement);
      // add variable on lhs to assignedVars, independently from whether those
      // vars are simple ones or arrays.
      if (casted->lhs->type() == program::Type::FieldAccess) {
        auto access = static_cast<const program::StructFieldAccess*>(
            casted->lhs.get());
        auto structName = toSort(access->getStruct()->exprType())->name;
        auto fieldName = logic::toLower(structName) + "_" + access->getField()->name;
         
        fields[structName].insert(fieldName);
      }
      break;
    }
    case program::Statement::Type::IfElse: {
      auto castedStatement = static_cast<const program::IfElse*>(statement);
      // collect assignedVars from both branches
      for (const auto& statement : castedStatement->ifStatements) {
        auto res = computeAssignedFields(statement.get());
        customMerge(fields, res);
      }
      for (const auto& statement : castedStatement->elseStatements) {
        auto res = computeAssignedFields(statement.get());
        customMerge(fields, res);
      }
      break;
    }
    case program::Statement::Type::WhileStatement: {
      auto castedStatement =
          static_cast<const program::WhileStatement*>(statement);
      // collect assignedVars from body
      for (const auto& statement : castedStatement->bodyStatements) {
        auto res = computeAssignedFields(statement.get());
        customMerge(fields, res);
      }
      break;
    }
    case program::Statement::Type::SkipStatement:
    case program::Statement::Type::Assumption:
    case program::Statement::Type::Assertion:
    case program::Statement::Type::VarDecl: {
      break;
    }
  }

  return fields;
}


std::unordered_set<std::shared_ptr<const program::Variable>>
AnalysisPreComputation::computeAssignedVars(const program::Statement* statement,
                                            bool pointerVars) {
  std::unordered_set<std::shared_ptr<const program::Variable>> assignedVars;

  switch (statement->type()) {
    case program::Statement::Type::Assignment: {
      auto casted = static_cast<const program::Assignment*>(statement);
      // add variable on lhs to assignedVars, independently from whether those
      // vars are simple ones or arrays.
      if (casted->lhs->type() == program::Type::VariableAccess) {
        auto access = static_cast<const program::VariableAccess*>(
            casted->lhs.get());
        if((casted->lhs->isPointerExpr() && pointerVars) || 
           !casted->lhs->isPointerExpr()){
          assignedVars.insert(access->var);
        }
      } else if (casted->lhs->type() == program::Type::IntArrayApplication) {
        auto arrayAccess =
            static_cast<const program::IntArrayApplication*>(casted->lhs.get());
        assignedVars.insert(arrayAccess->array);
      }
      break;
    }
    case program::Statement::Type::IfElse: {
      auto castedStatement = static_cast<const program::IfElse*>(statement);
      // collect assignedVars from both branches
      for (const auto& statement : castedStatement->ifStatements) {
        auto res = computeAssignedVars(statement.get(), pointerVars);
        assignedVars.insert(res.begin(), res.end());
      }
      for (const auto& statement : castedStatement->elseStatements) {
        auto res = computeAssignedVars(statement.get(), pointerVars);
        assignedVars.insert(res.begin(), res.end());
      }
      break;
    }
    case program::Statement::Type::WhileStatement: {
      auto castedStatement =
          static_cast<const program::WhileStatement*>(statement);
      // collect assignedVars from body
      for (const auto& statement : castedStatement->bodyStatements) {
        auto res = computeAssignedVars(statement.get(), pointerVars);
        assignedVars.insert(res.begin(), res.end());
      }
      break;
    }
    case program::Statement::Type::SkipStatement:
    case program::Statement::Type::Assumption:
    case program::Statement::Type::Assertion:      
    case program::Statement::Type::VarDecl: {
      break;
    }
  }
  return assignedVars;
}

bool AnalysisPreComputation::doNotOccurIn(
    std::unordered_set<std::shared_ptr<const program::Variable>>& vars,
    std::shared_ptr<const program::Expression> expr) {
    switch (expr->type()) {
    case program::Type::VariableAccess: {
      auto var =
          std::static_pointer_cast<const program::VariableAccess>(expr);
      return vars.find(var->var) == vars.end();
    }
    case program::Type::Addition: {
      auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
      return doNotOccurIn(vars, castedExpr->summand1) &&
             doNotOccurIn(vars, castedExpr->summand2);
    }
    case program::Type::Subtraction: {
      auto castedExpr =
          std::static_pointer_cast<const program::Subtraction>(expr);
      return doNotOccurIn(vars, castedExpr->child1) &&
             doNotOccurIn(vars, castedExpr->child2);
    }
    case program::Type::Modulo: {
      auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
      return doNotOccurIn(vars, castedExpr->child1) &&
             doNotOccurIn(vars, castedExpr->child2);
    }
    case program::Type::Multiplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::Multiplication>(expr);
      return doNotOccurIn(vars, castedExpr->factor1) &&
             doNotOccurIn(vars, castedExpr->factor2);
    }
    case program::Type::IntegerConstant: {
      return true;
    }
    case program::Type::IntArrayApplication: {
      auto var =
          std::static_pointer_cast<const program::IntArrayApplication>(expr);
      return vars.find(var->array) == vars.end();
    }
    default:
      // TODO update with pointer constructs
      // should never happen
      return false;
  }
}

void AnalysisPreComputation::computeVariablesContainedInLoopCondition(
    std::shared_ptr<const program::BoolExpression> expr,
    std::unordered_set<std::shared_ptr<const program::Variable>>& variables) {
  assert(expr != nullptr);
  switch (expr->type()) {
    case program::BoolExpression::Type::BooleanAnd: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanAnd>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;
    }
    case program::BoolExpression::Type::BooleanOr: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanOr>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;
    }
    case program::BoolExpression::Type::BooleanNot: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanNot>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child, variables);
      break;
    }
    case program::BoolExpression::Type::ArithmeticComparison: {
      auto castedExpr =
          std::static_pointer_cast<const program::ArithmeticComparison>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;
    }
    case program::BoolExpression::Type::Equality: {
      auto castedExpr =
          std::static_pointer_cast<const program::Equality>(expr);    
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;            
    }
    case program::BoolExpression::Type::BooleanConstant: {
      // do nothing
      break;
    }
  }
}

void AnalysisPreComputation::computeVariablesContainedInLoopCondition(
    std::shared_ptr<const program::Expression> expr,
    std::unordered_set<std::shared_ptr<const program::Variable>>& variables) {
  assert(expr != nullptr);
  switch (expr->type()) {
    case program::Type::Addition: {
      auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->summand1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->summand2, variables);
      break;
    }
    case program::Type::Subtraction: {
      auto castedExpr =
          std::static_pointer_cast<const program::Subtraction>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;
    }
    case program::Type::Multiplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::Multiplication>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->factor1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->factor2, variables);
      break;
    }
    case program::Type::Modulo: {
      auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
      computeVariablesContainedInLoopCondition(castedExpr->child1, variables);
      computeVariablesContainedInLoopCondition(castedExpr->child2, variables);
      break;
    }
    case program::Type::VariableAccess: {
      auto castedExpr =
          std::static_pointer_cast<const program::VariableAccess>(expr);
      variables.insert(castedExpr->var);
      break;
    }
    case program::Type::IntArrayApplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::IntArrayApplication>(expr);
      variables.insert(castedExpr->array);
      computeVariablesContainedInLoopCondition(castedExpr->index, variables);
      break;
    }
    case program::Type::IntegerConstant: {
      // do nothing
      break;
    }
    default: {
      // Currently, this function only has use in conjunction with the inliner
      // which is not sound in the presence of memory manipulating constructs
      assert(false);
    }
  }
}
}  // namespace analysis
