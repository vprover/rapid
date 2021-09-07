#include "SymbolDeclarations.hpp"

#include <Options.hpp>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

std::shared_ptr<const logic::Symbol> locationSymbol(std::string location,
                                                    unsigned numberOfLoops) {
  auto enclosingIteratorTypes = std::vector<const logic::Sort*>();
  for (int i = 0; i < numberOfLoops; ++i) {
    if (util::Configuration::instance().integerIterations()) {
      enclosingIteratorTypes.push_back(logic::Sorts::intSort());
    } else {
      enclosingIteratorTypes.push_back(logic::Sorts::natSort());
    }
  }
  return logic::Signature::fetchOrAdd(location, enclosingIteratorTypes,
                                      logic::Sorts::timeSort());
}

std::shared_ptr<const logic::Symbol> locationSymbolForStatement(
    program::Statement* statement) {
  if (typeid(*statement) == typeid(program::WhileStatement)) {
    return locationSymbol(statement->location,
                          statement->enclosingLoops->size() + 1);
  } else {
    return locationSymbol(statement->location,
                          statement->enclosingLoops->size());
  }
}

std::shared_ptr<const logic::Symbol> locationSymbolEndLocation(
    const program::Function* function) {
  return locationSymbol(function->name + "_end", 0);
}

std::shared_ptr<const logic::Symbol> lastIterationSymbol(
    program::WhileStatement* statement, unsigned numberOfTraces) {
  if (util::Configuration::instance().integerIterations()) {
    return intLastIterationSymbol(statement, numberOfTraces);
  }
  std::vector<const logic::Sort*> argumentSorts;
  for (unsigned i = 0; i < statement->enclosingLoops->size(); ++i) {
    argumentSorts.push_back(logic::Sorts::natSort());
  }
  if (numberOfTraces > 1) {
    argumentSorts.push_back(logic::Sorts::traceSort());
  }
  return logic::Signature::fetchOrAdd("n" + statement->location, argumentSorts,
                                      logic::Sorts::natSort());
}

std::shared_ptr<const logic::Symbol> iteratorSymbol(
    program::WhileStatement* whileStatement) {
  if (util::Configuration::instance().integerIterations()) {
    return intIteratorSymbol(whileStatement);
  }
  return logic::Signature::varSymbol("It" + whileStatement->location,
                                     logic::Sorts::natSort());
}

std::shared_ptr<const logic::Symbol> intLastIterationSymbol(
    program::WhileStatement* statement, unsigned numberOfTraces) {
  std::vector<const logic::Sort*> argumentSorts;
  for (unsigned i = 0; i < statement->enclosingLoops->size(); ++i) {
    argumentSorts.push_back(logic::Sorts::intSort());
  }
  if (numberOfTraces > 1) {
    argumentSorts.push_back(logic::Sorts::traceSort());
  }
  return logic::Signature::fetchOrAdd("n" + statement->location, argumentSorts,
                                      logic::Sorts::intSort());
}

std::shared_ptr<const logic::Symbol> intIteratorSymbol(
    program::WhileStatement* whileStatement) {
  return logic::Signature::varSymbol("It" + whileStatement->location,
                                     logic::Sorts::intSort());
}

std::shared_ptr<const logic::Symbol> posVarSymbol() {
  return logic::Signature::varSymbol("pos", logic::Sorts::intSort());
}

std::shared_ptr<const logic::Symbol> traceSymbol(unsigned traceNumber) {
  std::string traceName = "t" + std::to_string(traceNumber);
  return logic::Signature::fetchOrAdd(traceName, {}, logic::Sorts::traceSort());
}

std::shared_ptr<const logic::Symbol> declareInitTargetSymbol(
    const program::Variable* var) {
  // declare target symbol var_final and var_init for invariant generation
  assert(!var->isConstant);
  std::vector<const logic::Sort*> argSorts;
  if (var->isArray) {
    argSorts.push_back(logic::Sorts::intSort());
  }
  if (var->numberOfTraces > 1) {
    // TODO: this probably needs more proper handling
    argSorts.push_back(logic::Sorts::traceSort());
  }

  return logic::Signature::add(var->name + "_init", argSorts,
                               logic::Sorts::intSort());
}

std::shared_ptr<const logic::Symbol> declareFinalTargetSymbol(
    const program::Variable* var) {
  // declare target symbol var_final and var_init for invariant generation
  assert(!var->isConstant);
  std::vector<const logic::Sort*> argSorts;
  if (var->isArray) {
    argSorts.push_back(logic::Sorts::intSort());
  }
  if (var->numberOfTraces > 1) {
    // TODO: this probably needs more proper handling
    argSorts.push_back(logic::Sorts::traceSort());
  }

  return logic::Signature::add(var->name + "_final", argSorts,
                               logic::Sorts::intSort());
}

void declareColorSymbolLeft(const program::Variable* var) {
  // declare color symbol left for symbol elimination
  assert(!var->isConstant);
  auto orientation = "left";
  logic::Signature::addColorSymbol(var->name, orientation);
}

void declareSymbolForProgramVar(program::Variable* var) {
  std::vector<const logic::Sort*> argSorts;
  if (!var->isConstant) {
    argSorts.push_back(logic::Sorts::timeSort());
  }
  if (var->isArray) {
    argSorts.push_back(logic::Sorts::intSort());
  }
  if (var->numberOfTraces > 1) {
    argSorts.push_back(logic::Sorts::traceSort());
  }

  if (var->type() == program::ValueType::Bool) {
    logic::Signature::add(var->name, argSorts, logic::Sorts::boolSort());
  } else {
    logic::Signature::add(var->name, argSorts, logic::Sorts::intSort());
  }
}

void declareSymbolsForTraces(unsigned numberOfTraces) {
  // declare trace symbols
  // note: we number traces starting from 1
  for (unsigned i = 1; i < numberOfTraces + 1; i++) {
    traceSymbol(i);
  }
}

// symbols get declared by constructing them once
void declareSymbolsForFunction(const program::Function* function,
                               unsigned numberOfTraces) {
  // recurse on statements
  for (const auto& statement : function->statements) {
    declareSymbolsForStatements(statement.get(), numberOfTraces);
  }

  // declare end-location of function
  locationSymbolEndLocation(function);
}

void declareSymbolsForStatements(program::Statement* statement,
                                 unsigned numberOfTraces) {
  // declare main location symbol
  locationSymbolForStatement(statement);

  if (typeid(*statement) == typeid(program::IfElseStatement)) {
    auto castedStatement = static_cast<program::IfElseStatement*>(statement);

    // recurse
    for (const auto& statementInBranch : castedStatement->ifStatements) {
      declareSymbolsForStatements(statementInBranch.get(), numberOfTraces);
    }
    for (const auto& statementInBranch : castedStatement->elseStatements) {
      declareSymbolsForStatements(statementInBranch.get(), numberOfTraces);
    }
  } else if (typeid(*statement) == typeid(program::WhileStatement)) {
    auto castedStatement = static_cast<program::WhileStatement*>(statement);

    // declare last iteration-symbol
    lastIterationSymbol(castedStatement, numberOfTraces);

    // recurse
    for (const auto& bodyStatement : castedStatement->bodyStatements) {
      declareSymbolsForStatements(bodyStatement.get(), numberOfTraces);
    }
  }
}
