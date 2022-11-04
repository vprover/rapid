#include "WhileParsingContext.hpp"

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace parser {
bool WhileParsingContext::pushQuantifiedVars(
    std::vector<std::shared_ptr<const logic::Symbol>> quantifiedVars) {
  // TODO: later check that those don't exist yet.
  // insert each var into into map
  for (const auto& quantifiedVar : quantifiedVars) {
    if (quantifiedVarsDeclarations.count(quantifiedVar->name) > 0) {
      return false;
    }
    quantifiedVarsDeclarations[quantifiedVar->name] = quantifiedVar;
  }
  // push new level onto stack
  std::vector<std::string> quantifiedVarNames;
  for (const auto& quantifiedVar : quantifiedVars) {
    quantifiedVarNames.push_back(quantifiedVar->name);
  }
  quantifiedVarsStack.push_back(quantifiedVarNames);

  return true;
}

void WhileParsingContext::popQuantifiedVars() {
  // remove each var of last level from map
  for (const auto& quantifiedVarName : quantifiedVarsStack.back()) {
    quantifiedVarsDeclarations.erase(quantifiedVarName);
  }
  // pop last level
  quantifiedVarsStack.pop_back();
}

bool WhileParsingContext::isDeclared(std::string name) {
  return logic::Signature::isDeclared(name) ||
         (quantifiedVarsDeclarations.count(name) > 0);
}

std::shared_ptr<const logic::Symbol> WhileParsingContext::fetch(
    std::string name) {
  if (quantifiedVarsDeclarations.count(name) > 0) {
    return quantifiedVarsDeclarations[name];
  }
  return logic::Signature::fetch(name);
}

void WhileParsingContext::pushProgramVars() { programVarsStack.push_back({}); }

void WhileParsingContext::popProgramVars() {
  // remove each var of last level from map
  for (const auto& programVarName : programVarsStack.back()) {
    programVarsDeclarations.erase(programVarName);
  }
  // pop last level
  programVarsStack.pop_back();
}

void WhileParsingContext::addProgramVar(
    std::shared_ptr<const program::Variable> programVar) {
 
  auto isValidVariableName = [&](std::string name){
    std::string error = "";

    if(!util::Configuration::instance().integerIterations()){
      if(name == "p" || name == "Sub" || name == "zero" || name == "s"){
        error =  name + " is and invalid variable name. When using natural number iterations, 'p','Sub','zero' and 's' are reserved";
      }
    }
    if(name == "if" || name == "while" || name == "then" || name == "Int" || name == "else"){
      error = name + " is an invalid variable name as it is a reserved keyword";
    }
    //TODO add other errors
    return error;
  };

  auto message = isValidVariableName(programVar->name);
  if(message != ""){
    throw std::invalid_argument( message );    
  }

  // TODO too restrictive? We can allow different variables
  // to have the same name so long as they are in difference scopes...
  if (programVarsDeclarations.count(programVar->name) > 0) {
    throw std::invalid_argument( "redeclaring variable " + programVar->name );
  }
  programVarsDeclarations[programVar->name] = programVar;
  programVarsStack.back().push_back(programVar->name);
}

bool WhileParsingContext::addTypeName(std::string name){
  if(std::find(declaredTypeNames.begin(), declaredTypeNames.end(),name) !=
     declaredTypeNames.end()){
    return false;
  }
  declaredTypeNames.push_back(name);
  return true;
}


bool WhileParsingContext::validTypeName(std::string name){
  if(std::find(declaredTypeNames.begin(), declaredTypeNames.end(),name) !=
     declaredTypeNames.end()){
    return true;
  }  
  return false;
}

void WhileParsingContext::addStructType(std::string name, 
  std::shared_ptr<const program::ExprType> st){
  structTypeDecls[name] = st;
}


std::shared_ptr<const program::ExprType> 
WhileParsingContext::getExprType(std::string name){
  assert(validTypeName(name));
  if(name == "Int"){
    return std::shared_ptr<const program::ExprType>(new program::ExprType(program::BasicType::INTEGER));
  } else if (name == "Nat"){
    return std::shared_ptr<const program::ExprType>(new program::ExprType(program::BasicType::NAT));
  }
  return structTypeDecls[name];
}

void WhileParsingContext::endParsingStruct(std::shared_ptr<const program::StructType> st) {
  parsingStrucName = "";

  for(auto& field : st->getFields()){
    assert(field->vt);
    // if we have a pointer to the very struct that is being parsed,
    // we are now in a position to set the child type
    if(field->vt->isPointerType() && field->vt->getChild() == nullptr){
      field->vt->setChild(st);
    }
  }
}


std::shared_ptr<const program::Variable> WhileParsingContext::getProgramVar(
    std::string name) {
  if (programVarsDeclarations.count(name) > 0) {
    return programVarsDeclarations[name];
  } else {
    std::cout << "program var " << name << " has not been declared!" << std::endl;
    assert(false);
    return nullptr;
  }
}

std::vector<std::shared_ptr<const program::Variable>>
WhileParsingContext::getActiveProgramVars() {
  // sort active vars so that nonArrayVars occur before arrayVars
  std::vector<std::shared_ptr<const program::Variable>> activeVars;
  std::vector<std::shared_ptr<const program::Variable>> activeArrayVars;
  for (const auto& pairNameVar : programVarsDeclarations) {
    auto var = pairNameVar.second;
    if (!var->isArray()) {
      activeVars.push_back(var);
    } else {
      activeArrayVars.push_back(var);
    }
  }
  activeVars.insert(activeVars.end(), activeArrayVars.begin(),
                    activeArrayVars.end());

  return activeVars;
}

#pragma mark enclosingLoops

void WhileParsingContext::addEnclosingLoops(const program::Function& function) {
  for (const auto& statement : function.statements) {
    addEnclosingLoopsForStatement(statement.get(), {});
  }
}

void WhileParsingContext::addEnclosingLoopsForStatement(
    const program::Statement* statement,
    std::vector<const program::WhileStatement*> enclosingLoops) {
  *statement->enclosingLoops = enclosingLoops;

  if (statement->type() == program::Statement::Type::IfElse) {
    auto castedStatement = static_cast<const program::IfElse*>(statement);
    for (const auto& statementInBranch : castedStatement->ifStatements) {
      addEnclosingLoopsForStatement(statementInBranch.get(), enclosingLoops);
    }
    for (const auto& statementInBranch : castedStatement->elseStatements) {
      addEnclosingLoopsForStatement(statementInBranch.get(), enclosingLoops);
    }
  } else if (statement->type() == program::Statement::Type::WhileStatement) {
    auto castedStatement =
        static_cast<const program::WhileStatement*>(statement);

    auto enclosingLoopsCopy = enclosingLoops;
    enclosingLoopsCopy.push_back(castedStatement);
    for (const auto& bodyStatement : castedStatement->bodyStatements) {
      addEnclosingLoopsForStatement(bodyStatement.get(), enclosingLoopsCopy);
    }
  }
}
}  // namespace parser
