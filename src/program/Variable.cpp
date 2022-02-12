/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "Options.hpp"

namespace program {

//    // hack needed for bison: std::vector has no overload for ostream, but
//    these overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const program::Variable>>& e) {
  ostr << "not implemented";
  return ostr;
}

//    // hack needed for bison: std::list has no overload for ostream, but
//    these overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::list<std::shared_ptr<const program::Variable>>& e) {
  ostr << "not implemented";
  return ostr;
}

std::shared_ptr<const program::Variable> 
StructType::getField(std::string name) const {
  for(auto i = fields.begin(); i != fields.end(); ++i){
    if((*i)->name == name){
      return *i;
    } 
  }
  return std::shared_ptr<const program::Variable>();
}

int StructType::getFieldPos(std::string name) const {
  int count = 0;
  for(auto i = fields.begin(); i != fields.end(); ++i){
    if((*i)->name == name){
      return count;
    } 
    count++;
  }
  assert(false);
  //to make compiler happy
  return -1;
}


std::string StructType::toString() const {
  return name;
}

std::string StructFieldAccess::toString() const {
  std::string structStr = struc->toString();
  if(struc->exprType()->isPointerToStruct()){
    return structStr + "->" + field->name;
  }
  return structStr + "." + field->name;
}

std::string IntArrayApplication::toString() const {
  return array->name + "[" + index->toString() + "]";
}

std::string VariableAccess::toString() const { return var->name; }

std::string DerefExpression::toString() const {
  return "*" + expr->toString();
}

std::string VarReference::toString() const { return "&" + referent->name; }


}  // namespace program
