#include "Sort.hpp"

#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <utility>

#include "Options.hpp"
#include "Signature.hpp"

namespace logic {

#pragma mark - Sort

std::string Sort::toSMTLIB() const {
  if (name == "Int") {
    return "Int";
  } else if (name == "Bool") {
    return "Bool";
  } else if (name == "Arr") {
    // only integer indexed integer arrays at the moment
    return "(Array Int Int)";
  } else {
    return name;
  }
}

std::string Sort::toTPTP() const {
  if (name == "Int") {
    return "$int";
  } else if (name == "Bool") {
    return "$o";
  } else {
    std::string nameTPTP = name;
    nameTPTP[0] = std::tolower(nameTPTP[0]);
    return nameTPTP;
  }
}

std::vector<std::string> StructSort::recursiveSelectors()
{
  std::vector<std::string> recSels;
  for(auto& sel : _selectors){
    auto sym = Signature::fetch(sel);
    auto returnTypeName = sym->rngSort->name;
    if(returnTypeName == name){
      recSels.push_back(sel);
    }
  } 
  return recSels;
}  

std::string declareSortSMTLIB(const Sort* s) {
  if (s->toSMTLIB() == "Int" || s->toSMTLIB() == "Bool" ||
      s->toSMTLIB() == "(Array Int Int)" || s->toSMTLIB() == "Time") {
    // SMTLIB already knows Int, Array and Bool.
    // Non-standard extension to Vampire recognises time sorts
    // TODO add option to output valid SMTLIB benchmark if required
    return "";
  } else if (s->toSMTLIB() == "Nat") {
    if (util::Configuration::instance().nativeNat()) {
      return "(declare-nat Nat zero s p Sub)\n";
    } else {
      return "(declare-datatypes ((Nat 0)) (( (zero) (s (p Nat)) )) )\n";
    }
  } else if (s->isStructSort() && util::Configuration::instance().nativeStructs()){
    std::string name = s->name;
    std::string lowerName = logic::toLower(name);
    std::string res = "(declare-struct " + name + " " + lowerName + "_null_loc (";

    auto structSort = static_cast<const logic::StructSort*>(s);
    for(auto& sel : structSort->selectors()){
      auto sym = logic::Signature::fetch(sel);
      const Sort* range = sym->rngSort;
      res += "(" + sel + " " + range->name;      
      if(range == s){
        std::string chain = sel + "_chain";
        std::string support = "in_support_" + sel + "_chain";
        res += " " + chain + " " + support;
      } 
      res += ")";
    } 

    res += "))";
    return res;
  } else {
    return "(declare-sort " + s->toSMTLIB() + " 0)\n";
  }
}

std::string declareSortTPTP(const Sort& s) {
  std::string logic = "tff";
  if (util::Configuration::instance().hol()) {
    logic = "thf";
  }

  if (s.toTPTP() == "$int" || s.toTPTP() == "$o") {
    // TPTP already knows bool and int.
    return "";
  } else if (s.toTPTP() == "Nat") {
    // assert(false); // TPTP doesn't support term algebras
    return "";
  } else {
    return logic + "(sort_" + s.toTPTP() + ", type, (" + s.toTPTP() +
           " : $tType)).\n";
  }
}

bool Sort::operator==(Sort& o) { return name == o.name; }

std::ostream& operator<<(std::ostream& ostr, const Sort& s) {
  ostr << s.name;
  return ostr;
}

#pragma mark - Sorts

std::map<std::string, std::unique_ptr<Sort>> Sorts::_sorts;
std::vector<Sort*> Sorts::_structSorts;

Sort* Sorts::structSort(std::string name, 
    std::vector<std::string> selectors){

  auto it = _sorts.find(name);

  if (it == _sorts.end()) {
    //TODO change name of constructor to lower case
    auto ret = _sorts.insert(
        std::make_pair(name, std::unique_ptr<Sort>(new StructSort(name, selectors))));
    auto sort = ret.first->second.get();
    _structSorts.push_back(sort);
    return sort;
  } else {
    assert((*it).second->isStructSort());
    return (*it).second.get();
  }
}

Sort* Sorts::fetch(std::string name){
  auto it = _sorts.find(name);
  assert(it != _sorts.end());
  return (*it).second.get();
}

Sort* Sorts::fetchOrDeclare(std::string name) {
  auto it = _sorts.find(name);

  if (it == _sorts.end()) {
    auto ret = _sorts.insert(
        std::make_pair(name, std::unique_ptr<Sort>(new Sort(name))));
    return ret.first->second.get();
  } else {
    return (*it).second.get();
  }
}

}  // namespace logic
