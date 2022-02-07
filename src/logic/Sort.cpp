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

std::string declareSortSMTLIB(const Sort& s) {
  if (s.toSMTLIB() == "Int" || s.toSMTLIB() == "Bool" ||
      s.toSMTLIB() == "(Array Int Int)") {
    // SMTLIB already knows Int, Array and Bool.
    return "";
  } else if (s.toSMTLIB() == "Nat") {
    if (util::Configuration::instance().nativeNat()) {
      return "(declare-nat Nat zero s p Sub)\n";
    } else {
      return "(declare-datatypes ((Nat 0)) (( (zero) (s (p Nat)) )) )\n";
    }
  } else if (s.isAlgebraicSort()){    
    std::string res = "(declare-datatype " + s.toSMTLIB() + " ((" + s.constructor + " ";
    for(const auto& sel : s.selectors){
      //TODO hack below. Change code so that sort IS location
      res = res + "(" + sel.first + " Location)";
    }
    res = res + ")))\n";
    return res;
  } else {
    return "(declare-sort " + s.toSMTLIB() + " 0)\n";
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

Sort* Sorts::structSort(std::string name,
    std::vector<std::pair<std::string, std::string>> selectors) {
  
  std::string constructor = toLower(name) + "Con";

  auto it = _sorts.find(name);

  if (it == _sorts.end()) {
    //TODO change name of constructor to lower case
    auto ret = _sorts.insert(
        std::make_pair(name, std::unique_ptr<Sort>(new Sort(name, constructor, selectors))));
    return ret.first->second.get();
  } else {
    assert((*it).second->isAlgebraicSort());
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
