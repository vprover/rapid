#include "Sort.hpp"

#include <map>
#include <memory>
#include <string>
#include <utility>
#include <cassert>

#include "Options.hpp"

namespace logic {

#pragma mark - Sort

std::string Sort::toSMTLIB() const {
  if (name == "Int") {
    return "Int";
  } else if (name == "Bool") {
    return "Bool";
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
    return name;
  }
}

std::string declareSortSMTLIB(const Sort& s) {
  if (s.toSMTLIB() == "Int" || s.toSMTLIB() == "Bool") {
    // SMTLIB already knows Int and Bool.
    return "";
  } else if (s.toSMTLIB() == "Nat") {
    if (util::Configuration::instance().nativeNat()) {
      return "(declare-nat Nat zero s p Sub)\n";
    } else {
      return "(declare-datatypes ((Nat 0)) (( (zero) (s (p Nat)) )) )\n";
    }
  } else {
    return "(declare-sort " + s.toSMTLIB() + " 0)\n";
  }
}

std::string declareSortTPTP(const Sort& s) {
  if (s.toTPTP() == "int" || s.toTPTP() == "bool") {
    // TPTP already knows bool and int.
    return "";
  } else if (s.toTPTP() == "Nat") {
    assert(false);  // TPTP doesn't support term algebras
    return "";
  } else {
    return "tff(sort_" + s.toTPTP() + ", type, " + s.toTPTP() + " : $tType).\n";
  }
}

bool Sort::operator==(Sort& o) { return name == o.name; }

std::ostream& operator<<(std::ostream& ostr, const Sort& s) {
  ostr << s.name;
  return ostr;
}

#pragma mark - Sorts

std::map<std::string, std::unique_ptr<Sort>> Sorts::_sorts;

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
