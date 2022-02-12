#ifndef __Sort__
#define __Sort__

#include <iostream>
#include <map>
#include <memory>
#include <string>

#include "../util/Options.hpp"

namespace logic {

#pragma mark - Sort

class Sort {
  // we need each sort to be unique.
  // We therefore use the Sorts-class below as a manager-class for Sort-objects
  friend class Sorts;

 private:
  // constructor is private to prevent accidental usage.
  Sort(std::string name) : name(name), constructor(""){};
  Sort(std::string name, std::string constructor, 
    std::vector<std::pair<std::string, std::string>> selectors) : 
    name(name), constructor(constructor), selectors(selectors){};

 public:
  const std::string name;
  const std::string constructor;
  const std::vector<std::pair<std::string, std::string>> selectors;

  bool isNatSort() const { return name == "Nat"; }
  bool isIntSort() const { return name == "Int"; }
  bool isArraySort() const { return name == "Array"; }
  bool isAlgebraicSort() const { return selectors.size(); }

  bool operator==(Sort& o);

  std::string toSMTLIB() const;
  std::string toTPTP() const;
};
std::ostream& operator<<(std::ostream& ostr, const Sort& s);

std::string declareSortSMTLIB(const Sort& s);
std::string declareSortTPTP(const Sort& s);

#pragma mark - Sorts

// we need each sort to be unique.
// We therefore use Sorts as a manager-class for Sort-instances
class Sorts {
 public:
  // construct various sorts
  static Sort* boolSort() { return fetchOrDeclare("Bool"); }
  static Sort* intSort() { return fetchOrDeclare("Int"); }
  static Sort* natSort() { return fetchOrDeclare("Nat"); }
  static Sort* iterSort() {
    if(util::Configuration::instance().integerIterations()){
      return intSort();
    }
    return natSort();
  }
  static Sort* arraySort() { return fetchOrDeclare("Arr"); }
  static Sort* timeSort() { return fetchOrDeclare("Time"); }
  static Sort* traceSort() { return fetchOrDeclare("Trace"); }
  static Sort* structSort(std::string name,
    std::vector<std::pair<std::string, std::string>> selectors);
  static Sort* fetch(std::string name);
 
  // returns map containing all previously constructed sorts as pairs
  // (nameOfSort, Sort)
  static const std::map<std::string, std::unique_ptr<Sort>>& nameToSort() {
    return _sorts;
  };

 private:
  static Sort* fetchOrDeclare(std::string name);
  static std::map<std::string, std::unique_ptr<Sort>> _sorts;
};

}  // namespace logic

#endif
