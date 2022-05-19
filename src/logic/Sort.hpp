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

 protected:
  // constructor is private to prevent accidental usage.
  Sort(std::string name) : name(name){};

 public:
  const std::string name;

  bool isNatSort() const { return name == "Nat"; }
  bool isIntSort() const { return name == "Int"; }
  bool isArraySort() const { return name == "Array"; }
  bool isBoolSort() const { return name == "Bool"; }

  virtual bool isStructSort() const { return false; }

  bool operator==(Sort& o);

  std::string toSMTLIB() const;
  std::string toTPTP() const;
};
std::ostream& operator<<(std::ostream& ostr, const Sort& s);


class StructSort : public Sort {
  friend class Sorts;  

private:
  StructSort(std::string name, std::vector<std::string> selectors) 
    : Sort(name), _selectors(selectors) {};

  // selector functions for this sort
  const std::vector<std::string> _selectors;
 
public:
  std::vector<std::string> recursiveSelectors();  
  std::vector<std::string> selectors() { return _selectors; }
  bool isStructSort() const { return true; }  

};

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
  static Sort* intSetSort() { return fetchOrDeclare("IntSet"); }
  static Sort* fetch(std::string name);
  static Sort* structSort(std::string name, 
    std::vector<std::string> selectors);
 
  // returns map containing all previously constructed sorts as pairs
  // (nameOfSort, Sort)
  static const std::map<std::string, std::unique_ptr<Sort>>& nameToSort() {
    return _sorts;
  };

  static const std::vector<Sort*>& structSorts() {
    return _structSorts;
  };

 private:
  static Sort* fetchOrDeclare(std::string name);
  static std::map<std::string, std::unique_ptr<Sort>> _sorts;
  static std::vector<Sort*> _structSorts;

};

}  // namespace logic

#endif
