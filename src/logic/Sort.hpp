#ifndef __Sort__
#define __Sort__

#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <cassert>

#include "Options.hpp"

namespace logic {

#pragma mark - Sort

class Sort {
  // we need each sort to be unique.
  // We therefore use the Sorts-class below as a manager-class for Sort-objects
  friend class Sorts;

 private:
  // constructor is private to prevent accidental usage.
  Sort(std::string name) : name(name) {};

 public:
  const std::string name;

  bool operator==(Sort &o);

  std::string toSMTLIB() const;
  std::string toTPTP() const;
};
std::ostream &operator<<(std::ostream &ostr, const Sort &s);

std::string declareSortSMTLIB(const Sort &s);
std::string declareSortTPTP(const Sort &s);

#pragma mark - Sorts

// we need each sort to be unique.
// We therefore use Sorts as a manager-class for Sort-instances
class Sorts {
 public:
  // construct various sorts
  static Sort *boolSort() { return fetchOrDeclare("Bool"); }
  static Sort *intSort() { return fetchOrDeclare("Int"); }
  static Sort *natSort() { return fetchOrDeclare("Nat"); }
  static Sort *timeSort() { return fetchOrDeclare("Time"); }
  static Sort *traceSort() { return fetchOrDeclare("Trace"); }

  // Used additionally if array theory is enabled
  static Sort *intArraySort() { return fetchOrDeclare("(Array Int Int)"); }
  static Sort *boolArraySort() { return fetchOrDeclare("(Array Int Bool)"); }

  static const Sort *toActualSort(const Sort *sort, bool isArray) {
    if (!isArray || !util::Configuration::instance().nativeArrays()) {
      return sort;
    }
    if (sort == boolSort()) {
      return boolArraySort();
    }
    if (sort == intSort()) {
      return intArraySort();
    }
    assert(false);
    return nullptr;
  }

  // returns map containing all previously constructed sorts as pairs
  // (nameOfSort, Sort)
  static const std::map<std::string, std::unique_ptr<Sort>> &nameToSort() {
    return _sorts;
  };

 private:
  static Sort *fetchOrDeclare(std::string name);
  static std::map<std::string, std::unique_ptr<Sort>> _sorts;
};

}  // namespace logic

#endif
