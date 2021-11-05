#ifndef __Sort__
#define __Sort__

#include <iostream>
#include <map>
#include <memory>
#include <string>

namespace logic {

#pragma mark - Sort

class Sort {
  // we need each sort to be unique.
  // We therefore use the Sorts-class below as a manager-class for Sort-objects
  friend class Sorts;

 private:
  // constructor is private to prevent accidental usage.
  Sort(std::string name) : name(name){};

 public:
  const std::string name;

  bool operator==(Sort& o);

  std::string toSMTLIB() const;
};
std::ostream& operator<<(std::ostream& ostr, const Sort& s);

std::string declareSortSMTLIB(const Sort& s);

#pragma mark - Sorts

// we need each sort to be unique.
// We therefore use Sorts as a manager-class for Sort-instances
class Sorts {
 public:
  // construct various sorts
  static Sort* boolSort() { return fetchOrDeclare("Bool"); }
  static Sort* intSort() { return fetchOrDeclare("Int"); }
  static Sort* natSort() { return fetchOrDeclare("Nat"); }
  static Sort* locSort() {
    return fetchOrDeclare("Location");
  }  // memory locations
  static Sort* arraySort() { return fetchOrDeclare("Array"); }
  static Sort* timeSort() { return fetchOrDeclare("Time"); }
  static Sort* traceSort() { return fetchOrDeclare("Trace"); }

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
