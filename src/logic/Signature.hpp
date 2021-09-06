#ifndef __Signature__
#define __Signature__

#include <cassert>
#include <cstddef>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Options.hpp"
#include "Sort.hpp"

#pragma mark - Symbol

namespace logic {

class Symbol {
  // we need each symbol to be either declared in the signature or to be a
  // variable (which will be declared by the quantifier) We use the
  // Signature-class below as a manager-class for symbols of the first kind
  friend class Signature;

 private:
  Symbol(std::string name, const Sort* rngSort, bool isLemmaPredicate,
         bool noDeclaration)
      : name(name),
        argSorts(),
        rngSort(rngSort),
        isLemmaPredicate(isLemmaPredicate),
        noDeclaration(noDeclaration),
        isColorSymbol(false) {
    assert(!name.empty());
    assert(!isLemmaPredicate || isPredicateSymbol());
  }

  Symbol(std::string name, std::vector<const Sort*> argSorts,
         const Sort* rngSort, bool isLemmaPredicate, bool noDeclaration)
      : name(name),
        argSorts(std::move(argSorts)),
        rngSort(rngSort),
        isLemmaPredicate(isLemmaPredicate),
        isColorSymbol(false),
        noDeclaration(noDeclaration) {
    assert(!name.empty());
    assert(!isLemmaPredicate || isPredicateSymbol());
  }

  Symbol(std::string name, std::string orientation, bool isColorSymbol)
      : name(name),
        argSorts(),
        rngSort(),
        isLemmaPredicate(false),
        noDeclaration(false),
        orientation(orientation),
        isColorSymbol(isColorSymbol) {
    assert(!name.empty());
    assert(!orientation.empty());
    assert(orientation == "left" || orientation == "right");
  }

 public:
  const std::string name;
  const std::vector<const Sort*> argSorts;
  const Sort* rngSort;
  const bool isLemmaPredicate;  // lemma predicates will be annotated in the
                                // smtlib-output, so that Vampire can treat them
                                // differently
  const bool
      noDeclaration;  // true iff the symbol needs no declaration in smtlib
                      // (i.e. true only for interpreted symbols and variables)

  // used for symbol elimination, values are either "left" or "right", can be
  // empty for non-color symbols
  const std::string orientation;
  const bool isColorSymbol;

  bool isPredicateSymbol() const { return rngSort == Sorts::boolSort(); }

  std::string toSMTLIB() const;
  std::string toTPTP() const;
  std::string declareSymbolSMTLIB() const;
  std::string declareSymbolTPTP() const;
  std::string declareSymbolColorSMTLIB() const;

  bool operator==(const Symbol& s) const { return name == s.name; }
  bool operator!=(const Symbol& s) const { return !(name == s.name); }
};

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const logic::Symbol>>& f);

}  // namespace logic

namespace std {
template <>
struct hash<logic::Symbol> {
  using argument_type = logic::Symbol;
  using result_type = std::size_t;

  result_type operator()(argument_type const& s) const {
    return std::hash<std::string>()(s.name);
  }
};

template <>
struct hash<const logic::Symbol> {
  using argument_type = logic::Symbol;
  using result_type = std::size_t;

  result_type operator()(argument_type const& s) const {
    return std::hash<std::string>()(s.name);
  }
};
}  // namespace std

#pragma mark - Signature

namespace logic {

// We use Signature as a manager-class for Symbol-instances
class Signature {
 public:
  static bool isDeclared(std::string name);

  // construct new symbols
  static std::shared_ptr<const Symbol> add(std::string name,
                                           std::vector<const Sort*> argSorts,
                                           const Sort* rngSort,
                                           bool noDeclaration = false);
  static std::shared_ptr<const Symbol> fetch(std::string name);
  static std::shared_ptr<const Symbol> fetchOrAdd(
      std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort,
      bool isLemmaPredicate = false, bool noDeclaration = false);

  // check that variable doesn't use name which already occurs in Signature
  // return Symbol without adding it to Signature
  static std::shared_ptr<const Symbol> varSymbol(std::string name,
                                                 const Sort* rngSort);

  // construct color symbol declarations for symbol elimination
  static void addColorSymbol(std::string name, std::string orientation);

  static const std::vector<std::shared_ptr<const Symbol>>&
  signatureOrderedByInsertion() {
    return _signatureOrderedByInsertion;
  }

 private:
  // _signature collects all symbols used so far.
  static std::unordered_map<std::string, std::shared_ptr<const Symbol>>
      _signature;
  // symbols of signature, in the order of insertion.
  static std::vector<std::shared_ptr<const Symbol>>
      _signatureOrderedByInsertion;
};
}  // namespace logic
#endif
