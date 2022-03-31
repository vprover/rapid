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

//Sticking it here as not sure where to put it
inline std::string toLower(std::string s){
  std::transform(s.begin(), s.begin() + 1, s.begin(), ::tolower);
  return s;
};

class Symbol {
  // we need each symbol to be either declared in the signature or to be a
  // variable (which will be declared by the quantifier) We use the
  // Signature-class below as a manager-class for symbols of the first kind

 public:
  enum class SymbolType {
    LemmaPredicate,
    DensityPredicate,
    ProgramVar,
    ConstProgramVar,
    FinalLoopCount,
    TimePoint,
    MallocFunc,
    Selector,
    Other
  };

 protected:
  friend class Signature;

  Symbol(std::string name, const Sort* rngSort, bool noDeclaration,
         SymbolType typ)
      : name(name),
        argSorts(),
        rngSort(rngSort),
        noDeclaration(noDeclaration),
        isColorSymbol(false),
        symbolType(typ) {
    assert(!name.empty());
    assert(typ != SymbolType::LemmaPredicate || isPredicateSymbol());
  }

  Symbol(std::string name, std::vector<const Sort*> argSorts,
         const Sort* rngSort, bool noDeclaration, SymbolType typ)
      : name(name),
        argSorts(std::move(argSorts)),
        rngSort(rngSort),
        isColorSymbol(false),
        noDeclaration(noDeclaration),
        symbolType(typ) {
    assert(!name.empty());
    assert(typ != SymbolType::LemmaPredicate || isPredicateSymbol());
  }

  Symbol(std::string name, std::string orientation, bool isColorSymbol)
      : name(name),
        argSorts(),
        rngSort(),
        noDeclaration(false),
        orientation(orientation),
        isColorSymbol(isColorSymbol),
        symbolType(SymbolType::Other) {
    assert(!name.empty());
    assert(!orientation.empty());
    assert(orientation == "left" || orientation == "right");
  }

  std::string replaceString(std::string, std::string, std::string) const;

 public:
  const std::string name;
  const std::vector<const Sort*> argSorts;
  const Sort* rngSort;

  const bool
      noDeclaration;  // true iff the symbol needs no declaration in smtlib
                      // (i.e. true only for interpreted symbols and variables)
  const SymbolType symbolType;  // true if represents variable

  // used for symbol elimination, values are either "left" or "right", can be
  // empty for non-color symbols
  const std::string orientation;
  const bool isColorSymbol;

  bool isPredicateSymbol() const { return rngSort == Sorts::boolSort(); }
  bool isMallocSymbol() const { return symbolType == SymbolType::MallocFunc; }
  bool isSelectorSymbol() const { return symbolType == SymbolType::Selector; }
  //bool isConstMemoryArray() const {
  //  return (symbolType == SymbolType::MemoryArray) && (argSorts.size() == 0);
  //}

  std::string toSMTLIB() const;
  std::string toTPTP() const;
  virtual std::string declareSymbolSMTLIB() const;
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
  typedef Symbol::SymbolType SyS;

  static bool isDeclared(std::string name);

  // construct new symbols
  static std::shared_ptr<const Symbol> add(
      std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort,
      bool noDeclaration = false,
      Symbol::SymbolType sym = Symbol::SymbolType::Other);
  static std::shared_ptr<const Symbol> fetch(std::string name);
  static std::shared_ptr<const Symbol> fetchOrAdd(
      std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort,
      bool noDeclaration = false, SyS sym = SyS::Other);
  static std::shared_ptr<const Symbol> fetchArraySelect();
  static std::shared_ptr<const Symbol> fetchArrayStore();

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
