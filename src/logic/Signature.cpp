#include "Signature.hpp"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Options.hpp"

namespace logic {

#pragma mark - Symbol

std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const logic::Symbol>>& f) {
  ostr << "not implemented";
  return ostr;
}

std::string Symbol::declareSymbolSMTLIB() const {
  if (!noDeclaration) {
    // hack since Vampire currently doesn't add the sub-predicate itself
    // declare and define the symbol time_sub

    if (!util::Configuration::instance().integerIterations() &&
        !util::Configuration::instance().nativeNat() && name == "Sub") {
      return "(declare-fun Sub (Nat Nat) Bool)\n";
    }

    if (isColorSymbol) {
      return "(color-symbol " + name + " :" + orientation + ")\n";
    }

    bool isLemmaPredicate = symbolType == SymbolType::LemmaPredicate;

    if (argSorts.size() == 0 &&
        !(isLemmaPredicate &&
          util::Configuration::instance().lemmaPredicates())) {
      if (symbolType == SymbolType::TimePoint) {
        return "(declare-time-point " + toSMTLIB() + " " + rngSort->toSMTLIB() +
               ")\n";
      }

      if (symbolType == SymbolType::FinalLoopCount) {
        return "(declare-final-loop-count " + toSMTLIB() + " " +
               rngSort->toSMTLIB() + ")\n";
      }

      if (symbolType == SymbolType::ConstProgramVar) {
        return "(declare-const-var " + toSMTLIB() + " " + rngSort->toSMTLIB() +
               ")\n";
      }

      return "(declare-const " + toSMTLIB() + " " + rngSort->toSMTLIB() + ")\n";
    } else {
      std::string res = (isLemmaPredicate &&
                         util::Configuration::instance().lemmaPredicates())
                            ? "(declare-lemma-predicate "
                            : "(declare-fun ";

      if (symbolType == SymbolType::TimePoint) {
        res = "(declare-time-point ";
      }

      if(symbolType == SymbolType::MallocFunc) {
        res = "(declare-malloc-func ";        
      }

      if (symbolType == SymbolType::FinalLoopCount) {
        res = "(declare-final-loop-count ";
      }

      if (symbolType == SymbolType::ProgramVar) {
        res = "(declare-program-var ";
      }

      res += toSMTLIB() + " (";
      for (int i = 0; i < argSorts.size(); ++i) {
        res += argSorts[i]->toSMTLIB() + (i + 1 == argSorts.size() ? "" : " ");
      }
      res += ") " + rngSort->toSMTLIB() + ")\n";
      return res;
    }
  } else {
    return "";
  }
}

std::string Symbol::declareSymbolTPTP() const {
  if (noDeclaration) {
    return "";  // don't need to declare symbols, which are already known to
                // TPTP-solvers.
                // TODO: vampire doesn't parse tptp for lemma-predicates, so
                // neglected for now
  }

  static bool hol = util::Configuration::instance().hol();
  std::string logic = hol ? "thf" : "tff";

  std::string outputName = toTPTP();
  std::string s =
      logic + "(symb_" + outputName + ", type, " + outputName + " : ";
  if (argSorts.size() == 0) {
    s += rngSort->toTPTP() + ").\n";
  } else if (argSorts.size() == 1) {
    s += argSorts[0]->toTPTP() + " > " + rngSort->toTPTP() + ").\n";
  } else {
    s += hol ? "" : "(";
    for (unsigned i = 0; i < argSorts.size() - 1; i++) {
      s += argSorts[i]->toTPTP() + (hol ? " > " : " * ");
    }
    s += argSorts[argSorts.size() - 1]->toTPTP() + (hol ? "" : ")") + " > " +
         rngSort->toTPTP() + ").\n";
  }
  return s;
}

std::string Symbol::toSMTLIB() const {
  // if non-negative integer constant
  if (std::all_of(name.begin(), name.end(), ::isdigit)) {
    return name;
  }
  // if negative integer constant
  else if (name[0] == '-' && name.size() > 1 &&
           std::all_of(name.begin() + 1, name.end(), ::isdigit)) {
    // need to encode negative integer as unary minus of positive integer
    return "(- " + name.substr(1, name.size() - 1) + ")";
  } else {
    return name;
  }
}

std::string Symbol::replaceString(std::string subject, std::string search,
                                  std::string replace) const {
  size_t pos = 0;
  while ((pos = subject.find(search, pos)) != std::string::npos) {
    subject.replace(pos, search.length(), replace);
    pos += replace.length();
  }
  return subject;
}

std::string Symbol::toTPTP() const {
  const std::string toFind = "main_end";
  // if non-negative integer constant
  if (symbolType == SymbolType::ProgramVar) {
    std::string nameTPTP = name;
    nameTPTP[0] = std::toupper(name[0]);
    return nameTPTP;
  } else if (std::all_of(name.begin(), name.end(), ::isdigit)) {
    return name;
  }
  // if negative integer constant
  else if (name[0] == '-' && name.size() > 1 &&
           std::all_of(name.begin() + 1, name.end(), ::isdigit)) {
    // need to encode negative integer as unary minus of positive integer
    return "($uminus " + name.substr(1, name.size() - 1) + ")";
  } else if (name == "+") {
    return "$sum";
  } else if (name == "-") {
    return "$difference";
  } else if (name.find("-") != std::string::npos) {
    std::string nameTPTP = name;
    nameTPTP = replaceString(nameTPTP, "-", "");
    nameTPTP[0] = std::tolower(name[0]);
    return nameTPTP;
  } else {
    return name;
  }
}

#pragma mark - Signature

std::unordered_map<std::string, std::shared_ptr<const Symbol>>
    Signature::_signature;
std::vector<std::shared_ptr<const Symbol>>
    Signature::_signatureOrderedByInsertion;

bool Signature::isDeclared(std::string name) {
  auto it = _signature.find(name);
  return (it != _signature.end());
}

std::shared_ptr<const Symbol> Signature::add(std::string name,
                                             std::vector<const Sort*> argSorts,
                                             const Sort* rngSort,
                                             bool noDeclaration, SyS typ) {
  // there must be no symbol with name name already added
  assert(_signature.count(name) == 0);

  auto pair = _signature.insert(
      std::make_pair(name, std::unique_ptr<Symbol>(new Symbol(
                               name, argSorts, rngSort, noDeclaration, typ))));
  assert(pair.second);  // must succeed since we checked that no such symbols
                        // existed before the insertion

  auto symbol = pair.first->second;
  _signatureOrderedByInsertion.push_back(symbol);
  return symbol;
}

std::shared_ptr<const Symbol> Signature::fetchArraySelect() {
  // TODO possibly clashing name here?
  return Signature::fetchOrAdd("select", {Sorts::arraySort(), Sorts::intSort()},
                               Sorts::intSort(), true);
}

std::shared_ptr<const Symbol> Signature::fetchArrayStore() {
  // TODO possibly clashing name here?
  return Signature::fetchOrAdd(
      "store", {Sorts::arraySort(), Sorts::intSort(), Sorts::intSort()},
      Sorts::arraySort(), true);
}

std::shared_ptr<const Symbol> Signature::fetch(std::string name) {
  auto it = _signature.find(name);
  assert(it != _signature.end());

  return it->second;
}

std::shared_ptr<const Symbol> Signature::fetchOrAdd(
    std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort,
    bool noDeclaration, SyS typ) {
  auto pair = _signature.insert(
      std::make_pair(name, std::shared_ptr<Symbol>(new Symbol(
                               name, argSorts, rngSort, noDeclaration, typ))));
  auto symbol = pair.first->second;

  if (pair.second) { 
    _signatureOrderedByInsertion.push_back(symbol);
  }
  // if a symbol with the name already exist, make sure it has the same sorts
  // and attributes
  else {
    if (argSorts.size() != symbol->argSorts.size()) {
      std::cout << "User error: symbol " << symbol->name << " requires "
                << symbol->argSorts.size() << " arguments, but "
                << argSorts.size() << " arguments where given" << std::endl;
      assert(false);
    }
    for (int i = 0; i < argSorts.size(); ++i) {
      assert(argSorts[i] == symbol->argSorts[i]);
    }
    assert(rngSort = symbol->rngSort);
    assert(noDeclaration == symbol->noDeclaration);
  }
  return symbol;
}

std::shared_ptr<const Symbol> Signature::varSymbol(std::string name,
                                                   const Sort* rngSort) {
  // there must be no symbol with name name already added
  assert(_signature.count(name) == 0);

  return std::shared_ptr<Symbol>(
      new Symbol(name, rngSort, true, SyS::Other));
}

void Signature::addColorSymbol(std::string name, std::string orientation) {
  // there must be no symbol with name name already added
  assert(orientation == "left" || orientation == "right");
  bool isColorSymbol = true;

  auto pair = _signature.insert(std::make_pair(
      name + "_color",
      std::unique_ptr<Symbol>(new Symbol(name, orientation, isColorSymbol))));
  assert(pair.second);  // must succeed since we checked that no such symbols
                        // existed before the insertion

  auto symbol = pair.first->second;
  _signatureOrderedByInsertion.push_back(symbol);
}

}  // namespace logic
