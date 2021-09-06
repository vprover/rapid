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

    std::ostream& operator<<(std::ostream& ostr, const std::vector<std::shared_ptr<const logic::Symbol>>& f){ ostr << "not implemented"; return ostr; }
    
    std::string Symbol::declareSymbolSMTLIB() const {
        if (!noDeclaration) {
            // hack since Vampire currently doesn't add the sub-predicate itself
            // declare and define the symbol time_sub
            if (!util::Configuration::instance().nativeNat() && name == "Sub") {
                return "(declare-fun Sub (Nat Nat) Bool)\n";
            }
            if (argSorts.size() == 0 && !(isLemmaPredicate && util::Configuration::instance().lemmaPredicates())) {
                return "(declare-const " + toSMTLIB() + " " + rngSort->toSMTLIB() + ")\n";
            }
            else {
                std::string res = (isLemmaPredicate && util::Configuration::instance().lemmaPredicates()) ? "(declare-lemma-predicate " : "(declare-fun ";
                res += toSMTLIB() + " (";
                for (int i=0; i < argSorts.size(); ++i)
                {
                    res += argSorts[i]->toSMTLIB() + (i+1 == argSorts.size() ? "" : " ");
                }
                res += ") " + rngSort->toSMTLIB() + ")\n";
                return res;
            }
        }
        else {
            return "";
        }
    }
    
    std::string Symbol::toSMTLIB() const {
        // if non-negative integer constant
        if (std::all_of(name.begin(), name.end(), ::isdigit)) {
            return name;
        }
        // if negative integer constant
        else if (name[0]=='-' && name.size() > 1 && std::all_of(name.begin()+1, name.end(), ::isdigit)) {
            // need to encode negative integer as unary minus of positive integer
            return  "(- " + name.substr(1,name.size()-1) + ")";
        }
        else {
            return name;
        }
    }
  } else {
    return "";
  }
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

#pragma mark - Signature
    
    std::unordered_map<std::string, std::shared_ptr<const Symbol>> Signature::_signature;
    std::vector<std::shared_ptr<const Symbol>> Signature::_signatureOrderedByInsertion;

    bool Signature::isDeclared(std::string name) {
        auto it = _signature.find(name);
        return (it != _signature.end());
    }
    
    std::shared_ptr<const Symbol> Signature::add(std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort, bool noDeclaration) {
        // there must be no symbol with name name already added
        assert(_signature.count(name) == 0);
        
        auto pair = _signature.insert(std::make_pair(name,std::unique_ptr<Symbol>(new Symbol(name, argSorts, rngSort, false, noDeclaration))));
        assert(pair.second); // must succeed since we checked that no such symbols existed before the insertion

        auto symbol = pair.first->second;
        _signatureOrderedByInsertion.push_back(symbol);
        return symbol;
    }
    
    std::shared_ptr<const Symbol> Signature::fetch(std::string name) {
        auto it = _signature.find(name);
        assert(it != _signature.end());
        
        return it->second;
    }
    
    std::shared_ptr<const Symbol> Signature::fetchOrAdd(std::string name, std::vector<const Sort*> argSorts, const Sort* rngSort, bool isLemmaPredicate, bool noDeclaration) {
        auto pair = _signature.insert(std::make_pair(name, std::shared_ptr<Symbol>(new Symbol(name, argSorts, rngSort, isLemmaPredicate, noDeclaration))));
        auto symbol = pair.first->second;

        if (pair.second) {
            _signatureOrderedByInsertion.push_back(symbol);
        }
        // if a symbol with the name already exist, make sure it has the same sorts and attributes
        else {
            if (argSorts.size() != symbol->argSorts.size()) {
                std::cout << "User error: symbol " << symbol->name << " requires " << symbol->argSorts.size() << " arguments, but " << argSorts.size() << " arguments where given" << std::endl;
                assert(false);
            }
            for (int i=0; i < argSorts.size(); ++i) {
                if (argSorts[i] != symbol->argSorts[i]) {
                    _sleep(0);
                }
                assert(argSorts[i] == symbol->argSorts[i]);
            }
            assert(rngSort == symbol->rngSort);
            assert(isLemmaPredicate == symbol->isLemmaPredicate);
            assert(noDeclaration == symbol->noDeclaration);
        }
        return symbol;
    }
    
    std::shared_ptr<const Symbol> Signature::varSymbol(std::string name, const Sort* rngSort) {
        // there must be no symbol with name name already added
        assert(_signature.count(name) == 0);
        
        return std::shared_ptr<Symbol>(new Symbol(name, rngSort, false, true));
    }
    assert(rngSort = symbol->rngSort);
    assert(isLemmaPredicate == symbol->isLemmaPredicate);
    assert(noDeclaration == symbol->noDeclaration);
  }
  return symbol;
}

std::shared_ptr<const Symbol> Signature::varSymbol(std::string name,
                                                   const Sort* rngSort) {
  // there must be no symbol with name name already added
  assert(_signature.count(name) == 0);

  return std::shared_ptr<Symbol>(new Symbol(name, rngSort, false, true));
}

}  // namespace logic
