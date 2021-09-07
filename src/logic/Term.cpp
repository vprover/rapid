#include "Term.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace logic {

    // hack needed for bison: std::vector has no overload for ostream, but these overloads are needed for bison
    std::ostream& operator<<(std::ostream& ostr, const std::vector<std::shared_ptr<const logic::Term>>& t){ostr << "not implemented"; return ostr;}
    std::ostream& operator<<(std::ostream& ostr, const std::vector<std::shared_ptr<const logic::LVariable>>& v){ostr << "not implemented"; return ostr;}

    unsigned LVariable::freshId = 0;

    bool operator==(const Term& t1, const Term& t2)
    {
        if (t1.type() != t2.type())
        {
            return false;
        }
        if (t1.type() == Term::Type::Variable)
        {
            return *t1.symbol == *t2.symbol;
        }
        else
        {
            assert(t1.type() == Term::Type::FuncTerm);
            auto f1 = static_cast<const FuncTerm&>(t1);
            auto f2 = static_cast<const FuncTerm&>(t2);
            if (*f1.symbol != *f2.symbol || f1.subterms.size() != f2.subterms.size())
            {
                return false;
            }
            for (unsigned i = 0; i < f1.subterms.size(); i++)
            {
                if (*f1.subterms[i] != *f2.subterms[i])
                {
                    return false;
                }
            }
            return true;
        }
    }
    bool operator!=(const Term& t1, const Term& t2)
    {
        return !(t1 == t2);
    }

    std::string LVariable::toSMTLIB() const
    {
        return symbol->name;
    }

     std::string LVariable::toTPTP() const
    {
        return symbol->toTPTP();
    }
    
    std::string LVariable::prettyString() const
    {
        return symbol->name;
    }

    std::string FuncTerm::toSMTLIB() const
    {
        if (subterms.size() == 0)
        {
            return symbol->toSMTLIB();
        }
        else
        {
            std::string str = "(" + symbol->toSMTLIB() + " ";
            for (unsigned i = 0; i < subterms.size(); i++)
            {
                str += subterms[i]->toSMTLIB();
                str += (i == subterms.size() - 1) ? ")" : " ";
            }
            return str;
        }
    }

    std::string FuncTerm::toTPTP() const
    {

        if (subterms.size() == 0) {
            return symbol->toTPTP();
        } else {

            std::string str;
            
            if(util::Configuration::instance().hol()){
                str = "(" + symbol->toTPTP() + " @ ";
                for (unsigned i = 0; i < subterms.size(); i++) {
                    str += subterms[i]->toTPTP();
                    str += (i == subterms.size() - 1) ? ")" : " @ ";
                }
            } else {
                str = symbol->toTPTP() + "(";
                for (unsigned i = 0; i < subterms.size(); i++) {
                    str += subterms[i]->toTPTP();
                    str += (i == subterms.size() - 1) ? ")" : ",";
                }
            }

            // replace trace logic function terms with target symbols for postcondition
            /*if (str.find("main_end") != std::string::npos)
            {
                std::string toReplace("(main_end");
                std::string replacement("_final(");
                size_t pos = str.find(toReplace);
                str = str.replace(pos, toReplace.length(), replacement);

                // remove () for constants
                std::string toReplace2("()");
                std::string replacement2("");
                size_t pos2 = str.find(toReplace2);
                if (pos2 != std::string::npos)
                    str = str.replace(pos2, toReplace2.length(), replacement2);

                // replace (, for function terms with (
                std::string toReplace3("(,");
                std::string replacement3("(");
                size_t pos3 = str.find(toReplace3);
                if (pos3 != std::string::npos)
                    str = str.replace(pos3, toReplace3.length(), replacement3);
            }*/
            return str;
        }
    }
    
    std::string FuncTerm::prettyString() const
    {
        if (subterms.size() == 0)
        {
            return symbol->toSMTLIB();
        }
        else
        {
            std::string str = symbol->toSMTLIB() + "(";
            for (unsigned i = 0; i < subterms.size(); i++) {
                str += subterms[i]->toSMTLIB();
                str += (i == subterms.size() - 1) ? ")" : ",";
            }
            return str;
        }
    }


# pragma mark - Terms
    
    std::shared_ptr<const LVariable> Terms::var(std::shared_ptr<const Symbol> symbol)
    {
        return std::shared_ptr<const LVariable>(new LVariable(symbol));
    }
    
    std::shared_ptr<const FuncTerm> Terms::func(std::string name, std::vector<std::shared_ptr<const Term>> subterms, const Sort* sort, bool noDeclaration, Symbol::SymbolType typ)
    {
        std::vector<const Sort*> subtermSorts;
        for (const auto& subterm : subterms)
        {
            subtermSorts.push_back(subterm->symbol->rngSort);
        }
        auto symbol = Signature::fetchOrAdd(name, subtermSorts, sort, false, noDeclaration, typ);
        return std::shared_ptr<const FuncTerm>(new FuncTerm(symbol, subterms));
    }
    
    std::shared_ptr<const FuncTerm> Terms::func(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms)
    {
        return std::shared_ptr<const FuncTerm>(new FuncTerm(symbol, subterms));
    }
}

