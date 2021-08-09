#ifndef __Term__
#define __Term__

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "Signature.hpp"
#include "Sort.hpp"

namespace logic {

    class Term {
    public:

        Term(std::shared_ptr<const Symbol> symbol) : Term(std::move(symbol), "") {}
        Term(std::string label) : label(label), symbol(nullptr), hasSymbol(false) {}
        Term(std::shared_ptr<const Symbol> symbol, std::string label) : symbol(symbol), hasSymbol(true), label(label) {}

        virtual ~Term() {}

        const std::string label;
        const std::shared_ptr<const Symbol> symbol;
        const bool hasSymbol;

        enum class Type {
            Variable,
            FuncTerm,

            Predicate,
            Equality,
            Conjunction,
            Disjunction,
            Negation,
            Existential,
            Universal,
            Implication,
            Equivalence,
            True,
            False,
        };

        virtual Type type() const = 0;

        virtual std::string toSMTLIB(unsigned indentation = 0) const = 0;

        virtual std::string prettyString(unsigned indentation = 0) const = 0;

    protected:
        std::string stringForLabel(unsigned indentation) const;
    };

    bool operator==(const Term &t1, const Term &t2);

    bool operator!=(const Term &t1, const Term &t2);

    class LVariable : public Term {
        friend class Terms;

        LVariable(std::shared_ptr<const Symbol> symbol) : Term(symbol), id(freshId++) {}

    public:
        const unsigned id;

        Type type() const override { return Term::Type::Variable; }

        std::string toSMTLIB(unsigned indentation) const override;

        virtual std::string prettyString(unsigned indentation) const override;

        static unsigned freshId;
    };

    class FuncTerm : public Term {
        friend class Terms;

    protected:
        FuncTerm(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms, std::string label) : Term(std::move(symbol), label), subterms(std::move(subterms)) {
            assert(this->symbol->argSorts.size() == this->subterms.size());
            for (int i = 0; i < this->symbol->argSorts.size(); ++i) {
                assert(this->symbol->argSorts[i] == this->subterms[i]->symbol->rngSort);
            }
        }

        FuncTerm(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms) : FuncTerm(std::move(symbol), std::move(subterms), "") { }

    public:
        const std::vector<std::shared_ptr<const Term>> subterms;

        Type type() const override { return Term::Type::FuncTerm; }

        std::string toSMTLIB(unsigned indentation) const override;

        virtual std::string prettyString(unsigned indentation) const override;
    };

    class PredicateFormula : public FuncTerm {
        friend class Formulas;

    public:
        PredicateFormula(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms, std::string label = "") : FuncTerm(std::move(symbol), std::move(subterms), label) { }

        Type type() const override { return Term::Type::Predicate; }
    };

    class EqualityFormula : public Term {
        friend class Formulas;

    public:
        // TODO: refactor polarity into explicit negation everywhere
        EqualityFormula(bool polarity, std::shared_ptr<const Term> left, std::shared_ptr<const Term> right, std::string label = "")
                : Term(label), polarity(polarity), left(left), right(right) { }

        const bool polarity;
        const std::shared_ptr<const Term> left;
        const std::shared_ptr<const Term> right;

        Type type() const override { return Term::Type::Equality; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class ConjunctionFormula : public Term {
        friend class Formulas;

    public:
        ConjunctionFormula(std::vector<std::shared_ptr<const Term>> conj, std::string label = "") : Term(label), conj(conj) {}

        const std::vector<std::shared_ptr<const Term>> conj;

        Type type() const override { return Term::Type::Conjunction; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class DisjunctionFormula : public Term {
        friend class Formulas;

    public:
        DisjunctionFormula(std::vector<std::shared_ptr<const Term>> disj, std::string label = "") : Term(label), disj(disj) {}

        const std::vector<std::shared_ptr<const Term>> disj;

        Type type() const override { return Term::Type::Disjunction; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class NegationFormula : public Term {
        friend class Formulas;

    public:
        NegationFormula(std::shared_ptr<const Term> f, std::string label = "") : Term(label), f(f) {}

        const std::shared_ptr<const Term> f;

        Type type() const override { return Term::Type::Negation; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;

    };

    class ExistentialFormula : public Term {
        friend class Formulas;

    public:
        ExistentialFormula(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "")
                : Term(label), vars(std::move(vars)), f(f) {
            for (const auto &var : vars) {
                assert(var->argSorts.empty());
            }
        }

        const std::vector<std::shared_ptr<const Symbol>> vars;
        const std::shared_ptr<const Term> f;

        Type type() const override { return Term::Type::Existential; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class UniversalFormula : public Term {
        friend class Formulas;

    public:
        UniversalFormula(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "")
                : Term(label), vars(std::move(vars)), f(f) {
            for (const auto &var : vars) {
                assert(var->argSorts.empty());
            }
        }

        const std::vector<std::shared_ptr<const Symbol>> vars;
        const std::shared_ptr<const Term> f;

        Type type() const override { return Term::Type::Universal; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class ImplicationFormula : public Term {
        friend class Formulas;

    public:
        ImplicationFormula(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "")
                : Term(label), f1(f1), f2(f2) {}

        const std::shared_ptr<const Term> f1;
        const std::shared_ptr<const Term> f2;

        Type type() const override { return Term::Type::Implication; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class EquivalenceFormula : public Term {
        friend class Formulas;

    public:
        EquivalenceFormula(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "")
                : Term(label), f1(f1), f2(f2) {}

        const std::shared_ptr<const Term> f1;
        const std::shared_ptr<const Term> f2;

        Type type() const override { return Term::Type::Equivalence; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class TrueFormula : public Term {
        friend class Formulas;

    public:
        TrueFormula(std::string label = "") : Term(label) {}

        Type type() const override { return Term::Type::True; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    class FalseFormula : public Term {
        friend class Formulas;

    public:
        FalseFormula(std::string label = "") : Term(label) {}

        Type type() const override { return Term::Type::False; }

        std::string toSMTLIB(unsigned indentation = 0) const override;

        std::string prettyString(unsigned indentation = 0) const override;
    };

    inline std::ostream &operator<<(std::ostream &ostr, const Term &e) {
        ostr << e.toSMTLIB();
        return ostr;
    }

    // hack needed for bison: std::vector has no overload for ostream, but these overloads are needed for bison
    std::ostream &operator<<(std::ostream &ostr, const std::vector<std::shared_ptr<const logic::Term>> &t);

    std::ostream &operator<<(std::ostream &ostr, const std::vector<std::shared_ptr<const logic::LVariable>> &v);

}

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const logic::Term>>& t);
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const logic::LVariable>>& v);
}  // namespace logic

// custom hash for terms
namespace std {
    template<>
    struct hash<const logic::Term> {
        using argument_type = const logic::Term;
        using result_type = std::size_t;

        result_type operator()(argument_type const &t) const {
            // start from symbol of term
            size_t result = std::hash<const logic::Symbol>()(*t.symbol);
            // then integrate type into the hash
            result ^= std::hash<logic::Term::Type>()(t.type()) + 0x9e3779b9 + (result << 6) + (result >> 2);
            if (t.type() == logic::Term::Type::Variable) {
                // for an LVariable, finally integrate id into the hash
                auto castedTerm = dynamic_cast<const logic::LVariable &>(t);
                result ^= std::hash<unsigned>()(castedTerm.id) + 0x9e3779b9 + (result << 6) + (result >> 2);
            }
            else {
                // for a FuncTerm, integrate each subterm into the hash
                auto castedTerm = dynamic_cast<const logic::FuncTerm &>(t);
                for (const auto &subterm : castedTerm.subterms) {
                    result ^= std::hash<const logic::Term>()(*subterm) + 0x9e3779b9 + (result << 6) + (result >> 2);
                }
            }
            return result;
        }
    };
}

#pragma mark - Terms
namespace logic {
    // We use Terms as a manager-class for Term-instances
    class Terms {
    public:

        // construct new terms
        static std::shared_ptr<const LVariable> var(std::shared_ptr<const Symbol> symbol);

        static std::shared_ptr<const FuncTerm> func(std::string name, std::vector<std::shared_ptr<const Term>> subterms, const Sort *sort, bool noDeclaration = false);

        static std::shared_ptr<const FuncTerm> func(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms);
    };
}
#endif
