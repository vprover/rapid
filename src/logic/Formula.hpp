#ifndef __Formula__
#define __Formula__

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "Term.hpp"

namespace logic {

# pragma mark - Formulas
    
    // We use Formulas as a manager-class for Formula-instances
    class Formulas
    {
    public:
        static std::shared_ptr<const Term> predicate(std::string name, std::vector<std::shared_ptr<const Term>> subterms, std::string label = "", bool noDeclaration=false);
        static std::shared_ptr<const Term> Formulas::predicate(std::shared_ptr<const Symbol> symbol, std::vector<std::shared_ptr<const Term>> subterms);
        static std::shared_ptr<const Term> lemmaPredicate(std::string name, std::vector<std::shared_ptr<const Term>> subterms, std::string label = "");

        static std::shared_ptr<const Term> equality(std::shared_ptr<const Term> left, std::shared_ptr<const Term> right, std::string label = "");
        static std::shared_ptr<const Term> disequality(std::shared_ptr<const Term> left, std::shared_ptr<const Term> right, std::string label = "");

        static std::shared_ptr<const Term> negation(std::shared_ptr<const Term> f, std::string label = "");

        static std::shared_ptr<const Term> conjunction(std::vector<std::shared_ptr<const Term>> conj, std::string label = "");
        static std::shared_ptr<const Term> disjunction(std::vector<std::shared_ptr<const Term>> disj, std::string label = "");

        static std::shared_ptr<const Term> implication(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "");
        static std::shared_ptr<const Term> equivalence(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "");

        static std::shared_ptr<const Term> existential(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "");
        static std::shared_ptr<const Term> universal(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "");

        static std::shared_ptr<const Term> trueFormula(std::string label = "");
        static std::shared_ptr<const Term> falseFormula(std::string label = "");

        // variants of the above methods which additionally attempt to apply simplifications before generating the formulas
        // the label 'label' will be set on the result of the simplifications
        static std::shared_ptr<const Term> equalitySimp(std::shared_ptr<const Term> left, std::shared_ptr<const Term> right, std::string label = "");
        static std::shared_ptr<const Term> disequalitySimp(std::shared_ptr<const Term> left, std::shared_ptr<const Term> right, std::string label = "");

        static std::shared_ptr<const Term> negationSimp(std::shared_ptr<const Term> f, std::string label = "");

        static std::shared_ptr<const Term> conjunctionSimp(std::vector<std::shared_ptr<const Term>> conj, std::string label = "");
        static std::shared_ptr<const Term> disjunctionSimp(std::vector<std::shared_ptr<const Term>> disj, std::string label = "");
        
        static std::shared_ptr<const Term> implicationSimp(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "");
        static std::shared_ptr<const Term> equivalenceSimp(std::shared_ptr<const Term> f1, std::shared_ptr<const Term> f2, std::string label = "");

        static std::shared_ptr<const Term> existentialSimp(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "");
        static std::shared_ptr<const Term> universalSimp(std::vector<std::shared_ptr<const Symbol>> vars, std::shared_ptr<const Term> f, std::string label = "");

    private:
        static std::shared_ptr<const Term> copyWithLabel(std::shared_ptr<const Term> f, std::string label);
    };
}

#pragma mark - Formulas

// We use Formulas as a manager-class for Formula-instances
class Formulas {
 public:
  static std::shared_ptr<const Formula> predicate(
      std::string name, std::vector<std::shared_ptr<const Term>> subterms,
      std::string label = "", bool noDeclaration = false);
  static std::shared_ptr<const Formula> lemmaPredicate(
      std::string name, std::vector<std::shared_ptr<const Term>> subterms,
      std::string label = "");

  static std::shared_ptr<const Formula> equality(
      std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
      std::string label = "");
  static std::shared_ptr<const Formula> disequality(
      std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
      std::string label = "");

  static std::shared_ptr<const Formula> negation(
      std::shared_ptr<const Formula> f, std::string label = "");

  static std::shared_ptr<const Formula> conjunction(
      std::vector<std::shared_ptr<const Formula>> conj, std::string label = "");
  static std::shared_ptr<const Formula> disjunction(
      std::vector<std::shared_ptr<const Formula>> disj, std::string label = "");

  static std::shared_ptr<const Formula> implication(
      std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
      std::string label = "");
  static std::shared_ptr<const Formula> equivalence(
      std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
      std::string label = "");

  static std::shared_ptr<const Formula> existential(
      std::vector<std::shared_ptr<const Symbol>> vars,
      std::shared_ptr<const Formula> f, std::string label = "");
  static std::shared_ptr<const Formula> universal(
      std::vector<std::shared_ptr<const Symbol>> vars,
      std::shared_ptr<const Formula> f, std::string label = "");

  static std::shared_ptr<const Formula> trueFormula(std::string label = "");
  static std::shared_ptr<const Formula> falseFormula(std::string label = "");

  // variants of the above methods which additionally attempt to apply
  // simplifications before generating the formulas the label 'label' will be
  // set on the result of the simplifications
  static std::shared_ptr<const Formula> equalitySimp(
      std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
      std::string label = "");
  static std::shared_ptr<const Formula> disequalitySimp(
      std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
      std::string label = "");

  static std::shared_ptr<const Formula> negationSimp(
      std::shared_ptr<const Formula> f, std::string label = "");

  static std::shared_ptr<const Formula> conjunctionSimp(
      std::vector<std::shared_ptr<const Formula>> conj, std::string label = "");
  static std::shared_ptr<const Formula> disjunctionSimp(
      std::vector<std::shared_ptr<const Formula>> disj, std::string label = "");

  static std::shared_ptr<const Formula> implicationSimp(
      std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
      std::string label = "");
  static std::shared_ptr<const Formula> equivalenceSimp(
      std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
      std::string label = "");

  static std::shared_ptr<const Formula> existentialSimp(
      std::vector<std::shared_ptr<const Symbol>> vars,
      std::shared_ptr<const Formula> f, std::string label = "");
  static std::shared_ptr<const Formula> universalSimp(
      std::vector<std::shared_ptr<const Symbol>> vars,
      std::shared_ptr<const Formula> f, std::string label = "");

 private:
  static std::shared_ptr<const Formula> copyWithLabel(
      std::shared_ptr<const Formula> f, std::string label);
};
}  // namespace logic

#endif
