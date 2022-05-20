#include "Formula.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace logic {

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const logic::Formula>>& f) {
  ostr << "not implemented";
  return ostr;
}

std::string Formula::stringForLabel(unsigned indentation) const {
  std::string str = "";
  if (!label.empty()) {
    str += std::string(indentation, ' ') + ";" + label + "\n";
  }
  return str;
}

std::string Formula::stringForLabelTPTP(unsigned indentation) const {
  std::string str = "";
  if (!label.empty()) {
    str += std::string(indentation, ' ') + "%" + label + "\n";
  }
  return str;
}

#pragma - Methods to generate SMTLIB output

std::string PredicateFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  str += std::string(indentation, ' ');
  if (subterms.size() == 0) {
    str += symbol->toSMTLIB();
  } else {
    str += "(" + symbol->toSMTLIB() + " ";
    for (unsigned i = 0; i < subterms.size(); i++) {
      str += subterms[i]->toSMTLIB();
      str += (i == subterms.size() - 1) ? ")" : " ";
    }
  }
  return str;
}

std::string EqualityFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  str += std::string(indentation, ' ');
  if (polarity) {
    str += "(= " + left->toSMTLIB() + " " + right->toSMTLIB() + ")";
  } else {
    str += "(not (= " + left->toSMTLIB() + " " + right->toSMTLIB() + "))";
  }
  return str;
}

std::string ConjunctionFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  if (conj.size() == 0) {
    return str + std::string(indentation, ' ') + "true";
  }
  str += std::string(indentation, ' ') + "(and\n";
  for (unsigned i = 0; i < conj.size(); i++) {
    str += conj[i]->toSMTLIB(indentation + 3) + "\n";
  }
  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string DisjunctionFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  if (disj.size() == 0) {
    return str + std::string(indentation, ' ') + "false";
  }
  str = std::string(indentation, ' ') + "(or\n";
  for (unsigned i = 0; i < disj.size(); i++) {
    str += disj[i]->toSMTLIB(indentation + 3) + "\n";
  }
  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string NegationFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  str += std::string(indentation, ' ') + "(not\n";
  str += f->toSMTLIB(indentation + 3) + "\n";
  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string ExistentialFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  str += std::string(indentation, ' ') + "(exists ";

  // list of quantified variables
  str += "(";
  for (const auto& var : vars) {
    str += "(" + var->name + " " + var->rngSort->toSMTLIB() + ")";
  }
  str += ")\n";

  // formula
  str += f->toSMTLIB(indentation + 3) + "\n";

  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string UniversalFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  str += std::string(indentation, ' ') + "(forall ";

  // list of quantified variables
  str += "(";
  for (const auto& var : vars) {
    str += "(" + var->name + " " + var->rngSort->toSMTLIB() + ")";
  }
  str += ")\n";

  // formula
  str += f->toSMTLIB(indentation + 3) + "\n";

  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string ImplicationFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);

  str += std::string(indentation, ' ') + "(=>\n";
  str += f1->toSMTLIB(indentation + 3) + "\n";
  str += f2->toSMTLIB(indentation + 3) + "\n";
  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string EquivalenceFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);

  str += std::string(indentation, ' ') + "(=\n";
  str += f1->toSMTLIB(indentation + 3) + "\n";
  str += f2->toSMTLIB(indentation + 3) + "\n";
  str += std::string(indentation, ' ') + ")";
  return str;
}

std::string TrueFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  return str + std::string(indentation, ' ') + "true";
}

std::string FalseFormula::toSMTLIB(unsigned indentation) const {
  std::string str = stringForLabel(indentation);
  return str + std::string(indentation, ' ') + "false";
}

#pragma - Methods to generate TPTP output
std::string PredicateFormula::toTPTP(unsigned indentation) const {
  std::string sym = "";

  if (symbol.get()->name == "*") {
    sym = "$product";
  } else if (symbol.get()->name == "/") {
    sym = "$quotient_e";
  } else if (symbol.get()->name == "-") {
    sym = "$uminus";
  } else if (symbol.get()->name == ">") {
    sym = "$greater";
  } else if (symbol.get()->name == ">=") {
    sym = "$greatereq";
  } else if (symbol.get()->name == "<") {
    sym = "$less";
  } else if (symbol.get()->name == "<=") {
    sym = "$lesseq";
  } else if (symbol.get()->name == "true") {
    sym = "$true";
  } else if (symbol.get()->name == "false") {
    sym = "$false";
  }
  if (symbol.get()->name == "!") {
    sym = "~";
  }

  std::string str;
  if (subterms.size() == 0) {
    str += symbol->toTPTP();
  } else {
    std::string separator;
    if (util::Configuration::instance().hol()) {
      separator = " @ ";
    } else {
      separator = ", ";
    }

    if (!sym.empty()) {
      if (util::Configuration::instance().hol()) {
        str = "(" + sym + " @ ";
      } else {
        str = sym + "(";
      }
    } else {
      if (util::Configuration::instance().hol()) {
        str = "(" + symbol->toTPTP() + " @ ";
      } else {
        str = symbol->toTPTP() + "(";
      }
    }
    for (unsigned i = 0; i < subterms.size(); i++) {
      str += subterms[i]->toTPTP();
      str += (i == subterms.size() - 1) ? ") " : separator;
    }
  }

  return str;
}

std::string EqualityFormula::toTPTP(unsigned indentation) const {
  std::string str = "";  // stringForLabelTPTP(indentation);
  // str += std::string(indentation, ' ');
  if (polarity) {
    str += " (" + left->toTPTP() + " = " + right->toTPTP() + ") ";
  } else {
    str += " (" + left->toTPTP() + " != " + right->toTPTP() + ") ";
  }
  return str;
}

std::string ConjunctionFormula::toTPTP(unsigned indentation) const {
  std::string str = "";  // stringForLabelTPTP(indentation);
  std::string indent = std::string(indentation, ' ');
  if (conj.size() == 0) return "$true";
  if (conj.size() == 1) return conj[0]->toTPTP();

  for (unsigned i = 0; i < conj.size(); i++) {
    str += "" + conj[i]->toTPTP(indentation) + "";
    str += (i == conj.size() - 1) ? "" : " & \n" + indent;
  }
  return str;
}

std::string DisjunctionFormula::toTPTP(unsigned indentation) const {
  std::string str = "";  // stringForLabelTPTP(indentation);
  if (disj.size() == 0) return "$false";
  if (disj.size() == 1) return disj[0]->toTPTP();
  for (unsigned i = 0; i < disj.size(); i++) {
    str += "(" + disj[i]->toTPTP(indentation) + ")";

    str += (i == disj.size() - 1) ? "" : " | ";
  }
  return str;
}

std::string NegationFormula::toTPTP(unsigned indentation) const {
  return "~(" + f->toTPTP() + ")";
}

std::string ExistentialFormula::toTPTP(unsigned indentation) const {
  std::string indent = std::string(indentation, ' ');
  std::string str = "? [";
  for (unsigned i = 0; i < vars.size(); i++) {
    str += vars[i]->toTPTP() + " : " + vars[i]->rngSort->toTPTP();
    if (i != vars.size() - 1) {
      str += ", ";
    }
  }
  str += "] : (" + indent + f->toTPTP(indentation + 3) + ")";
  return str;
}

std::string UniversalFormula::toTPTP(unsigned indentation) const {
  std::string indent = std::string(indentation, ' ');
  std::string str = "! [";
  for (unsigned i = 0; i < vars.size(); i++) {
    str += vars[i]->toTPTP() + " : " + vars[i]->rngSort->toTPTP();
    if (i != vars.size() - 1) {
      str += ", ";
    }
  }
  str += "] : \n" + indent + "(" + f->toTPTP(indentation + 3) + ")";
  return str;
}

std::string ImplicationFormula::toTPTP(unsigned indentation) const {
  std::string str = std::string(indentation, ' ');
  return "(" + f1->toTPTP(indentation) + ")\n" + str + "=> (" +
         f2->toTPTP(indentation + 3) + ")";
}

std::string EquivalenceFormula::toTPTP(unsigned indentation) const {
  std::string str = "";  // stringForLabelTPTP(indentation);
  str +=
      "(" + f1->toTPTP(indentation) + ") = (" + f2->toTPTP(indentation) + ")";
  return str;
}

std::string TrueFormula::toTPTP(unsigned indentation) const {
  std::string str = stringForLabelTPTP(indentation);
  return str + "$true";
}

std::string FalseFormula::toTPTP(unsigned indentation) const {
  std::string str = stringForLabelTPTP(indentation);
  return str + "$false";
}

#pragma - Methods for printing formulas

std::string PredicateFormula::prettyString(unsigned indentation) const {
  auto str = std::string(indentation, ' ');

  if(symbol->integerCompSym()){
    assert(subterms.size() == 2);
    str += subterms[0]->toSMTLIB() + " "  + symbol->toSMTLIB() + " " + 
        subterms[1]->toSMTLIB();
    return str;
  }

  if (subterms.size() == 0) {
    str += symbol->toSMTLIB();
  } else {
    str += symbol->toSMTLIB() + "(";
    for (unsigned i = 0; i < subterms.size(); i++) {
      str += subterms[i]->toSMTLIB();
      str += (i == subterms.size() - 1) ? ")" : ",";
    }
  }
  return str;
}

std::string EqualityFormula::prettyString(unsigned indentation) const {
  if (polarity)
    return std::string(indentation, ' ') + left->prettyString() + " = " +
           right->prettyString();
  else
    return std::string(indentation, ' ') + left->prettyString() +
           " != " + right->prettyString();
}

std::string ConjunctionFormula::prettyString(unsigned indentation) const {
  if (conj.size() == 0) return std::string(indentation, ' ') + "True";

  std::string str = std::string(indentation, ' ') + "AND\n";

  for (unsigned i = 0; i < conj.size(); i++) {
    str += conj[i]->prettyString(indentation + 3);
    str += (i + 1 < conj.size()) ? "\n" : "";
  }

  return str;
}

std::string DisjunctionFormula::prettyString(unsigned indentation) const {
  if (disj.size() == 0) return std::string(indentation, ' ') + "False";

  std::string str = std::string(indentation, ' ') + "OR\n";

  for (unsigned i = 0; i < disj.size(); i++) {
    str += disj[i]->prettyString(indentation + 3);
    str += (i + 1 < disj.size()) ? "\n" : "";
  }

  return str;
}

std::string NegationFormula::prettyString(unsigned indentation) const {
  std::string str = std::string(indentation, ' ') + "NOT\n";
  str += f->prettyString(indentation + 3);
  return str;
}

std::string ExistentialFormula::prettyString(unsigned indentation) const {
  std::string str = std::string(indentation, ' ') + "EXISTS ";
  for (unsigned i = 0; i < vars.size(); i++) {
    str += vars[i]->name + " : " + vars[i]->rngSort->name;
    if (i != vars.size() - 1) {
      str += ", ";
    }
  }
  str += ".\n" + f->prettyString(indentation + 3);
  return str;
}

std::string UniversalFormula::prettyString(unsigned indentation) const {
  std::string str = std::string(indentation, ' ') + "FORALL ";
  for (unsigned i = 0; i < vars.size(); i++) {
    str += vars[i]->name + " : " + vars[i]->rngSort->name;
    if (i != vars.size() - 1) {
      str += ", ";
    }
  }
  str += ".\n";
  str += f->prettyString(indentation + 3);

  return str;
}

std::string ImplicationFormula::prettyString(unsigned indentation) const {
  std::string str = std::string(indentation, ' ') + "=>\n";
  str += f1->prettyString(indentation + 3) + "\n";
  str += f2->prettyString(indentation + 3);
  return str;
}

std::string EquivalenceFormula::prettyString(unsigned indentation) const {
  std::string str = std::string(indentation, ' ') + "=\n";
  str += f1->prettyString(indentation + 3) + "\n";
  str += f2->prettyString(indentation + 3);
  return str;
}

std::string TrueFormula::prettyString(unsigned indentation) const {
  return std::string(indentation, ' ') + "True";
}

std::string FalseFormula::prettyString(unsigned indentation) const {
  return std::string(indentation, ' ') + "False";
}

#pragma mark - Formulas
std::shared_ptr<const Formula> Formulas::predicate(
    std::string name, std::vector<std::shared_ptr<const Term>> subterms,
    std::string label, bool noDeclaration, SyS sym) {
  std::vector<const Sort*> subtermSorts;
  for (const auto& subterm : subterms) {
    subtermSorts.push_back(subterm->symbol->rngSort);
  }
  auto symbol = Signature::fetchOrAdd(name, subtermSorts, Sorts::boolSort(),
                                      noDeclaration, sym);
  return std::make_shared<const PredicateFormula>(symbol, subterms, label);
}
std::shared_ptr<const Formula> Formulas::lemmaPredicate(
    std::string name, std::vector<std::shared_ptr<const Term>> subterms,
    std::string label) {
  std::vector<const Sort*> subtermSorts;
  for (const auto& subterm : subterms) {
    subtermSorts.push_back(subterm->symbol->rngSort);
  }
  auto symbol =
      Signature::fetchOrAdd(name, subtermSorts, Sorts::boolSort(), false,
                            logic::Symbol::SymbolType::LemmaPredicate);
  return std::make_shared<const PredicateFormula>(symbol, subterms, label);
}

std::shared_ptr<const Formula> Formulas::equality(
    std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
    std::string label) {
  return std::make_shared<const EqualityFormula>(true, left, right, label);
}

std::shared_ptr<const Formula> Formulas::disequality(
    std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
    std::string label) {
  auto eq = std::make_shared<const EqualityFormula>(true, left, right);
  return std::make_shared<const NegationFormula>(eq, label);
}

std::shared_ptr<const Formula> Formulas::negation(
    std::shared_ptr<const Formula> f, std::string label) {
  return std::make_shared<const NegationFormula>(f, label);
}

std::shared_ptr<const Formula> Formulas::conjunction(
    std::vector<std::shared_ptr<const Formula>> conj, std::string label) {
  return std::make_shared<const ConjunctionFormula>(conj, label);
}
std::shared_ptr<const Formula> Formulas::disjunction(
    std::vector<std::shared_ptr<const Formula>> disj, std::string label) {
  return std::make_shared<const DisjunctionFormula>(disj, label);
}

std::shared_ptr<const Formula> Formulas::implication(
    std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
    std::string label) {
  return std::make_shared<const ImplicationFormula>(f1, f2, label);
}
std::shared_ptr<const Formula> Formulas::equivalence(
    std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
    std::string label) {
  return std::make_shared<const EquivalenceFormula>(f1, f2, label);
}

std::shared_ptr<const Formula> Formulas::existential(
    std::vector<std::shared_ptr<const Symbol>> vars,
    std::shared_ptr<const Formula> f, std::string label) {
  if (vars.empty()) {
    return copyWithLabel(f, label);
  } else {
    return std::make_shared<const ExistentialFormula>(std::move(vars), f,
                                                      label);
  }
}
std::shared_ptr<const Formula> Formulas::universal(
    std::vector<std::shared_ptr<const Symbol>> vars,
    std::shared_ptr<const Formula> f, std::string label) {
  if (vars.empty()) {
    return copyWithLabel(f, label);
  } else {
    return std::make_shared<const UniversalFormula>(std::move(vars), f, label);
  }
}

std::shared_ptr<const Formula> Formulas::trueFormula(std::string label) {
  return std::make_shared<const TrueFormula>(label);
}
std::shared_ptr<const Formula> Formulas::falseFormula(std::string label) {
  return std::make_shared<const FalseFormula>(label);
}

std::shared_ptr<const Formula> Formulas::equalitySimp(
    std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
    std::string label) {
  if (*left == *right) {
    return trueFormula(label);
  }
  return equality(left, right, label);
}

std::shared_ptr<const Formula> Formulas::disequalitySimp(
    std::shared_ptr<const Term> left, std::shared_ptr<const Term> right,
    std::string label) {
  if (*left == *right) {
    return falseFormula(label);
  }
  return disequality(left, right, label);
}

std::shared_ptr<const Formula> Formulas::negationSimp(
    std::shared_ptr<const Formula> f, std::string label) {
  if (f->type() == Formula::Type::True) {
    return falseFormula(label);
  } else if (f->type() == Formula::Type::False) {
    return trueFormula(label);
  } else if (f->type() == Formula::Type::Negation) {
    // double negation, get rid of both, we are not constructivists!
    return std::static_pointer_cast<const logic::NegationFormula>(f)->f;
  }

  return negation(f, label);
}

std::shared_ptr<const Formula> Formulas::conjunctionSimp(
    std::vector<std::shared_ptr<const Formula>> conj, std::string label) {
  for (const auto& conjunct : conj) {
    if (conjunct->type() == Formula::Type::False) {
      return falseFormula(label);
    }
  }

  auto isTrueFormula = [](std::shared_ptr<const logic::Formula> f) -> bool {
    return f->type() == Formula::Type::True;
  };
  conj.erase(std::remove_if(conj.begin(), conj.end(), isTrueFormula),
             conj.end());

  if (conj.empty()) {
    return trueFormula(label);
  } else if (conj.size() == 1) {
    return (label == "") ? conj.front() : copyWithLabel(conj.front(), label);
  }

  return conjunction(conj, label);
}
std::shared_ptr<const Formula> Formulas::disjunctionSimp(
    std::vector<std::shared_ptr<const Formula>> disj, std::string label) {
  for (const auto& disjunct : disj) {
    if (disjunct->type() == Formula::Type::True) {
      return trueFormula(label);
    }
  }

  auto isFalseFormula = [](std::shared_ptr<const logic::Formula> f) -> bool {
    return f->type() == Formula::Type::False;
  };
  disj.erase(std::remove_if(disj.begin(), disj.end(), isFalseFormula),
             disj.end());

  if (disj.empty()) {
    return falseFormula(label);
  } else if (disj.size() == 1) {
    return (label == "") ? disj.front() : copyWithLabel(disj.front(), label);
  }

  return disjunction(disj, label);
}

std::shared_ptr<const Formula> Formulas::implicationSimp(
    std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
    std::string label) {
  if (f1->type() == Formula::Type::False || f2->type() == Formula::Type::True) {
    return trueFormula(label);
  } else if (f1->type() == Formula::Type::True) {
    return (label == "") ? f2 : copyWithLabel(f2, label);
  } else if (f2->type() == Formula::Type::False) {
    return negation(f1, label);
  }

  return implication(f1, f2, label);
}

std::shared_ptr<const Formula> Formulas::equivalenceSimp(
    std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2,
    std::string label) {
  if (f1->type() == Formula::Type::True) {
    return (label == "") ? f2 : copyWithLabel(f2, label);
  } else if (f1->type() == Formula::Type::False) {
    return negation(f2, label);
  } else if (f2->type() == Formula::Type::True) {
    return (label == "") ? f1 : copyWithLabel(f1, label);
  } else if (f2->type() == Formula::Type::False) {
    return negation(f1, label);
  }

  return equivalence(f1, f2, label);
}

std::shared_ptr<const Formula> Formulas::existentialSimp(
    std::vector<std::shared_ptr<const Symbol>> vars,
    std::shared_ptr<const Formula> f, std::string label) {
  if (f->type() == Formula::Type::True || f->type() == Formula::Type::False) {
    return copyWithLabel(f, label);
  }

  return existential(vars, f, label);
}
std::shared_ptr<const Formula> Formulas::universalSimp(
    std::vector<std::shared_ptr<const Symbol>> vars,
    std::shared_ptr<const Formula> f, std::string label) {
  if (f->type() == Formula::Type::True || f->type() == Formula::Type::False) {
    return copyWithLabel(f, label);
  }

  return universal(vars, f, label);
}

std::shared_ptr<const Formula> Formulas::copyWithLabel(
    std::shared_ptr<const Formula> f, std::string label) {
  switch (f->type()) {
    case logic::Formula::Type::Predicate: {
      auto castedFormula =
          std::static_pointer_cast<const logic::PredicateFormula>(f);
      return std::make_shared<const PredicateFormula>(
          castedFormula->symbol, castedFormula->subterms, label);
    }
    case logic::Formula::Type::Equality: {
      auto castedFormula =
          std::static_pointer_cast<const logic::EqualityFormula>(f);
      return equality(castedFormula->left, castedFormula->right, label);
    }
    case logic::Formula::Type::Conjunction: {
      auto castedFormula =
          std::static_pointer_cast<const logic::ConjunctionFormula>(f);
      return conjunction(castedFormula->conj, label);
    }
    case logic::Formula::Type::Disjunction: {
      auto castedFormula =
          std::static_pointer_cast<const logic::DisjunctionFormula>(f);
      return disjunction(castedFormula->disj, label);
    }
    case logic::Formula::Type::Negation: {
      auto castedFormula =
          std::static_pointer_cast<const logic::NegationFormula>(f);
      return negation(castedFormula->f, label);
    }
    case logic::Formula::Type::Existential: {
      auto castedFormula =
          std::static_pointer_cast<const logic::ExistentialFormula>(f);
      return existential(castedFormula->vars, castedFormula->f, label);
    }
    case logic::Formula::Type::Universal: {
      auto castedFormula =
          std::static_pointer_cast<const logic::UniversalFormula>(f);
      return universal(castedFormula->vars, castedFormula->f, label);
    }
    case logic::Formula::Type::Implication: {
      auto castedFormula =
          std::static_pointer_cast<const logic::ImplicationFormula>(f);
      return implication(castedFormula->f1, castedFormula->f2, label);
    }
    case logic::Formula::Type::Equivalence: {
      auto castedFormula =
          std::static_pointer_cast<const logic::EquivalenceFormula>(f);
      return equivalence(castedFormula->f1, castedFormula->f2, label);
    }
    case logic::Formula::Type::True: {
      return trueFormula(label);
    }
    case logic::Formula::Type::False: {
      return falseFormula(label);
    }
    default: {
      assert(false);
      break;
    }
  }
}
}  // namespace logic
