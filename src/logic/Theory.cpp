#include "Theory.hpp"

#include "Options.hpp"
#include "Signature.hpp"

namespace logic {

// declare each function-/predicate-symbol by constructing it
// has additional sideeffect of declaring the involved sorts
void Theory::declareTheories() {
  boolTrue();
  boolFalse();

  auto intConst = intConstant(0);
  intAddition(intConst, intConst);
  intSubtraction(intConst, intConst);
  intModulo(intConst, intConst);
  intMultiplication(intConst, intConst);
  intAbsolute(intConst);
  intLess(intConst, intConst);
  intLessEqual(intConst, intConst);
  intGreater(intConst, intConst);
  intGreaterEqual(intConst, intConst);

  auto zero = Theory::zero();

  if (!util::Configuration::instance().integerIterations()) {
    natSucc(zero);
    natPre(zero);
    natSub(zero, zero);
  }
}

void Theory::declareMemoryArrays() {
  auto null = nullLoc();
  auto tp = arbitraryTP();

  auto sel = Signature::fetchArraySelect();
  auto store = Signature::fetchArrayStore();

  //valueAt(tp, null, "Int", false);
  deref(tp, null);
}

std::shared_ptr<const FuncTerm> Theory::intConstant(int i) {
  return Terms::func(std::to_string(i), {}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::intZero() {
  return Theory::intConstant(0);
}

std::shared_ptr<const FuncTerm> Theory::intAddition(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2) {
  return Terms::func("+", {t1, t2}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::intSubtraction(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2) {
  return Terms::func("-", {t1, t2}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::intModulo(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2) {
  return Terms::func("mod", {t1, t2}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::intMultiplication(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2) {
  return Terms::func("*", {t1, t2}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::intAbsolute(
    std::shared_ptr<const Term> t) {
  return Terms::func("abs", {t}, Sorts::intSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::toInt(std::shared_ptr<const Term> t) {
  return Terms::func("to-int", {t}, Sorts::intSort(), false);
}

std::shared_ptr<const FuncTerm> Theory::intSucc(std::shared_ptr<const Term> t) {
  return intAddition(t, Theory::intConstant(1));
}

std::shared_ptr<const Formula> Theory::intLess(std::shared_ptr<const Term> t1,
                                               std::shared_ptr<const Term> t2,
                                               std::string label) {
  return Formulas::predicate("<", {t1, t2}, label, true);
}

std::shared_ptr<const Formula> Theory::intLessEqual(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
    std::string label) {
  return Formulas::predicate("<=", {t1, t2}, label, true);
}

std::shared_ptr<const Formula> Theory::intGreater(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
    std::string label) {
  return Formulas::predicate(">", {t1, t2}, label, true);
}

std::shared_ptr<const Formula> Theory::intGreaterEqual(
    std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
    std::string label) {
  return Formulas::predicate(">=", {t1, t2}, label, true);
}

std::shared_ptr<const Formula> Theory::boolTrue(std::string label) {
  return Formulas::trueFormula(label);
}

std::shared_ptr<const Formula> Theory::boolFalse(std::string label) {
  return Formulas::falseFormula(label);
}

std::shared_ptr<const FuncTerm> Theory::natZero() {
  return Terms::func("zero", {}, Sorts::natSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::natSucc(
    std::shared_ptr<const Term> term) {
  return Terms::func("s", {term}, Sorts::natSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::natPre(
    std::shared_ptr<const Term> term) {
  return Terms::func("p", {term}, Sorts::natSort(), true);
}

std::shared_ptr<const Formula> Theory::natSub(std::shared_ptr<const Term> t1,
                                              std::shared_ptr<const Term> t2,
                                              std::string label) {
  bool alreadyDeclared = util::Configuration::instance().nativeNat();
  return Formulas::predicate("Sub", {t1, t2}, label, alreadyDeclared);
}

std::shared_ptr<const Formula> Theory::natSubEq(std::shared_ptr<const Term> t1,
                                                std::shared_ptr<const Term> t2,
                                                std::string label) {
  // encode t1<=t2 as t1 < s(t2).
  return Theory::natSub(t1, natSucc(t2), label);
}

std::shared_ptr<const FuncTerm> Theory::succ(std::shared_ptr<const Term> t) {
  if (util::Configuration::instance().integerIterations()) {
    return Theory::intSucc(t);
  }
  return Theory::natSucc(t);
}

std::shared_ptr<const Formula> Theory::less(std::shared_ptr<const Term> t1,
                                            std::shared_ptr<const Term> t2,
                                            std::string label) {
  if (util::Configuration::instance().integerIterations()) {
    return Theory::intLess(t1, t2, label);
  }
  return Theory::natSub(t1, t2, label);
}

std::shared_ptr<const Formula> Theory::lessEq(std::shared_ptr<const Term> t1,
                                              std::shared_ptr<const Term> t2,
                                              std::string label) {
  if (util::Configuration::instance().integerIterations()) {
    return Theory::intLessEqual(t1, t2, label);
  }
  return Theory::natSubEq(t1, t2, label);
}

std::shared_ptr<const FuncTerm> Theory::zero() {
  if (util::Configuration::instance().integerIterations()) {
    return Theory::intZero();
  }
  return Theory::natZero();
}

std::shared_ptr<const FuncTerm> Theory::arbitraryTP() {
  return Terms::func("arbitrary-tp", {}, Sorts::timeSort(), true);
}

std::shared_ptr<const FuncTerm> Theory::nullLoc() {
  return Terms::func("null-loc", {}, Sorts::locSort(), false);
}

std::shared_ptr<const FuncTerm> Theory::valueAt(
    std::shared_ptr<const Term> timePoint,
    std::shared_ptr<const Term> location,
    std::string sortName,
    bool isConst) {

  std::vector<std::shared_ptr<const Term>> subterms;
  if(!isConst){
    subterms.push_back(timePoint);
  }
  subterms.push_back(location);

  std::string str = isConst ? "const_" : "";
  std::string funcName = "value_" + str + toLower(sortName);

  return Terms::func(funcName, subterms, Sorts::fetch(sortName), false);
}

std::shared_ptr<const FuncTerm> Theory::deref(
    std::shared_ptr<const Term> timePoint, std::shared_ptr<const Term> location,
    unsigned level) {
  assert(level >= 1);

  auto term =
      Terms::func("deref", {timePoint, location}, Sorts::locSort(), false);
  for (unsigned i = 0; i < level - 1; i++) {
    term = Terms::func("deref", {timePoint, term}, Sorts::locSort(), false);
  }
  return term;
}

std::tuple<std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>, std::shared_ptr<logic::Axiom>>
inductionAxiom1(
    std::string name, std::string shortName,
    std::function<std::shared_ptr<const Formula>(std::shared_ptr<const Term>)>
        inductionHypothesis,
    std::vector<std::shared_ptr<const Symbol>> freeVarSymbols,
    ProblemItem::Visibility visibility) {
  auto boundLSymbol =
      logic::Signature::varSymbol("boundL", logic::Sorts::natSort());
  auto boundRSymbol =
      logic::Signature::varSymbol("boundR", logic::Sorts::natSort());
  auto itIndSymbol =
      logic::Signature::varSymbol("itInd", logic::Sorts::natSort());

  if (util::Configuration::instance().integerIterations()) {
    boundLSymbol =
        logic::Signature::varSymbol("boundL", logic::Sorts::intSort());
    boundRSymbol =
        logic::Signature::varSymbol("boundR", logic::Sorts::intSort());
    itIndSymbol = logic::Signature::varSymbol("itInd", logic::Sorts::intSort());
  }

  auto boundL = Terms::var(boundLSymbol);
  auto boundR = Terms::var(boundRSymbol);
  auto itInd = Terms::var(itIndSymbol);

  std::vector<std::shared_ptr<const Symbol>> argSymbols1 = {boundLSymbol};
  std::vector<std::shared_ptr<const Symbol>> argSymbols2 = {boundLSymbol,
                                                            boundRSymbol};
  std::vector<std::shared_ptr<const Term>> args1 = {boundL};
  std::vector<std::shared_ptr<const Term>> args2 = {boundL, boundR};
  for (const auto& varSymbol : freeVarSymbols) {
    argSymbols1.push_back(varSymbol);
    argSymbols2.push_back(varSymbol);
    args1.push_back(Terms::var(varSymbol));
    args2.push_back(Terms::var(varSymbol));
  }

  auto baseCase = Formulas::lemmaPredicate("BC-" + shortName, args1);
  auto inductiveCase = Formulas::lemmaPredicate("IC-" + shortName, args2);
  auto conclusion = Formulas::lemmaPredicate("Con-" + shortName, args2);

  auto baseCaseDef = Formulas::universal(
      argSymbols1,
      Formulas::equivalence(baseCase, inductionHypothesis(boundL)));
  auto inductiveCaseDef = Formulas::universal(
      argSymbols2,
      Formulas::equivalence(
          inductiveCase,
          Formulas::universal(
              {itIndSymbol},
              Formulas::implication(
                  Formulas::conjunction({Theory::lessEq(boundL, itInd),
                                         Theory::less(itInd, boundR),
                                         inductionHypothesis(itInd)}),
                  inductionHypothesis(Theory::succ(itInd))))));
  auto conclusionDef = Formulas::universal(
      argSymbols2,
      Formulas::equivalence(
          conclusion,
          Formulas::universal(
              {itIndSymbol},
              Formulas::implication(
                  Formulas::conjunction({Theory::lessEq(boundL, itInd),
                                         Theory::lessEq(itInd, boundR)}),
                  inductionHypothesis(itInd)))));

  auto inductionAxiom = Formulas::universal(
      argSymbols2,
      Formulas::implication(Formulas::conjunction({baseCase, inductiveCase}),
                            conclusion));

  return std::make_tuple(
      std::make_shared<logic::Definition>(baseCaseDef, "Base-Case for " + name,
                                          visibility),
      std::make_shared<logic::Definition>(
          inductiveCaseDef, "Inductive-Case for " + name, visibility),
      std::make_shared<logic::Definition>(conclusionDef,
                                          "Conclusion for " + name, visibility),
      std::make_shared<logic::Axiom>(inductionAxiom, name, visibility));
}

std::tuple<std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>, std::shared_ptr<logic::Axiom>>
inductionAxiom2(
    std::string name, std::string shortName,
    std::function<std::shared_ptr<const Formula>(std::shared_ptr<const Term>)>
        inductionHypothesis,
    std::shared_ptr<const logic::Term> nt1,
    std::shared_ptr<const logic::Term> nt2,
    std::vector<std::shared_ptr<const Symbol>> freeVarSymbols,
    ProblemItem::Visibility visibility) {
  auto itIndSymbol =
      logic::Signature::varSymbol("itInd", logic::Sorts::natSort());
  if (util::Configuration::instance().integerIterations()) {
    itIndSymbol = logic::Signature::varSymbol("itInd", logic::Sorts::intSort());
  }
  auto itInd = Terms::var(itIndSymbol);

  std::vector<std::shared_ptr<const Term>> freeVars = {};
  for (const auto& varSymbol : freeVarSymbols) {
    freeVars.push_back(Terms::var(varSymbol));
  }

  auto baseCase = Formulas::lemmaPredicate("BC-" + shortName, freeVars);
  auto inductiveCase = Formulas::lemmaPredicate("IC-" + shortName, freeVars);
  auto conclusion = Formulas::lemmaPredicate("Con-" + shortName, freeVars);

  auto baseCaseDef = Formulas::universal(
      freeVarSymbols,
      Formulas::equivalence(baseCase, inductionHypothesis(Theory::zero())));
  auto inductiveCaseDef = Formulas::universal(
      freeVarSymbols,
      Formulas::equivalence(
          inductiveCase,
          Formulas::universal(
              {itIndSymbol},
              Formulas::implication(
                  Formulas::conjunction({Theory::less(itInd, nt1),
                                         Theory::less(itInd, nt2),
                                         inductionHypothesis(itInd)}),
                  inductionHypothesis(Theory::succ(itInd))))));
  auto conclusionDef = Formulas::universal(
      freeVarSymbols,
      Formulas::equivalence(
          conclusion,
          Formulas::universal(
              {itIndSymbol},
              Formulas::implication(
                  Formulas::conjunction({Theory::natSubEq(itInd, nt1),
                                         Theory::natSubEq(itInd, nt2)}),
                  inductionHypothesis(itInd)))));

  auto inductionAxiom = Formulas::universal(
      freeVarSymbols,
      Formulas::implication(Formulas::conjunction({baseCase, inductiveCase}),
                            conclusion));

  return std::make_tuple(
      std::make_shared<logic::Definition>(baseCaseDef, "Base-Case for " + name,
                                          visibility),
      std::make_shared<logic::Definition>(
          inductiveCaseDef, "Inductive-Case for " + name, visibility),
      std::make_shared<logic::Definition>(conclusionDef,
                                          "Conclusion for " + name, visibility),
      std::make_shared<logic::Axiom>(inductionAxiom, name, visibility));
}
}  // namespace logic
