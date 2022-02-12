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

  valueAt(tp, null, false);
  valueAt(tp, null, true);  
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
  return Terms::func("null_loc", {}, Sorts::intSort(), false);
}

std::shared_ptr<const FuncTerm> Theory::valueAt(
    std::shared_ptr<const Term> timePoint,
    std::shared_ptr<const Term> location,
    bool isConst) {

  std::vector<std::shared_ptr<const Term>> subterms;
  if(!isConst){
    subterms.push_back(timePoint);
  }
  subterms.push_back(location);

  std::string str = isConst ? "_const" : "";
  std::string funcName = "value" + str;

  return Terms::func(funcName, subterms, Sorts::intSort(), false);
}

std::shared_ptr<const Formula> Theory::framePred(
      std::shared_ptr<const Term> location,
      std::shared_ptr<const Term> t1,
      std::shared_ptr<const Term> t2) {
  return Formulas::predicate("frame_axiom", {location, t1, t2});
}

std::shared_ptr<logic::Axiom> Theory::frameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::shared_ptr<const logic::Symbol> memLocVarSym) 
{
  auto memLocVariable = logic::Terms::var(memLocVarSym);
  auto tpVar = logic::Terms::var(tpVarSym1);  
  auto tpVar2 = logic::Terms::var(tpVarSym2);

  auto framePred = logic::Theory::framePred(memLocVariable, tpVar, tpVar2);
  auto loc = logic::Signature::varSymbol("m-loc", logic::Sorts::intSort());
  auto locVar = logic::Terms::var(loc); 

  auto notEqual = logic::Formulas::disequality(memLocVariable, locVar);
  auto rhs = logic::Formulas::equality(
    logic::Theory::valueAt(tpVar, locVar),
    logic::Theory::valueAt(tpVar2, locVar));
  rhs =  logic::Formulas::implicationSimp(notEqual, rhs);
  rhs =  logic::Formulas::universal({loc}, rhs);

  auto frameDefinition = logic::Formulas::universal({memLocVarSym,tpVarSym1,tpVarSym2 },
    logic::Formulas::equivalenceSimp(framePred, rhs));
  return std::make_shared<logic::Axiom>(
    frameDefinition, "Definition of the frame axiom",
    logic::ProblemItem::Visibility::Implicit);
}


std::shared_ptr<const Formula> Theory::disjoint1(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> size1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> size2) {
  return Formulas::predicate("disjoint1", {loc1, size1, loc2, size2});
}

std::shared_ptr<logic::Axiom> Theory::disjoint1Axiom(
      std::shared_ptr<const logic::Symbol> memLocVarSym1,
      std::shared_ptr<const logic::Symbol> sizeSym1,      
      std::shared_ptr<const logic::Symbol> memLocVarSym2,
      std::shared_ptr<const logic::Symbol> sizeSym2)
{
  auto memLocVar1 = logic::Terms::var(memLocVarSym1);
  auto size1 = logic::Terms::var(sizeSym1);  
  auto memLocVar2 = logic::Terms::var(memLocVarSym2);
  auto size2 = logic::Terms::var(sizeSym2);
  
  auto disjointPred = disjoint1(memLocVar1, size1, memLocVar2, size2);

  auto x1Sym = logic::Signature::varSymbol("x1", logic::Sorts::intSort());
  auto x1 = logic::Terms::var(x1Sym); 

  auto x2Sym = logic::Signature::varSymbol("x2", logic::Sorts::intSort());
  auto x2 = logic::Terms::var(x2Sym);

  std::vector<std::shared_ptr<const logic::Formula>> forms;
  forms.push_back(Theory::intLessEqual(memLocVar1, x1));
  forms.push_back(Theory::intLess(x1, Theory::intAddition(memLocVar1, size1)));
  forms.push_back(Theory::intLessEqual(memLocVar2, x2));
  forms.push_back(Theory::intLess(x2, Theory::intAddition(memLocVar2, size2)));
  auto premise = logic::Formulas::conjunctionSimp(forms);
  auto conc = logic::Formulas::disequality(x1,x2);
  auto imp = logic::Formulas::implicationSimp(premise, conc);
  auto rhs = logic::Formulas::universal({x1Sym, x2Sym}, imp);

  auto disjointDef = logic::Formulas::universal({memLocVarSym1,sizeSym1,memLocVarSym2, sizeSym2},
    logic::Formulas::equivalenceSimp(disjointPred, rhs));

  return std::make_shared<logic::Axiom>(
    disjointDef, "Definition of disjointness axiom",
    logic::ProblemItem::Visibility::Implicit);
}

std::shared_ptr<const Formula> Theory::disjoint2(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> size) {
  return Formulas::predicate("disjoint2", {loc1, loc2, size});
}  

std::shared_ptr<logic::Axiom> Theory::disjoint2Axiom(
      std::shared_ptr<const logic::Symbol> memLocVarSym1,
      std::shared_ptr<const logic::Symbol> memLocVarSym2,
      std::shared_ptr<const logic::Symbol> sizeSym)
{
  auto memLocVar1 = logic::Terms::var(memLocVarSym1);
  auto memLocVar2 = logic::Terms::var(memLocVarSym2);
  auto size = logic::Terms::var(sizeSym);
  
  auto disjointPred = disjoint2(memLocVar1, memLocVar2, size);

  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym); 

  std::vector<std::shared_ptr<const logic::Formula>> forms;
  forms.push_back(Theory::intLessEqual(memLocVar2, x));
  forms.push_back(Theory::intLess(x, Theory::intAddition(memLocVar2, size)));
  auto premise = logic::Formulas::conjunctionSimp(forms);
  auto conc = logic::Formulas::disequality(memLocVar1,x);
  auto imp = logic::Formulas::implicationSimp(premise, conc);
  auto rhs = logic::Formulas::universal({xSym}, imp);

  auto disjointDef = logic::Formulas::universal({memLocVarSym1,memLocVarSym2, sizeSym},
    logic::Formulas::equivalenceSimp(disjointPred, rhs));

  return std::make_shared<logic::Axiom>(
    disjointDef, "Definition of disjointness axiom",
    logic::ProblemItem::Visibility::Implicit);  
}

std::shared_ptr<const FuncTerm> Theory::mallocFun(
    std::shared_ptr<const Term> timePoint) {

  return Terms::func("malloc", {timePoint}, Sorts::intSort(), false, 
    logic::Symbol::SymbolType::MallocFunc);
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
