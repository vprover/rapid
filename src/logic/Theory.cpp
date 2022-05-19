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

  // false means non-const value array
  valueAt(tp, null, "Int", false);
  valueAt(tp, null, "Int", true);  
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

std::shared_ptr<const FuncTerm> Theory::nullLoc(std::string sortName) {

  auto sort = Sorts::fetch(sortName);;
  std::string prefix = "";
  if(sortName != "Int"){
    prefix = toLower(sortName) + "_";
  }

  return Terms::func(prefix + "null_loc", {}, sort, false);
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

  std::string str = isConst ? "_const" : "";
  str = str + (sortName == "Int" ? "" : "_" + toLower(sortName));
  std::string funcName = "value" + str;

  return Terms::func(funcName, subterms, Sorts::fetch(sortName), false);
}

std::shared_ptr<const FuncTerm> Theory::selectorAt(
    std::string selectorName,
    std::shared_ptr<const Term> timePoint,
    std::shared_ptr<const Term> object) {
  assert(util::Configuration::instance().memoryModel() == "typed");

  auto sym = Signature::fetch(selectorName);
  assert(sym->isSelectorSymbol());
  return Terms::func(sym, {timePoint, object});
}

std::shared_ptr<const FuncTerm> Theory::chain(
    std::string selectorName, 
    std::shared_ptr<const Term> location,    
    std::shared_ptr<const Term> timePoint,
    std::shared_ptr<const Term> length,      
    std::string sortName) {
  // TODO add untyped version
  assert(util::Configuration::instance().memoryModel() == "typed");
 
  auto sort = Sorts::fetch(sortName);
  auto name = selectorName + "_chain";
  return Terms::func(name, {location, timePoint, length}, sort, false, 
    logic::Symbol::SymbolType::ChainFunc);
}

std::shared_ptr<const Formula> Theory::inChainSupport(
  std::string selectorName, 
  std::shared_ptr<const Term> timePoint,
  std::shared_ptr<const Term> location1,
  std::shared_ptr<const Term> location2,      
  std::shared_ptr<const Term> length) {

  assert(util::Configuration::instance().memoryModel() == "typed");
  auto name = "in_support_" + selectorName + "_chain";
  return Formulas::predicate(name, {location1, timePoint, location2, length});
}

std::tuple<std::shared_ptr<logic::Axiom>,
          std::shared_ptr<logic::Axiom>,
          std::shared_ptr<logic::Axiom>>
Theory::chainAxioms(
    std::string selectorName,      
    std::string sortName) {

  auto sort = Sorts::fetch(sortName);
  auto zero = Theory::zero();

  auto varName = toLower(sortName) + "_var";
  auto varSym = logic::Signature::varSymbol(varName, sort);
  auto var = Terms::var(varSym);

  auto tpSym = logic::Signature::varSymbol("tp", Sorts::timeSort());
  auto tp = Terms::var(tpSym);

  // TODO ensure uniqueness of variable names 
  auto lenSym = logic::Signature::varSymbol("chain_len", Sorts::intSort());
  auto len = Terms::var(lenSym);
  auto lenSubOne = Theory::intSubtraction(len, Theory::intConstant(1));

  auto zeroLessLen = Theory::less(zero, len);

  // f_chain(loc, tp, 0)
  auto lhs1 = Theory::chain(selectorName, var, tp, zero, sortName);
  // f_chain(loc, tp, 0) = loc;
  auto baseCase = Formulas::universal({varSym, tpSym},
                    Formulas::equality(lhs1, var));


  auto lhs2 = Theory::chain(selectorName, var, tp, len, sortName);
  auto term = Theory::selectorAt(selectorName, tp, var);  
  auto rhs = Theory::chain(selectorName, term, tp, lenSubOne, sortName);

  auto inductiveCase = 
    Formulas::universal({varSym, tpSym, lenSym},
      Formulas::implication(
        zeroLessLen,              
        Formulas::equality(lhs2, rhs)));

  // f(tp, f_chain(loc, tp, len))
  auto lhs3 = Theory::selectorAt(selectorName, tp, lhs2);
  // f_chain(f(loc), tp, len)  
  auto rhs3 = Theory::chain(selectorName, term, tp, len, sortName);

  auto helperLemma =
     Formulas::universal({varSym, tpSym, lenSym}, 
      Formulas::equality(lhs3, rhs3));

  return std::make_tuple(
      std::make_shared<logic::Axiom>(baseCase, "Base case " + selectorName),
      std::make_shared<logic::Axiom>(inductiveCase, "Inductive case " + selectorName),
      std::make_shared<logic::Axiom>(helperLemma, "Helpful lemma " + selectorName));
}

std::shared_ptr<const Formula> Theory::isList(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> tp)
{
  return Formulas::predicate("is_list", {loc1, loc2, tp});    
} 

std::shared_ptr<const FuncTerm> Theory::listLocs(
  std::shared_ptr<const Term> loc1,
  std::shared_ptr<const Term> loc2,
  std::shared_ptr<const Term> tp)
{
  return Terms::func("list_locs", {loc1, loc2, tp}, Sorts::intSetSort(), false);
}

std::shared_ptr<const Formula> Theory::listLocsPred(
  std::shared_ptr<const Term> loc1,
  std::shared_ptr<const Term> loc2,
  std::shared_ptr<const Term> tp,
  std::shared_ptr<const Term> loc3)
{
  return Formulas::predicate("in_list_locs", {loc1, loc2, tp, loc3});      
}

std::shared_ptr<const Formula> Theory::isAcyclicList(
      std::shared_ptr<const Term> loc,
      std::shared_ptr<const Term> tp)
{
  return Formulas::predicate("is_acyclic_list", {loc, tp});    
} 

std::shared_ptr<const FuncTerm> Theory::acyclicListLocs(
  std::shared_ptr<const Term> loc,
  std::shared_ptr<const Term> tp)
{
  return Terms::func("acyclic_list_locs", {loc, tp}, Sorts::intSetSort(), false);
}

std::shared_ptr<const Formula>  Theory::acyclicListLocsPred(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> tp,
      std::shared_ptr<const Term> loc2)
{
  return Formulas::predicate("in_acyclic_list_locs", {loc1, tp, loc2});  
}

std::shared_ptr<const Formula> Theory::heapLoc(
  std::shared_ptr<const Term> location)
{
  return Formulas::predicate("heap_loc", {location});  
} 

std::shared_ptr<const Formula> Theory::framePred(
      std::shared_ptr<const Term> location,
      std::shared_ptr<const Term> t1,
      std::shared_ptr<const Term> t2,
      std::string suffix) {

  return Formulas::lemmaPredicate("frame_axiom" + suffix, {location, t1, t2});
}

std::shared_ptr<logic::Axiom> Theory::untypedFrameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::shared_ptr<const logic::Symbol> m1VarSym) 
{
  auto m1Var = logic::Terms::var(m1VarSym);
  auto tpVar = logic::Terms::var(tpVarSym1);  
  auto tpVar2 = logic::Terms::var(tpVarSym2);

  auto framePred = Theory::framePred(m1Var, tpVar, tpVar2);
  auto m2VarSym = Signature::varSymbol("m2", logic::Sorts::intSort());
  auto m2Var = Terms::var(m2VarSym); 

  auto isHeapM1 = heapLoc(m1Var);
  auto isHeapM2 = heapLoc(m2Var);
  auto notIsHeapM1 = Formulas::negation(isHeapM1);
  auto notIsHeapM2 = Formulas::negation(isHeapM2);
  
  auto locsNotEqual = Formulas::disequality(m1Var, m2Var);
  auto holdsValue = Formulas::equality(
    valueAt(tpVar, m2Var), 
    valueAt(tpVar2, m2Var));

  auto conj1 = Formulas::conjunction({notIsHeapM1, notIsHeapM2, locsNotEqual});
  auto imp1 = Formulas::implication(conj1, holdsValue);
 
  auto listThingsStaySame = Formulas::trueFormula();
  auto guardedListsStaySame = Formulas::trueFormula();
  if(util::Configuration::instance().useLists() == "acyclic"){
    auto isListTp1 = isAcyclicList(m2Var, tpVar); 
    auto isListTp2 = isAcyclicList(m2Var, tpVar2);
    auto isListStaysSame = Formulas::equivalence(isListTp1, isListTp2);
    
    std::shared_ptr<const Formula> listLocsStaySame, notInListLocs;  
    if(util::Configuration::instance().useLocSets()){
      auto ListLocsTp1 = acyclicListLocs(m2Var, tpVar);  
      auto ListLocsTp2 = acyclicListLocs(m2Var, tpVar2);  
      listLocsStaySame = Formulas::equality(ListLocsTp1, ListLocsTp2);
      notInListLocs = Formulas::negation(in(m1Var, ListLocsTp1));
    } else {
      auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
      auto x = logic::Terms::var(xSym);

      auto ListLocsTp1 = acyclicListLocsPred(m2Var, tpVar, x);  
      auto ListLocsTp2 = acyclicListLocsPred(m2Var, tpVar2, x);
      listLocsStaySame = Formulas::equivalence(ListLocsTp1, ListLocsTp2);
      listLocsStaySame = Formulas::universal({xSym}, listLocsStaySame);
      notInListLocs = Formulas::negation(acyclicListLocsPred(m2Var, tpVar, m1Var));
    }
    listThingsStaySame = Formulas::conjunction({isListStaysSame, listLocsStaySame});
    guardedListsStaySame = Formulas::implication(notInListLocs, listThingsStaySame);
  } //TODO cyclic

  auto conj2a = Formulas::conjunction({isHeapM1, notIsHeapM2});
  auto conj2b = Formulas::conjunction({notIsHeapM1, isHeapM2});
  auto disj = Formulas::disjunction({conj2a, conj2b});
  auto imp2 = Formulas::implication(disj, 
    Formulas::conjunctionSimp({holdsValue, listThingsStaySame}));

  auto conj3 = Formulas::conjunction({isHeapM1, isHeapM2});
  auto imp3 = Formulas::implication(locsNotEqual, holdsValue);

  auto imp4 = Formulas::implication(conj3, 
    Formulas::conjunctionSimp({imp3, guardedListsStaySame}));

  auto conj = Formulas::conjunctionSimp({imp1, imp2, imp4});
  conj = Formulas::universal({m2VarSym}, conj);

  auto frameDefinition = Formulas::universal({m1VarSym,tpVarSym1,tpVarSym2},
    Formulas::equivalenceSimp(framePred, conj));
  return std::make_shared<logic::Axiom>(
    frameDefinition, "Definition of the frame axiom",
    logic::ProblemItem::Visibility::Implicit);
}

std::shared_ptr<logic::Axiom> Theory::typedFrameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::shared_ptr<const logic::Symbol> m1VarSym) 
{
  auto m1Var = logic::Terms::var(m1VarSym);
  auto tpVar = logic::Terms::var(tpVarSym1);  
  auto tpVar2 = logic::Terms::var(tpVarSym2);

  auto framePred = Theory::framePred(m1Var, tpVar, tpVar2);
  auto m2VarSym = Signature::varSymbol("m2", logic::Sorts::intSort());
  auto m2Var = Terms::var(m2VarSym); 

  
  auto locsNotEqual = Formulas::disequality(m1Var, m2Var);

  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;
  auto structSorts = logic::Sorts::structSorts();
  for(auto sort : structSorts){
    auto holdsValue = Formulas::equality(
      valueAt(tpVar, m2Var, sort->name), 
      valueAt(tpVar2, m2Var, sort->name));
    conjuncts.push_back(holdsValue);
  }
  conjuncts.push_back(Formulas::equality(
    valueAt(tpVar, m2Var), 
    valueAt(tpVar2, m2Var)));

  auto conj = Formulas::conjunctionSimp(conjuncts);
  auto imp = Formulas::implication(locsNotEqual, conj);
  imp = Formulas::universal({m2VarSym}, imp);

  auto frameDefinition = Formulas::universal({m1VarSym,tpVarSym1,tpVarSym2},
    Formulas::equivalenceSimp(framePred, imp));
  return std::make_shared<logic::SpecAxiom>(
    frameDefinition, "Definition of the frame axiom",
    logic::ProblemItem::Visibility::Implicit);
}

std::shared_ptr<logic::Axiom> Theory::frameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::string sortName,
      std::string selectorName)
{
  auto selSym = Signature::fetch(selectorName);
  bool isRecursiveSel = selSym->rngSort->name == sortName;

  auto sort = Sorts::fetch(sortName);
  assert(sort->isStructSort());
  auto structSort = static_cast<StructSort*>(sort);

  auto o1sym = Signature::varSymbol("o1", sort);
  auto o2sym = Signature::varSymbol("o2", sort);
  auto o3sym = Signature::varSymbol("o3", sort);

  auto tp1var = logic::Terms::var(tpVarSym1);  
  auto tp2var = logic::Terms::var(tpVarSym2);

  auto o1var = logic::Terms::var(o1sym);  
  auto o2var = logic::Terms::var(o2sym);
  auto o3var = logic::Terms::var(o3sym);

  auto framePred = Theory::framePred(o1var, tp1var, tp2var, "_" + selectorName);

  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto objectsNotEqual = Formulas::disequality(o1var, o2var);
  auto equality1 = Formulas::equality(
      selectorAt(selectorName, tp1var, o2var),
      selectorAt(selectorName, tp2var, o2var)      
    );
  auto imp = Formulas::implication(objectsNotEqual, equality1);
  conjuncts.push_back(imp);

  if(isRecursiveSel){
    auto lsym = Signature::varSymbol("chain_len", Sorts::intSort());
    auto len = logic::Terms::var(lsym);  

    auto notInSup = Formulas::negation(
      inChainSupport(selectorName, tp1var, o1var, o2var, len));

    auto conclusion = Formulas::conjunction({
      Formulas::universal({o3sym}, 
        Formulas::equivalence(
          inChainSupport(selectorName, tp1var, o3var, o2var,len), 
          inChainSupport(selectorName, tp2var, o3var, o2var,len))),
      Formulas::equality(
        chain(selectorName,o2var, tp1var, len, sortName),
        chain(selectorName,o2var, tp2var, len, sortName))
    });

    conjuncts.push_back(
      Formulas::universal({lsym}, 
        Formulas::implication(notInSup, conclusion)));

  }

  for(auto selector : structSort->selectors()){
    if(selector != selectorName){
      auto holdsValue = Formulas::equality(
        selectorAt(selector, tp1var, o2var), 
        selectorAt(selector, tp2var, o2var));
      conjuncts.push_back(holdsValue);
    }
  }

  auto conj = Formulas::conjunctionSimp(conjuncts);
  conj = Formulas::universal({o2sym}, conj);

  auto frameDefinition = Formulas::universal({o1sym,tpVarSym1,tpVarSym2},
    Formulas::equivalenceSimp(framePred, conj));
  return std::make_shared<logic::SpecAxiom>(
    frameDefinition, "Definition of the frame axiom",
    logic::ProblemItem::Visibility::Implicit);  
}

std::shared_ptr<const Formula> Theory::allSame(
    std::shared_ptr<const Term> tp1,
    std::shared_ptr<const Term> tp2,
    std::string prefix) {
  auto str = logic::toLower(prefix) + "s_";
  return Formulas::lemmaPredicate(str + "same", {tp1, tp2});
} 

std::shared_ptr<logic::Axiom> Theory::allSameAxiom(
  std::shared_ptr<const logic::Symbol> tpVarSym1,
  std::shared_ptr<const logic::Symbol> tpVarSym2,
  std::string sortName) {

  auto tp1 = logic::Terms::var(tpVarSym1);  
  auto tp2 = logic::Terms::var(tpVarSym2);

  bool value = sortName == "Int";
  auto sort = logic::Sorts::fetch(sortName);
  auto varName = sort->isIntSort() ? "n" : toLower(sort->name) + "_var"; 

  auto varSym = Signature::varSymbol(varName, sort);
  auto var = Terms::var(varSym);

  auto prefix = value ? "value" : sortName;
  auto pred = allSame(tp1, tp2, prefix);
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;
  if(value){
    auto structSorts = logic::Sorts::structSorts();
    for(auto sort : structSorts){
      auto holdsValue = Formulas::equality(
        valueAt(tp1, var, sort->name), 
        valueAt(tp2, var, sort->name));
      conjuncts.push_back(holdsValue);
    }
    conjuncts.push_back(Formulas::equality(
        valueAt(tp1, var), 
        valueAt(tp2, var)));
  } else {
    assert(sort->isStructSort());
    auto structSort = static_cast<logic::StructSort*>(sort);
    auto selectors = structSort->selectors();
    for(auto selector : selectors){
      auto sym = Signature::fetch(selector);
      auto lhs = Terms::func(sym, {tp1, var});
      auto rhs = Terms::func(sym, {tp2, var});
      conjuncts.push_back(Formulas::equality(lhs, rhs));      
    }
  }
  
  auto conjunct = Formulas::conjunctionSimp(conjuncts);
  conjunct = Formulas::universal({varSym}, conjunct);
  auto def = Formulas::equivalence(pred, conjunct);
  def = Formulas::universal({tpVarSym1,tpVarSym2}, def);
  return std::make_shared<logic::SpecAxiom>(
    def, "Definition of staying the same across time points",
    logic::ProblemItem::Visibility::Implicit);  
}


std::shared_ptr<logic::Axiom> Theory::chainSameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::string sortName,
      std::string selectorName)
{
  auto sort = Sorts::fetch(sortName);
  assert(sort->isStructSort());
  auto structSort = static_cast<StructSort*>(sort);

  auto osym = Signature::varSymbol("o", sort);
  auto o3sym = Signature::varSymbol("o3", sort); 
  auto lsym = Signature::varSymbol("chain_len", Sorts::intSort());

  auto tp1var = logic::Terms::var(tpVarSym1);  
  auto tp2var = logic::Terms::var(tpVarSym2);

  auto ovar = logic::Terms::var(osym); 
  auto o3var = logic::Terms::var(o3sym);    
  auto len = logic::Terms::var(lsym);  

  auto samePred = Theory::allSame(tp1var, tp2var, selectorName + "_chain");

  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto equality = Formulas::equality(
      chain(selectorName, ovar, tp1var, len, sortName),
      chain(selectorName, ovar, tp2var, len, sortName)
    );

  auto equality2 = Formulas::equivalence(
      inChainSupport(selectorName,  tp1var, o3var, ovar, len),
      inChainSupport(selectorName, tp2var, o3var, ovar, len)
    );

  conjuncts.push_back(equality);
  conjuncts.push_back(Formulas::universal({o3sym}, equality2));

  auto conj = Formulas::conjunctionSimp(conjuncts);
  conj = Formulas::universal({osym, lsym}, conj);

  auto def = Formulas::universal({tpVarSym1,tpVarSym2},
    Formulas::equivalenceSimp(samePred, conj));
  return std::make_shared<logic::SpecAxiom>(
    def, "Definition of chain staying the same across time points ",
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
    std::shared_ptr<const Term> timePoint,
    std::string sortName) {
  
  auto sort = Sorts::fetch(sortName);
  std::string suffix = "";
  if(sortName != "Int"){
    suffix = "_" + toLower(sortName);
  }

  return Terms::func("malloc" + suffix , {timePoint}, sort, false, 
    logic::Symbol::SymbolType::MallocFunc);
}

// Set based reasoning
  
std::shared_ptr<const FuncTerm> Theory::emptySet() {
  return Terms::func("empty", {}, Sorts::intSetSort(), false);
} 

std::shared_ptr<const FuncTerm> Theory::setUnion(
  std::shared_ptr<const Term> s1,
  std::shared_ptr<const Term> s2) {

  return Terms::func("union", {s1, s2}, Sorts::intSetSort(), false);
} 

std::shared_ptr<const FuncTerm> Theory::singleton(
  std::shared_ptr<const Term> elem) {
  return Terms::func("singleton", {elem}, Sorts::intSetSort(), false);
}

std::shared_ptr<const Formula> Theory::in(
  std::shared_ptr<const Term> elem,
  std::shared_ptr<const Term> set) {
  return Formulas::predicate("in", {elem, set});
}

std::tuple<std::shared_ptr<logic::Conjecture>,
           std::shared_ptr<logic::Conjecture>,
           std::shared_ptr<logic::Axiom>>
inductionAxiom0(
    std::string concName,
    std::function<std::shared_ptr<const Formula>(std::shared_ptr<const Term>)>
        inductionHypothesis,
    std::shared_ptr<const Term> nlTerm,        
    std::vector<std::shared_ptr<const Symbol>> freeVarSymbols) {

  auto itSymbol = logic::Signature::varSymbol("it", logic::Sorts::iterSort());
  auto it = Terms::var(itSymbol);

  auto zero = Theory::zero();
  auto zeroLessEqIt = Theory::lessEq(zero, it);
  auto itLessNlTerm = Theory::less(it, nlTerm);
  auto itLessEqNlTerm = Theory::lessEq(it, nlTerm);
  auto itPlusOne = Theory::succ(it);

  auto baseCase = Formulas::universal(freeVarSymbols, inductionHypothesis(zero));

  freeVarSymbols.push_back(itSymbol);
  auto stepCase = Formulas::universal(freeVarSymbols, 
    Formulas::implication(
      Formulas::conjunction({zeroLessEqIt,itLessNlTerm, inductionHypothesis(it)}),
      inductionHypothesis(itPlusOne)
    ));
  
  auto conclusion = Formulas::universal(freeVarSymbols, 
    Formulas::implication(
      Formulas::conjunction({zeroLessEqIt,itLessEqNlTerm}),
      inductionHypothesis(it)
    ));

  return std::make_tuple(
      std::make_shared<logic::Conjecture>(baseCase),
      std::make_shared<logic::Conjecture>(stepCase),
      std::make_shared<logic::Axiom>(conclusion, concName));
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
      logic::Signature::varSymbol("boundL", logic::Sorts::iterSort());
  auto boundRSymbol =
      logic::Signature::varSymbol("boundR", logic::Sorts::iterSort());
  auto itIndSymbol =
      logic::Signature::varSymbol("itInd", logic::Sorts::iterSort());

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
