#include "TheoryAxioms.hpp"

#include "Options.hpp"
#include "Output.hpp"
#include "SemanticsHelper.hpp"
#include "Signature.hpp"
#include "SymbolDeclarations.hpp"
#include "Theory.hpp"

using namespace logic;

namespace analysis {

#pragma mark - High level methods

std::vector<std::shared_ptr<const logic::Axiom>> TheoryAxioms::generate() {
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;

  if (!util::Configuration::instance().nativeNat() &&
      !util::Configuration::instance().integerIterations()) {
    // add an axiomatization of Sub for natural numbers.
    // NOTE: this axiomatization should be the same as the one added by Vampire
    // internally for Sub, so that fair comparisons can be made.
    addZeroSmallestElementAxiom(axioms);
    addDefineSubEqAxiom(axioms);
    addMonotonicityAxiom(axioms);
    addTransitivityAxioms(axioms);
    addTotalityAxiom(axioms);
    addDisjointnessAxioms(axioms);
  }

  if(util::Configuration::instance().useLists() != "off") {
    if(util::Configuration::instance().useLocSets()){
      addEmptySetAxiom(axioms);
      addSetUnionAxiom(axioms);
      addSingletonAxiom(axioms);
    }
    addListAxioms(axioms);
    if(util::Configuration::instance().useLists() == "acyclic"){
      addAcyclicListAxioms(axioms);
    } else {
      addCyclicListAxioms(axioms);
    }
  }

  return axioms;
}

// forall x. 0 < s(x)
void TheoryAxioms::addZeroSmallestElementAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);

  auto axiom = logic::Formulas::universal(
      {xSym}, logic::Theory::natSub(logic::Theory::natZero(),
                                    logic::Theory::natSucc(x)));

  axioms.push_back(std::make_shared<const logic::Axiom>(
      axiom, "Theory axiom (zero smallest element Nat): forall x. 0 < s(x)"));
}

// forall x,y. x<s(y) <=> (x=y or x<y)
void TheoryAxioms::addDefineSubEqAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto ySym = logic::Signature::varSymbol("yNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);
  auto y = logic::Terms::var(ySym);

  // clause 1: x!<s(y) or x=y or x<y
  auto clause1 = logic::Formulas::universal(
      {xSym, ySym},
      logic::Formulas::disjunction(
          {logic::Formulas::negation(
               logic::Theory::natSub(x, logic::Theory::natSucc(y))),
           logic::Formulas::equality(x, y), logic::Theory::natSub(x, y)}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause1, "Theory axiom (subeq Nat): x!<s(y) or x=y or x<y"));

  // clause 2: x!=y or x<s(y), simplified to x<s(x)
  auto clause2 = logic::Formulas::universal(
      {xSym}, logic::Theory::natSub(x, logic::Theory::natSucc(x)));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause2, "Theory axiom (subeq Nat): x<s(x)"));

  // clause 3: x!<y or x<s(y)
  auto clause3 = logic::Formulas::universal(
      {xSym, ySym}, logic::Formulas::disjunction(
                        {logic::Formulas::negation(logic::Theory::natSub(x, y)),
                         logic::Theory::natSub(x, logic::Theory::natSucc(y))}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause3, "Theory axiom (subeq Nat): x!<y or x<s(y)"));
}

// forall x,y. x<y <=> s(x)<s(y)
void TheoryAxioms::addMonotonicityAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto ySym = logic::Signature::varSymbol("yNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);
  auto y = logic::Terms::var(ySym);
  auto sx = logic::Theory::natSucc(x);
  auto sy = logic::Theory::natSucc(y);

  // clause 1: x!<y or s(x)<s(y)
  auto clause1 = logic::Formulas::universal(
      {xSym, ySym}, logic::Formulas::disjunction(
                        {logic::Formulas::negation(logic::Theory::natSub(x, y)),
                         logic::Theory::natSub(sx, sy)}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause1, "Theory axiom (monotonicity Nat): x!<y or s(x)<s(y)"));

  // clause 2: s(x)!<s(y) or x<y
  auto clause2 = logic::Formulas::universal(
      {xSym, ySym},
      logic::Formulas::disjunction(
          {logic::Formulas::negation(logic::Theory::natSub(sx, sy)),
           logic::Theory::natSub(x, y)}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause2, "Theory axiom (monotonicity Nat): s(x)!<s(y) or x<y"));
}

void TheoryAxioms::addTransitivityAxioms(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto ySym = logic::Signature::varSymbol("yNat", logic::Sorts::natSort());
  auto zSym = logic::Signature::varSymbol("zNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);
  auto y = logic::Terms::var(ySym);
  auto z = logic::Terms::var(zSym);

  auto strict1 = logic::Formulas::negation(logic::Theory::natSub(x, y));
  auto strict2 = logic::Formulas::negation(logic::Theory::natSub(y, z));
  auto nonStrict1 = logic::Formulas::negation(logic::Theory::natSubEq(x, y));
  auto nonStrict2 = logic::Formulas::negation(logic::Theory::natSubEq(y, z));
  auto strict3 = logic::Theory::natSub(x, z);
  auto nonStrict3 = logic::Theory::natSubEq(x, z);

  // variant 1: forall x,y,z. x!<y or y!<z or x<z
  auto clause1 = logic::Formulas::universal(
      {xSym, ySym, zSym},
      logic::Formulas::disjunction({strict1, strict2, strict3}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause1,
      "Theory axiom (transitivity1 Nat): forall x,y,z. x!<y or y!<z or x<z"));

  // variant 2: forall x,y,z. x!<s(y) or y!<z or x<z
  auto clause2 = logic::Formulas::universal(
      {xSym, ySym, zSym},
      logic::Formulas::disjunction({nonStrict1, strict2, strict3}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause2,
      "Theory axiom (transitivity2 Nat): forall x,y,z. x!<s(y) or y!<z or "
      "x<z"));

  // variant 3: forall x,y,z. x!<y or y!<s(z) or x<z
  auto clause3 = logic::Formulas::universal(
      {xSym, ySym, zSym},
      logic::Formulas::disjunction({strict1, nonStrict2, strict3}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause3,
      "Theory axiom (transitivity3 Nat): forall x,y,z. x!<y or y!<s(z) or "
      "x<z"));

  // variant 4: forall x,y,z. x!<s(y) or y!<s(z) or x<s(z)
  auto clause4 = logic::Formulas::universal(
      {xSym, ySym, zSym},
      logic::Formulas::disjunction({nonStrict1, nonStrict2, nonStrict3}));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      clause4,
      "Theory axiom (transitivity4 Nat): forall x,y,z. x!<s(y) or y!<s(z) or "
      "x<s(z)"));
}

void TheoryAxioms::addTotalityAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto ySym = logic::Signature::varSymbol("yNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);
  auto y = logic::Terms::var(ySym);

  // forall x,y. (x<y or x=y or x>y)
  auto axiom = logic::Formulas::universal(
      {xSym, ySym},
      logic::Formulas::disjunction({logic::Theory::natSub(x, y),
                                    logic::Formulas::equality(x, y),
                                    logic::Theory::natSub(y, x)}));

  axioms.push_back(std::make_shared<const logic::Axiom>(
      axiom, "Theory axiom (totality Nat): forall x,y. (x<y or x=y or x>y)"));
}

void TheoryAxioms::addDisjointnessAxioms(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {
  auto xSym = logic::Signature::varSymbol("xNat", logic::Sorts::natSort());
  auto x = logic::Terms::var(xSym);

  // Clause 1: x!<y or x!=y, simplified to x!<x
  auto axiom = logic::Formulas::universal(
      {xSym}, logic::Formulas::negation(logic::Theory::natSub(x, x)));
  axioms.push_back(std::make_shared<const logic::Axiom>(
      axiom, "Theory axiom (disjointness Nat): forall x. x!<x"));

  // NOTE: all other clauses for this axiom are already subsumed by other axioms
}


void TheoryAxioms::addListAxioms(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {

  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto ySym = logic::Signature::varSymbol("y", logic::Sorts::intSort());
  auto zSym = logic::Signature::varSymbol("z", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym);
  auto y = logic::Terms::var(ySym);
  auto z = logic::Terms::var(zSym);
  auto succx = logic::Theory::intAddition(x, logic::Theory::intConstant(1));

  auto tpVarSym = logic::Signature::varSymbol("tp", logic::Sorts::timeSort());
  auto tp = logic::Terms::var(tpVarSym);  

  auto isList1 = logic::Theory::isList(x, y, tp);
  auto isList2 = logic::Theory::isList(z, y, tp);

  auto equalxy = logic::Formulas::equality(x, y);
  auto valueAtSuccx = logic::Theory::valueAt(tp, succx);
  auto equalzValueSuccx = logic::Formulas::equality(z, valueAtSuccx);

  auto xIsHeap = logic::Theory::heapLoc(x);
  auto succxIsHeap = logic::Theory::heapLoc(succx);

  auto conj1 = logic::Formulas::conjunction({isList2, equalzValueSuccx}); 
  auto recursiveCase = logic::Formulas::existential({zSym}, conj1);

  auto conj2 = logic::Formulas::conjunction({xIsHeap, succxIsHeap, recursiveCase});
  auto disj = logic::Formulas::disjunction({equalxy, conj2});

  auto listDef = logic::Formulas::equivalence(isList1, disj);
  listDef = logic::Formulas::universal({xSym, ySym, tpVarSym}, listDef);
  axioms.push_back(std::make_shared<const logic::Axiom>(
      listDef, "Definition of a list")); 

  // axiom defining locations in a list
  auto notList = logic::Formulas::negation(isList1);
  auto disj1 = logic::Formulas::disjunction({notList, equalxy});

  auto notEqualxy = logic::Formulas::negation(equalxy);
  auto conj3 = logic::Formulas::conjunction({isList1, notEqualxy});

  std::shared_ptr<const Formula> imp1, imp2;
  if(util::Configuration::instance().useLocSets()){
    auto listLocsxy = logic::Theory::listLocs(x, y, tp);
    auto listLocsEmpty = logic::Formulas::equality(listLocsxy, logic::Theory::emptySet());
    imp1 = logic::Formulas::implication(disj1, listLocsEmpty);

    auto singletonx = logic::Theory::singleton(x);
    auto singletonSuccx = logic::Theory::singleton(succx);
    auto unionSingletons = logic::Theory::setUnion(singletonx, singletonSuccx);

    auto listLocsTail = logic::Theory::listLocs(valueAtSuccx, y, tp);
    auto allLocs = logic::Theory::setUnion(unionSingletons, listLocsTail);
    auto listLocsDef = logic::Formulas::equality(listLocsxy, allLocs);
    imp2 = logic::Formulas::implication(conj3, listLocsDef);
  } else {
    auto listLocsxyz = logic::Theory::listLocsPred(x, y, tp, z);
    imp1 = logic::Formulas::implication(disj1, 
      logic::Formulas::universal({zSym}, 
        logic::Formulas::negation(listLocsxyz)));

    auto listLocsxyx = logic::Theory::listLocsPred(x, y, tp, x);
    auto listLocsxySuccx = logic::Theory::listLocsPred(x, y, tp, succx);
    auto listLocsTails = logic::Theory::listLocsPred(valueAtSuccx, y, tp, z);
    auto inTailImpInList = logic::Formulas::implication(listLocsTails, listLocsxyz);
    inTailImpInList = logic::Formulas::universal({zSym}, inTailImpInList);
    auto locationsInList = logic::Formulas::conjunction(
      {listLocsxyx, listLocsxySuccx, inTailImpInList});
    imp2 = logic::Formulas::implication(conj3, locationsInList);
  }

  auto conjOfImps = logic::Formulas::conjunction({imp1, imp2});
  auto axiom = logic::Formulas::universal({xSym, ySym, tpVarSym}, conjOfImps);
  axioms.push_back(std::make_shared<const logic::Axiom>(
      axiom, "Definition of locations in a list"));  
}

void TheoryAxioms::addAcyclicListAxioms(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {

  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym);

  auto tpVarSym = logic::Signature::varSymbol("tp", logic::Sorts::timeSort());
  auto tp = logic::Terms::var(tpVarSym); 

  auto isAcyclicList = logic::Theory::isAcyclicList(x, tp);  
  auto nullLoc = logic::Theory::nullLoc();
  auto isList = logic::Theory::isList(x, nullLoc, tp);

  auto def = logic::Formulas::equivalence(isAcyclicList, isList);
  def = logic::Formulas::universal({xSym, tpVarSym}, def);
  axioms.push_back(std::make_shared<const logic::Axiom>(
      def, "Definition of an acyclic list"));

  // axiom defining locations in an acyclic list
  std::shared_ptr<const Formula> def2;  
  if(util::Configuration::instance().useLocSets()){  
    auto acyclicListLocs = logic::Theory::acyclicListLocs(x, tp);
    auto listLocs = logic::Theory::listLocs(x, nullLoc, tp);

    def2 = logic::Formulas::equality(acyclicListLocs, listLocs);
    def2 = logic::Formulas::universal({xSym, tpVarSym}, def2);
  } else {
    auto ySym = logic::Signature::varSymbol("y", logic::Sorts::intSort());
    auto y = logic::Terms::var(ySym);

    auto acyclicListLocs = logic::Theory::acyclicListLocsPred(x, tp, y);
    auto listLocs = logic::Theory::listLocsPred(x, nullLoc, tp, y);
    def2 = logic::Formulas::equivalence(acyclicListLocs, listLocs);
    def2 = logic::Formulas::universal({xSym, ySym, tpVarSym}, def2);
  }
  axioms.push_back(std::make_shared<const logic::Axiom>(
        def2, "Definition of acyclic list locations"));  
}


void TheoryAxioms::addCyclicListAxioms(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms) {

}


void TheoryAxioms::addEmptySetAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms)
{
  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym);

  auto xnotinempty = logic::Formulas::negation(logic::Theory::in(x, logic::Theory::emptySet()));
  xnotinempty = logic::Formulas::universal({xSym}, xnotinempty);
  axioms.push_back(std::make_shared<const logic::Axiom>(
      xnotinempty, "Definition of the empty set")); 
}

void TheoryAxioms::addSetUnionAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms)
{
  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym);

  auto s1Sym = logic::Signature::varSymbol("s1", logic::Sorts::intSetSort());
  auto s1 = logic::Terms::var(s1Sym);

  auto s2Sym = logic::Signature::varSymbol("s2", logic::Sorts::intSetSort());
  auto s2 = logic::Terms::var(s2Sym);

  auto unions1s2 = logic::Theory::setUnion(s1, s2);
  auto xInUnion = logic::Theory::in(x, unions1s2);
  auto xIns1 = logic::Theory::in(x, s1);
  auto xIns2 = logic::Theory::in(x, s2);
  auto disj = logic::Formulas::disjunction({xIns1, xIns2});
  auto def = logic::Formulas::equivalence(xInUnion, disj);
  def = logic::Formulas::universal({xSym, s1Sym, s2Sym}, def);
  axioms.push_back(std::make_shared<const logic::Axiom>(
      def, "Definition of set union"));   
}

void TheoryAxioms::addSingletonAxiom(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms)
{
  auto xSym = logic::Signature::varSymbol("x", logic::Sorts::intSort());
  auto x = logic::Terms::var(xSym);
  
  auto xsingleton = logic::Theory::singleton(x);
  auto def = logic::Theory::in(x, xsingleton);
  def = logic::Formulas::universal({xSym}, def);
  //TODO, do we want to exclude everything != x from the set?
  axioms.push_back(std::make_shared<const logic::Axiom>(
      def, "Definition of a singleton set")); 
}

}  // namespace analysis
