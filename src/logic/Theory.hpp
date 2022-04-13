#ifndef __Theory__
#define __Theory__

#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <vector>

#include "Formula.hpp"
#include "LogicProblem.hpp"
#include "Term.hpp"

namespace logic {

class Theory {
 public:
  static void declareTheories();
  // TODO move memory management to its own file?
  static void declareMemoryArrays();

  static std::shared_ptr<const FuncTerm> intConstant(int i);
  static std::shared_ptr<const FuncTerm> intZero();
  static std::shared_ptr<const FuncTerm> intAddition(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2);
  static std::shared_ptr<const FuncTerm> intSubtraction(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2);
  static std::shared_ptr<const FuncTerm> intModulo(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2);
  static std::shared_ptr<const FuncTerm> intMultiplication(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2);
  static std::shared_ptr<const FuncTerm> intAbsolute(
      std::shared_ptr<const Term> t);
  static std::shared_ptr<const FuncTerm> toInt(std::shared_ptr<const Term> t);
  static std::shared_ptr<const FuncTerm> intSucc(std::shared_ptr<const Term> t);

  static std::shared_ptr<const Formula> intLess(std::shared_ptr<const Term> t1,
                                                std::shared_ptr<const Term> t2,
                                                std::string label = "");
  static std::shared_ptr<const Formula> intLessEqual(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
      std::string label = "");
  static std::shared_ptr<const Formula> intGreater(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
      std::string label = "");
  static std::shared_ptr<const Formula> intGreaterEqual(
      std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2,
      std::string label = "");

  static std::shared_ptr<const Formula> boolTrue(std::string label = "");
  static std::shared_ptr<const Formula> boolFalse(std::string label = "");

  static std::shared_ptr<const FuncTerm> natZero();
  static std::shared_ptr<const FuncTerm> natSucc(
      std::shared_ptr<const Term> term);
  static std::shared_ptr<const FuncTerm> natPre(
      std::shared_ptr<const Term> term);
  static std::shared_ptr<const Formula> natSub(std::shared_ptr<const Term> t1,
                                               std::shared_ptr<const Term> t2,
                                               std::string label = "");
  static std::shared_ptr<const Formula> natSubEq(std::shared_ptr<const Term> t1,
                                                 std::shared_ptr<const Term> t2,
                                                 std::string label = "");

  // Memory management
  static std::shared_ptr<const FuncTerm> nullLoc(
    std::string sortName = "Int");
  static std::shared_ptr<const FuncTerm> arbitraryTP();
  static std::shared_ptr<const FuncTerm> valueAt(
      std::shared_ptr<const Term> timePoint,
      std::shared_ptr<const Term> location,
      std::string sortName = "Int",
      bool isConst = false);  
  static std::shared_ptr<const FuncTerm> selectorAt(
      std::string selectorName,
      std::shared_ptr<const Term> timePoint,
      std::shared_ptr<const Term> object);
  static std::shared_ptr<const FuncTerm> chain(
      std::string selectorName, 
      std::shared_ptr<const Term> timePoint,
      std::shared_ptr<const Term> location,
      std::shared_ptr<const Term> length,      
      std::string sortName);
  static std::pair<std::shared_ptr<logic::Axiom>,
                   std::shared_ptr<logic::Axiom>>
  chainAxioms(
      std::string selectorName,      
      std::string sortName);

  static std::shared_ptr<const FuncTerm> mallocFun(
      std::shared_ptr<const Term> timePoint,
      std::string sortName = "Int");

  static std::shared_ptr<const Formula> isList(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> tp); 
  static std::shared_ptr<const FuncTerm> listLocs(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> tp);
  static std::shared_ptr<const Formula> listLocsPred(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> tp,
      std::shared_ptr<const Term> loc3      
    );
  static std::shared_ptr<const Formula> isAcyclicList(
      std::shared_ptr<const Term> loc,
      std::shared_ptr<const Term> tp); 
  static std::shared_ptr<const FuncTerm> acyclicListLocs(
      std::shared_ptr<const Term> loc,
      std::shared_ptr<const Term> tp);  
  static std::shared_ptr<const Formula>  acyclicListLocsPred(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> tp,
      std::shared_ptr<const Term> loc2);  

  static std::shared_ptr<const Formula> heapLoc(
      std::shared_ptr<const Term> location); 
  static std::shared_ptr<const Formula> framePred(
      std::shared_ptr<const Term> location,
      std::shared_ptr<const Term> t1,
      std::shared_ptr<const Term> t2,
      std::string suffix = "");
  static std::shared_ptr<logic::Axiom> untypedFrameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::shared_ptr<const logic::Symbol> memLocVarSym);
  static std::shared_ptr<logic::Axiom> typedFrameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::shared_ptr<const logic::Symbol> memLocVarSym);
  static std::shared_ptr<logic::Axiom> frameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::string sortName,
      std::string selectorName);

  static std::shared_ptr<const Formula> allSame(
      std::shared_ptr<const Term> tp1,
      std::shared_ptr<const Term> tp2,
      std::string prefix); 

  static std::shared_ptr<logic::Axiom> allSameAxiom(
      std::shared_ptr<const logic::Symbol> tpVarSym1,
      std::shared_ptr<const logic::Symbol> tpVarSym2,
      std::string prefix); 

  //predicate that holds when two memory regions are 
  //disjoint 
  static std::shared_ptr<const Formula> disjoint1(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> size1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> size2);       
  //predicate that holds when a memory region and 
  //a variable (memory region of size 1, are disjoint)
  static std::shared_ptr<const Formula> disjoint2(
      std::shared_ptr<const Term> loc1,
      std::shared_ptr<const Term> loc2,
      std::shared_ptr<const Term> size);       

  static std::shared_ptr<logic::Axiom> disjoint1Axiom(
      std::shared_ptr<const logic::Symbol> memLocVarSym1,
      std::shared_ptr<const logic::Symbol> sizeSym1,      
      std::shared_ptr<const logic::Symbol> memLocVarSym2,
      std::shared_ptr<const logic::Symbol> sizeSym2);
  static std::shared_ptr<logic::Axiom> disjoint2Axiom(
      std::shared_ptr<const logic::Symbol> memLocVarSym1,
      std::shared_ptr<const logic::Symbol> memLocVarSym2,
      std::shared_ptr<const logic::Symbol> sizeSym);


  // Set based reasoning
  
  static std::shared_ptr<const FuncTerm> emptySet(); 
  static std::shared_ptr<const FuncTerm> setUnion(
      std::shared_ptr<const Term> s1,
      std::shared_ptr<const Term> s2); 
  static std::shared_ptr<const FuncTerm> singleton(
      std::shared_ptr<const Term> elem); 
  static std::shared_ptr<const Formula> in(
      std::shared_ptr<const Term> elem,
      std::shared_ptr<const Term> set);

  static std::shared_ptr<const FuncTerm> zero();
  static std::shared_ptr<const FuncTerm> succ(std::shared_ptr<const Term> t);
  static std::shared_ptr<const Formula> less(std::shared_ptr<const Term> t1,
                                             std::shared_ptr<const Term> t2,
                                             std::string label = "");
  static std::shared_ptr<const Formula> lessEq(std::shared_ptr<const Term> t1,
                                               std::shared_ptr<const Term> t2,
                                               std::string label = "");
};

/*
 * Generates inductionAxiom0 from the induction hypothesis 'inductionHypothesis'
 * (short IH, modelled as function which maps each timepoint to a formula),
 * 'freeVarSymbols' must contain exactly all free variables
 * of 'inductionHypothesis' different from the free variable over which we
 * perform induction. The
 * induction axiom then has the following form: forall boundL,boundR.
 *    =>
 *       and
 *          BC(0)
 *          IC(0, nl)
 *       Con(0, nl),
 * where:
 * - the base case BC(0) is defined as
 *   IH(0)
 * - the inductive case IC(0,nl) is defined as
 *   forall it.
 *      =>
 *         and
 *            0<=it<nl
 *            IH(it)
 *         IH(it + 1)
 * - the conclusion Con(0,nl) is defined as
 *   forall it.
 *      =>
 *         0<=it<=nl
 *         IH(it)
 */
std::tuple<std::shared_ptr<logic::Conjecture>,
           std::shared_ptr<logic::Conjecture>,
           std::shared_ptr<logic::Axiom>>
inductionAxiom0(
    std::string concName,
    std::function<std::shared_ptr<const Formula>(std::shared_ptr<const Term>)>
        inductionHypothesis,
    std::shared_ptr<const Term> nlTerm,    
    std::vector<std::shared_ptr<const Symbol>> freeVarSymbols);

/*
 * Generates inductionAxiom1 from the induction hypothesis 'inductionHypothesis'
 * (short IH, modelled as function which maps each timepoint to a formula), and
 * adds it to 'items'. 'freeVarSymbols' must contain exactly all free variables
 * of 'inductionHypothesis' different from the free variable over which we
 * perform induction. If two invocations of this function differ in
 * 'inductionHypothesis', they also need to differ in the shortName. The
 * induction axiom then has the following form: forall boundL,boundR.
 *    =>
 *       and
 *          BC(boundL)
 *          IC(boundL, boundR)
 *       Con(boundL, boundR),
 * where:
 * - the base case BC(boundL) is defined as
 *   IH(boundL)
 * - the inductive case IC(boundL,boundR) is defined as
 *   forall it.
 *      =>
 *         and
 *            boundL<=it<boundR
 *            IH(it)
 *         IH(s(it))
 * - the conclusion Con(boundL,boundR) is defined as
 *   forall it.
 *      =>
 *         boundL<=it<=boundR
 *         IH(it)
 */
std::tuple<std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>,
           std::shared_ptr<logic::Definition>, std::shared_ptr<logic::Axiom>>
inductionAxiom1(
    std::string name, std::string shortName,
    std::function<std::shared_ptr<const Formula>(std::shared_ptr<const Term>)>
        inductionHypothesis,
    std::vector<std::shared_ptr<const Symbol>> freeVarSymbols,
    ProblemItem::Visibility visibility = ProblemItem::Visibility::None);

/*
 * Generates inductionAxiom2 from the induction hypothesis 'inductionHypothesis'
 * (short IH, modelled as function which maps each timepoint to a formula). The
 * induction axiom then has the following form:
 * =>
 *    and
 *       BC
 *       IC
 *    Con
 * where:
 * - the base case BC is defined as
 *   IH(0)
 * - the inductive case IC is defined as
 *   forall it.
 *      =>
 *         and
 *            it<n(t1)
 *            it<n(t2)
 *            IH(it)
 *         IH(s(it))
 * - the conclusion Con is defined as
 *   forall it.
 *      =>
 *         and
 *            it<=n(t1)
 *            it<=n(t2)
 *         IH(it)
 *
 * InductionAxiom2 differs from inductionAxiom1 in the base case, the inductive
 * case and in the conclusion. It can be obtained from inductionAxiom1 in the
 * following way:
 *
 * First, instantiate boundL to 0 and boundR to min(n(t1),n(t2)) and simplify
 * using the theory axiom forall it. 0<=it to get:
 * - BC :=
 *   IH(0)
 * - IC :=
 *   forall it.
 *      =>
 *         and
 *            it<min(n(t1),n(t2))
 *            IH(it)
 *         IH(s(it))
 * - Con :=
 *   forall it.
 *      =>
 *         it<=min(n(t1),n(t2))
 *         IH(it)
 *
 * Then eliminate min from both the inductive case and the conclusion by
 * rewriting it using the following two defining axioms: Axiom1: forall
 * it,it1,it2.
 *    <=>
 *       it < min(it1,it2)
 *       and
 *          it < it1
 *          it < it2
 * Axiom2:
 * forall it,it1,it2.
 *    <=>
 *       it <= min(it1,it2)
 *       and
 *          it <= it1
 *          it <= it2
 *
 * As result we get inductionAxiom2.
 */
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
    ProblemItem::Visibility visibility = ProblemItem::Visibility::None);
}  // namespace logic

#endif
