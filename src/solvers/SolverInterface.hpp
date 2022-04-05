#ifndef __SolverInterface__
#define __SolverInterface__

#include "LogicProblem.hpp"
#include "Solver.hpp"

using namespace logic;

namespace solvers {

template <class SolverExpression, class SolverSort>
class GenSolver {
  public:
    GenSolver(ReasoningTask task) : _task(task) {}

    void convertTask(){
      for(auto& axiom : _task.axioms){
        // We treat all user defined items equivalently
        // and do not differentiate between lemmas, axioms etc.
        // All are treated as axioms. Therefore, users must take
        // care to avoid introducing unsoundness
        solverAssert(convertForm(axiom->formula));
      }
      addConjecture(convertForm(_task.conjecture->formula));
    }

    // formula conversion functions
    // to be overriden by concrete solvers
    virtual SolverExpression solverFalse() const = 0;
    virtual SolverExpression solverTrue() const = 0;
    virtual SolverExpression solverEquiv(SolverExpression f1, SolverExpression f2) const = 0;
    virtual SolverExpression solverImp(SolverExpression f1, SolverExpression f2) const = 0;
      virtual SolverExpression solverUni(std::vector<std::shared_ptr<const Symbol>> vars, 
      SolverExpression f) const = 0;
    virtual SolverExpression solverExi(std::vector<std::shared_ptr<const Symbol>> vars, 
      SolverExpression f) const = 0;
    virtual SolverExpression solverNeg(SolverExpression f) const = 0;
    virtual SolverExpression solverDisj(std::vector<SolverExpression> disjuncts) const = 0;
    virtual SolverExpression solverConj(std::vector<SolverExpression> conjuncts) const = 0;
    virtual SolverExpression solverEq(SolverExpression l, SolverExpression r, bool pol) const = 0;
    // can be used for terms and formulas
    virtual SolverExpression solverApp(std::shared_ptr<const Symbol> sym,
                                       std::vector<SolverExpression> args) const = 0;
    virtual SolverExpression solverGt(SolverExpression s1, SolverExpression s2) const = 0;
    virtual SolverExpression solverGte(SolverExpression s1, SolverExpression s2) const = 0;
    virtual SolverExpression solverLt(SolverExpression s1, SolverExpression s2) const = 0;
    virtual SolverExpression solverLte(SolverExpression s1, SolverExpression s2) const = 0;

    // term conversion functions
    // to be overriden by concrete solvers
    virtual SolverExpression solverPlus(SolverExpression s1, SolverExpression s2) const = 0;
    virtual SolverExpression solverMin(SolverExpression s1, SolverExpression s2) const = 0;
    virtual SolverExpression solverVar(std::shared_ptr<const Term> t) const = 0;


    // sort conversion function
    // to be overriden by concrete solvers
    virtual SolverSort convertSort(const Sort* s) const = 0;

    SolverExpression convertTerm(std::shared_ptr<const Term> t){    

      if(t->type() == Term::Type::Variable){
        return solverVar(t);
      }
     
      auto ft = std::static_pointer_cast<const FuncTerm>(t);

      // see Note below regarding Rapid and 
      // interpreted symbols
      if(ft->symbol->name == "+"){
        assert(ft->subterms.size() == 2);
        return solverPlus(convertTerm(ft->subterms[0]), 
                          convertTerm(ft->subterms[1]));
      }

      if(t->symbol->name == "-"){
        return solverMin(convertTerm(ft->subterms[0]), 
                          convertTerm(ft->subterms[1]));
      }

      std::vector<SolverExpression> args;
      for(auto term : ft->subterms){
        args.push_back(convertTerm(term));
      }    
      return solverApp(ft->symbol, args);
    }

    SolverExpression convertForm(std::shared_ptr<const Formula> f){
      switch(f->type()){
        case Formula::Type::Predicate : {
          auto castedF = std::static_pointer_cast<const PredicateFormula>(f);
       
          // Rapid is a bit wierd in its treatment of interpreted
          // symbols. There is nothing special about them, hence code
          // below. TODO change if time allows
          if(castedF->symbol->name == ">"){
            assert(castedF->subterms.size() == 2);
            return solverGt(convertTerm(castedF->subterms[0]), 
                            convertTerm(castedF->subterms[1]));
          }  

          if(castedF->symbol->name == ">="){
            assert(castedF->subterms.size() == 2);
            return solverGte(convertTerm(castedF->subterms[0]), 
                             convertTerm(castedF->subterms[1]));
          } 

          if(castedF->symbol->name == "<"){
            assert(castedF->subterms.size() == 2);
            return solverLt(convertTerm(castedF->subterms[0]), 
                            convertTerm(castedF->subterms[1]));
          } 

          if(castedF->symbol->name == "<="){
            assert(castedF->subterms.size() == 2);
            return solverLte(convertTerm(castedF->subterms[0]), 
                             convertTerm(castedF->subterms[1]));
          } 

          std::vector<SolverExpression> args;
          for(auto term : castedF->subterms){
            args.push_back(convertTerm(term));
          }          
          return solverApp(castedF->symbol, args);
        }

        case Formula::Type::Equality : {
          auto castedF = std::static_pointer_cast<const EqualityFormula>(f);
          return solverEq(convertTerm(castedF->left), 
                          convertTerm(castedF->right), castedF->polarity);
        }

        case Formula::Type::Conjunction : {
          auto castedF = std::static_pointer_cast<const ConjunctionFormula>(f);
          std::vector<SolverExpression> conjuncts;
          for(auto form : castedF->conj){
            conjuncts.push_back(convertForm(form));
          }
          return solverConj(conjuncts);
        }            
    
        case Formula::Type::Disjunction : {
          auto castedF = std::static_pointer_cast<const DisjunctionFormula>(f);
          std::vector<SolverExpression> disjuncts;
          for(auto form : castedF->disj){
            disjuncts.push_back(convertForm(form));
          }
          return solverDisj(disjuncts);
        }        

        case Formula::Type::Negation : {
          auto castedF = std::static_pointer_cast<const NegationFormula>(f);
          return solverNeg(convertForm(castedF->f));
        }        

        case Formula::Type::Existential : {
          auto castedF = std::static_pointer_cast<const ExistentialFormula>(f);
          return solverExi(castedF->vars, convertForm(castedF->f));
        }     

        case Formula::Type::Universal : {
          auto castedF = std::static_pointer_cast<const UniversalFormula>(f);
          return solverUni(castedF->vars, convertForm(castedF->f));
        }     

        case Formula::Type::Implication : {
          auto castedF = std::static_pointer_cast<const ImplicationFormula>(f);
          return solverImp(convertForm(castedF->f1), convertForm(castedF->f2));
        }     

        case Formula::Type::Equivalence : {
          auto castedF = std::static_pointer_cast<const EquivalenceFormula>(f);
          return solverEquiv(convertForm(castedF->f1), convertForm(castedF->f2));
        }    

        case Formula::Type::True : {
          return solverTrue();
        }  

        case Formula::Type::False : {
          return solverFalse();
        } 
        default:
          assert(false);
      }
    } 

    // Assumes that ATP API has a way to take a strategy as a string.
    // True for Vampire, may not be true for other ATPs.
    virtual void setStrategy(std::string strat) const {};
    virtual void setTimeLimit(int t = 30) const = 0;
    virtual void solverAssert(SolverExpression) const = 0;
    virtual void addConjecture(SolverExpression) const = 0;

    virtual bool solve() = 0;

  private:
    ReasoningTask _task;
  };

// If there are other theorem provers that can handle quantifiers and
// have a programmatic API, can add them here

class VampireSolver : public GenSolver<Vampire::Expression, Vampire::Sort>
{
public: 
  VampireSolver(ReasoningTask task);

  typedef Vampire::Expression VExpr;

  VExpr solverPlus(VExpr v1, VExpr v2) const override;
  VExpr solverMin(VExpr v1, VExpr v2) const override;
  VExpr solverVar(std::shared_ptr<const Term> t) const override;

  Vampire::Sort convertSort(const Sort* s) const override;

  VExpr solverGt(VExpr s1, VExpr s2) const override;
  VExpr solverGte(VExpr s1, VExpr s2) const override;
  VExpr solverLt(VExpr s1, VExpr s2) const override;
  VExpr solverLte(VExpr s1, VExpr s2) const override;

  VExpr solverApp(std::shared_ptr<const Symbol> sym,
                  std::vector<VExpr> args) const override;

  VExpr solverNeg(VExpr f) const override;
  VExpr solverDisj(std::vector<VExpr> disjuncts) const override; 
  VExpr solverConj(std::vector<VExpr> conjuncts) const override;
  VExpr solverEq(VExpr l, VExpr r, bool pol) const override;

  VExpr solverExi(std::vector<std::shared_ptr<const Symbol>> vars, 
                  VExpr v) const override;
  VExpr solverUni(std::vector<std::shared_ptr<const Symbol>> vars, 
                  VExpr v) const override;
  VExpr solverImp(VExpr v1, VExpr v2) const override;
  VExpr solverEquiv(VExpr v1, VExpr v2) const override;
  VExpr solverFalse() const override;
  VExpr solverTrue() const override;

  void outputProblem(std::string fileName = "") const {
    _solver->outputProblem(fileName);
  }
  void setStrategy(std::string strat) const override;
  void setTimeLimit(int t = 30) const override;
  void solverAssert(VExpr) const override;
  void addConjecture(VExpr) const override;

  bool solve() override;

private:
  Vampire::Solver* _solver;
};

}  // namespace solvers

#endif  // __SolverInterface__
