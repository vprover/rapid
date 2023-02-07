#ifndef __SolverInterface__
#define __SolverInterface__

#include "LogicProblem.hpp"
#include "Solver.hpp"

using namespace logic;

namespace solvers {

template <class SolverExpression, class SolverSort>
class GenSolver {
  public:
    GenSolver() {}
    
    using SolverResult = std::pair<bool, std::string>;
  
    void convertTask(ReasoningTask task){
      reset();
      try{

        for(auto& sort : Sorts::structSorts()){
          declareStruct(sort);
        }

        // To ensure same ordering and hence precedence of symbols as in file
        // makes comparisons easier.
        for (const auto& symbol : Signature::signatureOrderedByInsertion()) {

          if(!symbol->noDeclaration)
            declareSymbol(symbol);
        }

        for(auto& axiom : task.axioms){
          // We treat all user defined items equivalently
          // and do not differentiate between lemmas, axioms etc.
          // All are treated as axioms. Therefore, users must take
          // care to avoid introducing unsoundness

          solverAssert(convertForm(axiom->formula));
          solverResetVars();
        }
        addConjecture(convertForm(task.conjecture->formula));
      } catch (Vampire::ApiException& e){
        std::cerr << "Exception: "<<e.msg()<<std::endl;
        abort();
      } catch (Vampire::FormulaBuilderException& f) {
        std::cerr << "Exception: "<<f.msg()<<std::endl;
        abort();
      }
    }

    // solvers can choose how to handle chainy tasks
    // We call a task chainy if it involves proving some facts about
    // a chain of fields e.g. a->f->f->f->f ...
    virtual SolverResult solveTask(ReasoningTask task, TaskType tt = TaskType::OTHER) {
      convertTask(task);
      return solve();
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
    virtual SolverExpression solverIntConst(int i) const = 0;    
    virtual SolverExpression solverVar(std::shared_ptr<const Term> t) const = 0;


    // sort conversion function
    // to be overriden by concrete solvers
    virtual SolverSort convertSort(const Sort* s) const = 0;

    SolverExpression convertTerm(std::shared_ptr<const Term> t){    

      auto isNumber = [](const std::string& str)
      {
        return str.find_first_not_of("0123456789") == std::string::npos;
      };

      if(t->type() == Term::Type::Variable){
        auto var = solverVar(t);
        return var;
      }
     
      auto ft = std::static_pointer_cast<const FuncTerm>(t);

      // see Note below regarding Rapid and 
      // interpreted symbols
      if(ft->symbol->name == "+"){
        assert(ft->subterms.size() == 2);
        auto arg2 = convertTerm(ft->subterms[1]);
        auto arg1 = convertTerm(ft->subterms[0]);
        return solverPlus(arg1,arg2);
      }

      if(t->symbol->name == "-"){
        auto arg2 = convertTerm(ft->subterms[1]);
        auto arg1 = convertTerm(ft->subterms[0]);
        return solverMin(arg1,arg2);
      }

      if(isNumber(t->symbol->name)){
        // Careful, stoi can raise out of bounds exceptions 
        // which we should handle!
        return solverIntConst(std::stoi(t->symbol->name));
      }

      std::vector<SolverExpression> args(ft->subterms.size());
      for(int i = ft->subterms.size() - 1; i >= 0; i--){
        args[i] = convertTerm(ft->subterms[i]);
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
            auto arg2 = convertTerm(castedF->subterms[1]);
            auto arg1 = convertTerm(castedF->subterms[0]);
            return solverGt(arg1,arg2);
          }  

          if(castedF->symbol->name == ">="){
            assert(castedF->subterms.size() == 2);
            auto arg2 = convertTerm(castedF->subterms[1]);
            auto arg1 = convertTerm(castedF->subterms[0]);
            return solverGte(arg1,arg2);
          } 

          if(castedF->symbol->name == "<"){
            assert(castedF->subterms.size() == 2);
            auto arg2 = convertTerm(castedF->subterms[1]);
            auto arg1 = convertTerm(castedF->subterms[0]);
            return solverLt(arg1,arg2);
          } 

          if(castedF->symbol->name == "<="){
            assert(castedF->subterms.size() == 2);
            auto arg2 = convertTerm(castedF->subterms[1]);
            auto arg1 = convertTerm(castedF->subterms[0]);
            return solverLte(arg1,arg2);
          } 

          std::vector<SolverExpression> args(castedF->subterms.size());
          for(int i = castedF->subterms.size() - 1; i >= 0; i--){
            args[i] = convertTerm(castedF->subterms[i]);
          }       
          
          return solverApp(castedF->symbol, args);
        }

        case Formula::Type::Equality : {
          auto castedF = std::static_pointer_cast<const EqualityFormula>(f);
          auto right = convertTerm(castedF->right);          
          auto left = convertTerm(castedF->left);
          return solverEq(left, right, castedF->polarity);
        }

        case Formula::Type::Conjunction : {
          auto castedF = std::static_pointer_cast<const ConjunctionFormula>(f);
          if(castedF->conj.size() == 1){
            return convertForm(castedF->conj[0]);
          }          
          std::vector<SolverExpression> conjuncts(castedF->conj.size());
          for(int i =  castedF->conj.size() - 1; i >=0; i--){
            conjuncts[i] = convertForm(castedF->conj[i]);
          }
          auto res = solverConj(conjuncts);
          return res;
        }            
    
        case Formula::Type::Disjunction : {
          auto castedF = std::static_pointer_cast<const DisjunctionFormula>(f);
          if(castedF->disj.size() == 1){
            return convertForm(castedF->disj[0]);
          }
          std::vector<SolverExpression> disjuncts(castedF->disj.size());
          for(int i =  castedF->disj.size() - 1; i >=0; i--){
            disjuncts[i] = convertForm(castedF->disj[i]);
          }
          return solverDisj(disjuncts);
        }        

        case Formula::Type::Negation : {
          auto castedF = std::static_pointer_cast<const NegationFormula>(f);
          return solverNeg(convertForm(castedF->f));
        }        

        case Formula::Type::Existential : {
          auto castedF = std::static_pointer_cast<const ExistentialFormula>(f);
          solverDeclareVars(castedF->vars);
          auto res = solverExi(castedF->vars, convertForm(castedF->f));
          popVars();
          return res;
        }     

        case Formula::Type::Universal : {
          auto castedF = std::static_pointer_cast<const UniversalFormula>(f);
          solverDeclareVars(castedF->vars);          
          auto res =  solverUni(castedF->vars, convertForm(castedF->f));
          popVars();
          return res;          
        }     

        case Formula::Type::Implication : {
          auto castedF = std::static_pointer_cast<const ImplicationFormula>(f);
          auto f2 = convertForm(castedF->f2);
          auto f1 = convertForm(castedF->f1);
          return solverImp(f1, f2);
        }     

        case Formula::Type::Equivalence : {
          auto castedF = std::static_pointer_cast<const EquivalenceFormula>(f);
          auto f2 = convertForm(castedF->f2);
          auto f1 = convertForm(castedF->f1);
          return solverEquiv(f1, f2);        
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

    virtual void declareSymbol(std::shared_ptr<const Symbol>) const = 0;
    // not = 0, since besides for Vampire no other prover supports structs
    // internally
    virtual void declareStruct(Sort* sort) const {}
    // Assumes that ATP API has a way to take a strategy as a string.
    // True for Vampire, may not be true for other ATPs.
    virtual void setStrategy(std::string strat) const {};
    virtual void setTimeLimit(int t = 30) const = 0;
    virtual void solverAssert(SolverExpression) const = 0;
    virtual void addConjecture(SolverExpression) const = 0;
    virtual void reset() const = 0;
    //HACKS
    virtual void solverResetVars() const = 0;
    virtual void solverDeclareVars(const std::vector<std::shared_ptr<const Symbol>> vars) const = 0;
    virtual void popVars() const = 0;

    virtual SolverResult solve() = 0;
  };

// If there are other theorem provers that can handle quantifiers and
// have a programmatic API, can add them here

class VampireSolver : public GenSolver<Vampire::Expression, Vampire::Sort>
{
public: 
  VampireSolver();

  typedef Vampire::Expression VExpr;

  VExpr solverPlus(VExpr v1, VExpr v2) const override;
  VExpr solverMin(VExpr v1, VExpr v2) const override;
  VExpr solverIntConst(int i) const override;    

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
  void reset() const override {
    _solver->resetHard();
  }
  void solverResetVars() const override {
    _solver->resetVariables();
  }
  void solverDeclareVars(const std::vector<std::shared_ptr<const Symbol>> vars) const override {
    std::vector<std::string> vnames;
    std::vector<Vampire::Sort> vsorts;
    for(auto var : vars){
      vnames.push_back(var->name);
      vsorts.push_back(convertSort(var->rngSort));
    }
    _solver->declareQuantifiedVars(vnames, vsorts);
  }
  void popVars() const override {
    _solver->popQuantVars();
  }

  void declareSymbol(std::shared_ptr<const Symbol> sym) const override;
  void declareStruct(Sort* sort) const override;

  SolverResult solveTask(ReasoningTask task, TaskType tt = TaskType::OTHER) override {
    convertTask(task);

    if(task.getPrint()){
      _solver->setVerbose(true);
      task.outputSMTLIB(std::cout);
    } else {
      _solver->setVerbose(false);      
    }

/*    _solver->setOption("lemma_literal_selection","on");
    _solver->setOption("theory_axioms","off");    
    _solver->setOption("cancellation","cautious");
    _solver->setOption("gaussian_variable_elimination","force");*/
    setTimeLimit(10);

    if(tt == TaskType::MAIN || tt == TaskType::STAY_SAME){
      std::cout << "Running Vampire's Rapid schedule for 60s" << std::endl;      
      setTimeLimit(60);
      //_solver->setVerbose(true);
      //_solver->setOption("show_preprocessing","on");
      return solveWithSched(Vampire::Solver::Schedule::RAPID_MAIN_TASK);
    }

    if(tt == TaskType::CHAINY2 || tt == TaskType::CHAINY3){
      std::cout << "Running Vampire's Rapid schedule for 20s" << std::endl;
      setTimeLimit(20);
      SolverResult res = solveWithSched(Vampire::Solver::Schedule::RAPID_CHAIN_TASK);   

      return res;
    }

    std::cout << "Running Vampire's Rapid schedule for 10s" << std::endl;
    if(tt == TaskType::MALLOC){
      _solver->setOption("unification_with_abstraction","one_side_interp");
      _solver->setOption("theory_axioms","on");    
      SolverResult res = solveWithSched(Vampire::Solver::Schedule::RAPID);
      _solver->setOption("unification_with_abstraction","off");      
      return res;            
//      task.outputSMTLIB(std::cout);
    }


    //assert(false);
    auto res = solveWithSched(Vampire::Solver::Schedule::RAPID);

    if(task.getPrint())
      assert(false); 

    return res;

  }

  // trys to solve the problem using Vampire's CASC mode
  SolverResult solve() override;
  SolverResult solveWithSched(Vampire::Solver::Schedule sched);

  static VampireSolver& instance(){ return _instance; }

private:
  Vampire::Solver* _solver;
  static VampireSolver _instance;
};

}  // namespace solvers

#endif  // __SolverInterface__
