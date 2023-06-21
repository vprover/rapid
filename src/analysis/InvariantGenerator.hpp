#ifndef __InvariantGenerator__
#define __InvariantGenerator__

#include "Program.hpp"
#include "Formula.hpp"
#include "LogicProblem.hpp"
#include "SolverInterface.hpp"
#include "AnalysisPreComputation.hpp"

#include <unordered_set>

namespace analysis {

//TODO make this a super class and create subclasses
class InvariantTask {
  public:
    enum class Status { SOLVED, FAILED, NOT_ATTEMPTED };

    // TODO we leak memory since we never delete these
    InvariantTask(logic::ReasoningTask* baseCase,
                 logic::ReasoningTask* stepCase,
                 std::vector<std::shared_ptr<const logic::Axiom>> conclusions,
                 std::string loopLocation,
                 TaskType tt = TaskType::OTHER) :
    _baseCase(baseCase), _stepCase(stepCase),
    _conclusions(conclusions), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _tt(tt) {}

    InvariantTask(logic::ReasoningTask* stepCase,
                 std::vector<std::shared_ptr<const logic::Axiom>> conclusions,
                 std::string loopLocation,
                 TaskType tt = TaskType::OTHER) :
    _baseCase(nullptr), _stepCase(stepCase),
    _conclusions(conclusions), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _tt(tt) {}

    InvariantTask(std::vector<std::shared_ptr<const logic::Axiom>> conclusions,
                 std::string loopLocation,
                 TaskType tt = TaskType::OTHER) :
    _baseCase(nullptr), _stepCase(nullptr),
    _conclusions(conclusions), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _tt(tt) {}

    void setStatus(Status status);
    Status status() const { return _status; }    
    bool containsBaseCase() const { return _baseCase != nullptr; }
    TaskType taskType() const { return _tt; }

    void addAxioms(std::vector<std::shared_ptr<const logic::Axiom>> axms){
      if(_stepCase){
        _stepCase->addAxioms(axms);
      }
      if(_baseCase){
        _baseCase->addAxioms(axms);
      }
    }

    void removeStandardConclusion();
    void removeVariantConclusion();

    logic::ReasoningTask* baseCase() { return _baseCase; }
    logic::ReasoningTask* stepCase() { return _stepCase; }
    
    std::vector<std::shared_ptr<const logic::Axiom>> 
    conclusions() { return _conclusions; }    
    
    std::string loopLoc(){ return _loopLocation; }

  private:
    Status _status;
    logic::ReasoningTask* _baseCase;
    logic::ReasoningTask* _stepCase;
    // from one base and step case can sometimes derive multiple conclusion 
    // at least for DENSE tasks
     std::vector<std::shared_ptr<const logic::Axiom>> _conclusions;
    std::string _loopLocation;
    TaskType _tt;
};

/*
 *  In some cases if we fail to prove an invariant, we want to try alternatives
 *  In other cases, if we prove an invariant, we want to try and prove others
 */
// TODO, make this a parent class and then create sub-classes for chainy
// etc.
class InvariantTaskList {
  public:

    InvariantTaskList(TaskType tt) :
     _tt(tt) {}

    void addTask(InvariantTask task){ _tasks.push_back(task); }

    std::vector<InvariantTask>& tasks() { return _tasks; }

    TaskType taskType() { return _tt; }

  private:
    TaskType _tt;
    std::vector<InvariantTask> _tasks;
};

class InvariantGenerator {
  public:
    InvariantGenerator(bool typed,
            std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars,
        EndTimePointMap endTimePointMap) : 
    _typed(typed), _locationToActiveVars(locationToActiveVars), _endTimePointMap(endTimePointMap) {
      solvers::VampireSolver::instance().setTimeLimit(10);
    }
 
    void generateStrengthenings( 
      const program::Statement* statement,
      std::shared_ptr<const logic::Formula> conditionsFromAbove,
      std::shared_ptr<const logic::Formula> semantics);

    std::vector<InvariantTaskList>&
    getPotentialStrengthenings(){ return _potentialInvariants; }
  
    /*
     * Insert axioms in @param iterms into
     * current tasks. if @param location is set
     * we only insert into invariant tasks over loops
     * at that location
     */
    void insertAxiomsIntoTasks(
      std::vector<std::shared_ptr<const logic::Axiom>> items, 
      std::string location = "");

    void attemptToProveStrengthenings();

    std::vector<std::shared_ptr<const logic::Axiom>>
    getProvenStrengtheningsAndAxioms();
  private:

    // TODO should const these arguments that we are passing by reference
    bool attemptToProveInvariant(InvariantTask& task);
    bool attemptToProveStrengthening(InvariantTask& task);
  

    /*
     * Given an if statement
     *
     * if(c){ p1 } else { p2 }
     *
     * try and show that some entire class of objects is not affected by the statement
     */
    void generateStaySameFormulas(
      const program::IfElse* ifStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Given an if statement
     *
     * if(c){ p1 } else { p2 }
     *
     * try and show for each variable in scope before the start of the 
     * if statement that it remains unchanged by the statement
     */
    void generateFrameFormulas(
      const program::IfElse* ifStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Generate a reasoning tasks whose conclusions are the following invariant:
     *
     * forall it.
     *   0 <= it /\ it < nl  =>
     *   f (*struc) it = null 
     *
     *  for each pointer field f over the type of *struc
     *  where struc is a pointer to a struc
     */
    void generatePointsToNullInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Generate a reasoning tasks whose conclusions are the following invariant:
     *
     * forall it.
     *   0 <= it /\ it < nl  =>
     *   f (it + 1) (malloc it) = f nl (malloc it)
     *
     *  for each pointer field f over the type of malloc
     */
    void generateMallocInLoopInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Generate reasoning tasks whose conclusions are the following invariant:
     *
     * forall it n.
     *   0 <= it /\ it <= nl  =>
     *   f it n = f nl n
     *
     *  for each field f over the type of malloc
     *  where is a variable ranging over the declared struct sorts
     */
    void generateStructsStaySameInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);


    /*
     * if 
     *  forall it n.
     *    0 <= it < n =>
     *    value_* var it = value_* var (+ it 1)
     *
     * then conclude 
     *    value_* var 0 = value_* var nl#   
     * 
     */
    void generateStaticVarInvariants(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Generate reasoning tasks whose conclusions are the following invariant:
     *
     * forall it n.
     *   0 <= it /\ it < nl  =>
     *   value it var = f_chain var 0 it
     *
     *  where var is a pointer to a struct and
     *  the loop contains a line var = var->f
     *
     *  f_chain is defined recursively with 
     *  f_chain var tp 0 = value tp var
     */
    void generateChainingInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    /*
     * Attempts to prove the density / strong density of a variable / term
     * and if successful adds relevant conclusions
     */
    void generateDenseInvariants(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    void generateEqualMallocFormulas(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics,
      std::shared_ptr<const logic::Formula> conditionsFromAbove);

    const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      _locationToActiveVars;
    const EndTimePointMap _endTimePointMap;

    std::vector<InvariantTaskList> _potentialInvariants;
    std::unordered_set<std::string> _chainsSameProved;
    bool _typed;
};

}  // namespace analysis
#endif
