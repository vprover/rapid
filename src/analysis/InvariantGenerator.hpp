#ifndef __InvariantGenerator__
#define __InvariantGenerator__

#include "Program.hpp"
#include "Formula.hpp"
#include "LogicProblem.hpp"
#include "SolverInterface.hpp"

namespace analysis {

class InvariantTask {
  public:
    enum class Status { SOLVED, FAILED, NOT_ATTEMPTED };

    // TODO we leak memory since we never delete these
    InvariantTask(logic::ReasoningTask* baseCase,
                 logic::ReasoningTask* stepCase,
                 std::vector<std::shared_ptr<const logic::Axiom>> conclusions,
                 std::string loopLocation,
                 TaskType tt = TaskType::OTHER,
                 std::vector<std::shared_ptr<const logic::Axiom>> chainAxioms = {}) :
    _baseCase(baseCase), _stepCase(stepCase),
    _conclusions(conclusions), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _tt(tt), _chainAxioms(chainAxioms) {}

    InvariantTask(logic::ReasoningTask* stepCase,
                 std::vector<std::shared_ptr<const logic::Axiom>> conclusions,
                 std::string loopLocation,
                 TaskType tt = TaskType::OTHER,
                 std::vector<std::shared_ptr<const logic::Axiom>> chainAxioms = {}) :
    _baseCase(nullptr), _stepCase(stepCase),
    _conclusions(conclusions), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _tt(tt), _chainAxioms(chainAxioms) {}

    void setStatus(Status status);
    Status status() const { return _status; }    
    bool containsBaseCase() const { return _baseCase != nullptr; }
    TaskType taskType() const { return _tt; }
    bool isChainyTask() const { return _tt == TaskType::CHAINY; }

    void addAxioms(std::vector<std::shared_ptr<const logic::Axiom>> axms){
      _stepCase->addAxioms(axms);
      if(_baseCase){
        _baseCase->addAxioms(axms);
      }
    }
    std::vector<std::shared_ptr<const logic::Axiom>>
    getChainAxioms() { return  _chainAxioms; }

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
    std::vector<std::shared_ptr<const logic::Axiom>> _chainAxioms;
};

/*
 *  In some cases if we fail to prove an invariant, we want to try alternatives
 *  In other cases, if we prove an invariant, we want to try and prove others
 */
class InvariantTaskList {
  public:

    enum class ListType { SINGLETON, CONTINUE_ON_SUCCESS, CONTINUE_ON_FAILURE };

    InvariantTaskList(ListType lt, InvariantTask main) :
     _lt(lt), _mainTask(main) {}

    void addTask(InvariantTask task){ _fallBackTasks.push_back(task); }

    std::vector<InvariantTask>& fallBackTasks() { return _fallBackTasks; }
    //WARNING, should only be used when _fallBakcs are no longer required
    std::vector<InvariantTask>& allTasks() {
      _fallBackTasks.push_back(_mainTask);
      return _fallBackTasks;
    }

    InvariantTask& mainTask() { return _mainTask;}

    bool continueOnFailure(){ return _lt == ListType::CONTINUE_ON_FAILURE; }
    bool continueOnSuccess(){ return _lt == ListType::CONTINUE_ON_SUCCESS; }

  private:
    ListType _lt;
    InvariantTask _mainTask;
    std::vector<InvariantTask> _fallBackTasks;
};

class InvariantGenerator {
  public:
    InvariantGenerator(bool typed,
            std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars) : 
    _typed(typed), _locationToActiveVars(locationToActiveVars) {
      solvers::VampireSolver::instance().setTimeLimit(10);
    }
 
    void generateInvariants( 
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Formula> semantics);

    std::vector<InvariantTaskList>&
    getPotentialInvariants(){ return _potentialInvariants; }
  
    /*
     * Insert axioms in @param iterms into
     * current tasks. if @param location is set
     * we only insert into invariant tasks over loops
     * at that location
     */
    void insertAxiomsIntoTasks(
      std::vector<std::shared_ptr<const logic::Axiom>> items, 
      std::string location = "");

    void attemptToProveInvariants();

    std::vector<std::shared_ptr<const logic::Axiom>>
    getProvenInvariantsAndAxioms();
  private:

    bool attemptToProveInvariant(InvariantTask& task);
  
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
      std::shared_ptr<const logic::Axiom> semantics);

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
      std::shared_ptr<const logic::Axiom> semantics);

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
      std::shared_ptr<const logic::Axiom> semantics);


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
      std::shared_ptr<const logic::Axiom> semantics);

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
      std::shared_ptr<const logic::Axiom> semantics);

    /*
     * Attempts to prove the density / strong density of a variable / term
     * and if successful adds reevant conclusions
     */
    void generateDenseInvariants(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics);


    std::map<std::string,std::vector<std::shared_ptr<logic::Axiom>>> _chainAxiomsUsed; 
    std::vector<std::shared_ptr<logic::Axiom>> _supportAxioms; 

    const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      _locationToActiveVars;

    std::vector<InvariantTaskList> _potentialInvariants;
    bool _typed;
};

}  // namespace analysis
#endif
