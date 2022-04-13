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

    // TODO we leak memory since we never delet these
    InvariantTask(logic::ReasoningTask* baseCase,
                 logic::ReasoningTask* stepCase,
                 std::shared_ptr<const logic::Axiom> conclusion,
                 std::string loopLocation,
                 std::vector<std::shared_ptr<const logic::Axiom>> chainAxioms = {}) :
    _baseCase(baseCase), _stepCase(stepCase),
    _conclusion(conclusion), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _chainAxioms(chainAxioms) {}

    InvariantTask(logic::ReasoningTask* stepCase,
                 std::shared_ptr<const logic::Axiom> conclusion,
                 std::string loopLocation,
                 std::vector<std::shared_ptr<const logic::Axiom>> chainAxioms = {}) :
    _baseCase(nullptr), _stepCase(stepCase),
    _conclusion(conclusion), _status(Status::NOT_ATTEMPTED),
    _loopLocation(loopLocation), _chainAxioms(chainAxioms) {}

    void setStatus(Status status);
    Status status() const { return _status; }    
    bool containsBaseCase() const { return _baseCase != nullptr; }
    bool isChainyTask() const { return _chainAxioms.size() > 0; }

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
    std::shared_ptr<const logic::Axiom> conclusion() { return _conclusion; }    
    std::string loopLoc(){ return _loopLocation; }
 
  private:
    Status _status;
    logic::ReasoningTask* _baseCase;
    logic::ReasoningTask* _stepCase;
    std::shared_ptr<const logic::Axiom> _conclusion;
    std::string _loopLocation;
    std::vector<std::shared_ptr<const logic::Axiom>> _chainAxioms;
};

class InvariantGenerator {
  public:
    InvariantGenerator(bool typed,
            std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars) : 
    _typed(typed), _locationToActiveVars(locationToActiveVars) {
      _solver.setTimeLimit();
    }
 
    void generateInvariants( 
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Formula> loopSemantics);

    std::vector<std::vector<InvariantTask>>&
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
    getProvenInvariantsAndChainAxioms();
  private:
  
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
      std::shared_ptr<const logic::Axiom> loopSemantics);

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
      std::shared_ptr<const logic::Axiom> loopSemantics);

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
      std::shared_ptr<const logic::Axiom> loopSemantics);

    std::map<std::string,std::vector<std::shared_ptr<logic::Axiom>>> _chainAxiomsUsed; 

    const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      _locationToActiveVars;
    std::vector<std::vector<InvariantTask>> _potentialInvariants;
    bool _typed;
    solvers::VampireSolver _solver;
};

}  // namespace analysis
#endif
