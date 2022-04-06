#ifndef __InvariantGenerator__
#define __InvariantGenerator__

#include "Program.hpp"
#include "Formula.hpp"
#include "LogicProblem.hpp"

namespace analysis {

class InvariantGenerator {
  public:
    InvariantGenerator(bool typed) : _typed(typed) {}
 
    void generateInvariants( 
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Formula> loopSemantics);

    std::vector<std::vector<logic::ReasoningTask>>&
    getPotentialInvariants(){ return _potentialInvariants; }
  
    void insertAxiomsIntoTasks(std::vector<std::shared_ptr<const logic::Axiom>> items);
    void attemptToProveInvariants();

  private:
    std::vector<std::vector<logic::ReasoningTask>> _potentialInvariants;
    bool _typed;
};

}  // namespace analysis
#endif
