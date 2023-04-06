#ifndef __AssertAssumeProcessor__
#define __AssertAssumeProcessor__

#include <memory>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "AnalysisPreComputation.hpp"
#include "Formula.hpp"
#include "LogicProblem.hpp"
#include "Program.hpp"
#include "SemanticsHelper.hpp"
#include "SemanticsInliner.hpp"
#include "Statements.hpp"
#include "InvariantGenerator.hpp"

#include "Output.hpp"

namespace analysis {

class AssertAssumeProcessor {
 public:
   

  AssertAssumeProcessor(
      const program::Program& program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems,
      unsigned numberOfTraces)
      : program(program),
        endTimePointMap(
            AnalysisPreComputation::computeEndTimePointMap(program)),
        locationToActiveVars(locationToActiveVars),
        problemItems(problemItems),
        numberOfTraces(numberOfTraces){}

  ~AssertAssumeProcessor(){}  


  void process();


 private:

  const program::Program& program;
  const EndTimePointMap endTimePointMap;
  const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      locationToActiveVars;
  std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems;
  const unsigned numberOfTraces;


  void process(
      const program::Statement* statement,
      std::shared_ptr<const logic::Term> trace,
      // conjunction of the conditions (coming from if statements)
      // required to reach this statement
      std::shared_ptr<const logic::Formula> condition);
  void process(
      const program::IfElse* ifElse,
      std::shared_ptr<const logic::Term> trace,
      std::shared_ptr<const logic::Formula> condition);
  void process(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Term> trace,
      std::shared_ptr<const logic::Formula> condition);
};
}  // namespace analysis
#endif