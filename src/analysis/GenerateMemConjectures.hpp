#ifndef __MemConjectureGenerator__
#define __MemConjectureGenerator__

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

namespace analysis {

class MemConjectureGenerator {
 public:
  MemConjectureGenerator(
      const program::Program& program)
      : program(program),
        endTimePointMap(
            AnalysisPreComputation::computeEndTimePointMap(program))
       {}

  std::vector<std::shared_ptr<const logic::Conjecture>>
  generateMemSafetyConjectures();

 private:

  void createLeftHandsSides(
      std::shared_ptr<const logic::Term> lhs,
      std::vector<std::shared_ptr<const logic::Term>>& lhSides);

  std::vector<std::shared_ptr<const logic::Formula>> memSafetyDisjuncts;
  std::vector<std::shared_ptr<const logic::Formula>> memSafetyConjuncts;

  const program::Program& program;
  const EndTimePointMap endTimePointMap;

  void generateConjectures(
      const program::Statement* statement,
      std::shared_ptr<const logic::Term> trace);
  void generateConjectures(
      const program::Assignment* assignment,
      std::shared_ptr<const logic::Term> trace);
  void generateConjectures(
      const program::IfElse* ifElse, 
      std::shared_ptr<const logic::Term> trace);
  void generateConjectures(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Term> trace);
};
}  // namespace analysis
#endif