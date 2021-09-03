#ifndef __AnalysisPreComputation__
#define __AnalysisPreComputation__

#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "Formula.hpp"
#include "Program.hpp"
#include "Statements.hpp"
#include "Term.hpp"
#include "Variable.hpp"

namespace analysis {
typedef std::unordered_map<program::Statement*,
                           std::shared_ptr<const logic::Term>>
    EndTimePointMap;

class AnalysisPreComputation {
 public:
  /*
   * for each statement, the end-timePoint is a term refering to the first
   * location after the statement
   */
  static EndTimePointMap computeEndTimePointMap(
      const program::Program& program);

 private:
  static void addEndTimePointForStatement(
      program::Statement* statement,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);
  static void addEndTimePointForIfElseStatement(
      program::IfElseStatement* ifElse,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);
  static void addEndTimePointForWhileStatement(
      program::WhileStatement* whileStatement,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);

 public:
  /*
   * collect all variables which are assigned as part of statement 'statement'
   */
  static std::unordered_set<std::shared_ptr<program::Variable>>
  computeAssignedVars(program::Statement* statement);

  /*
   * collect all variables which are contained in the loop condition 'expr'
   */
  static void computeVariablesContainedInLoopCondition(
      std::shared_ptr<program::Expression> expr,
      std::unordered_set<std::shared_ptr<program::Variable>>& variables);
};
}  // namespace analysis
#endif
