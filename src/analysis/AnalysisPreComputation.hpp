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
typedef std::unordered_map<const program::Statement*,
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
      const program::Statement* statement,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);
  static void addEndTimePointForIfElseStatement(
      const program::IfElse* ifElse,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);
  static void addEndTimePointForWhileStatement(
      const program::WhileStatement* whileStatement,
      const std::shared_ptr<const logic::Term> nextTimepoint,
      EndTimePointMap& endTimePointMap);
  static const program::Statement*
    getNextProperStatement(
      std::vector<std::shared_ptr<const program::Statement>> statements,
      unsigned currPos);

 public:
  /*
   * collect all variables which are assigned as part of statement 'statement'
   */
  static std::unordered_set<std::shared_ptr<const program::Variable>>
  computeAssignedVars(const program::Statement* statement,
                      bool pointerVars = false);

  /*
   * collect all variables which are contained in the loop condition 'expr'
   */
  static void computeVariablesContainedInLoopCondition(
      std::shared_ptr<const program::BoolExpression> expr,
      std::unordered_set<std::shared_ptr<const program::Variable>>& variables);
  static void computeVariablesContainedInLoopCondition(
      std::shared_ptr<const program::Expression> expr,
      std::unordered_set<std::shared_ptr<const program::Variable>>& variables);
};
}  // namespace analysis
#endif
