#ifndef __Semantics__
#define __Semantics__

#include <memory>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "AnalysisPreComputation.hpp"
#include "Formula.hpp"
#include "Problem.hpp"
#include "Program.hpp"
#include "SemanticsHelper.hpp"
#include "SemanticsInliner.hpp"
#include "Statements.hpp"

namespace analysis {

class Semantics {
 public:
  Semantics(
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
        numberOfTraces(numberOfTraces),
        inlinedVariableValues(traceTerms(numberOfTraces)) {
    bool containsPointerVariable = false;
    for (auto vars : locationToActiveVars) {
      for (auto v : vars.second) {
        if (v->isPointer()) {
          containsPointerVariable = true;
          break;
        }
      }
    }

    if (util::Configuration::instance().inlineSemantics() &&
        containsPointerVariable) {
      std::cout << "Ignoring request to inline semantics as inlining is "
                   "currently not sound in the presence of ponter variables"
                << std::endl;
      util::Configuration::instance().setDontInline();
    }
  }
  std::pair<std::vector<std::shared_ptr<const logic::Axiom>>,
            InlinedVariableValues>
  generateSemantics();
  std::vector<std::shared_ptr<const logic::Axiom>> generateBounds();


 private:

  const program::Program& program;
  const EndTimePointMap endTimePointMap;
  const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      locationToActiveVars;
  std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems;
  const unsigned numberOfTraces;
  InlinedVariableValues inlinedVariableValues;

  // stores variables that are used in the left side of assignments, i.e.
  // symbols that need to be colored and targeted for symbol elimination
  std::unordered_map<std::string, std::shared_ptr<const program::Variable>>
      coloredSymbols;
  // used to track start timepoints of all loops to find the first relevant
  // timepoint for target symbols
  std::vector<std::shared_ptr<const logic::Term>> loopStartTimePoints;
  // used to track start timepoints of all loops to find the last relevant
  // timepoint for target symbols
  // TODO, I dont think these arrays are necessary 
  std::vector<std::shared_ptr<const logic::Term>> loopEndTimePoints;

  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::Statement* statement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::VarDecl* varDecl, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::Assignment* assignment, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::IfElse* ifElse, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::WhileStatement* whileStatement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::SkipStatement* skipStatement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
};
}  // namespace analysis
#endif