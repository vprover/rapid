#ifndef __Semantics__
#define __Semantics__

#include <memory>
#include <string>
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
      const program::Program &program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          locationToActiveVars,
      std::vector<std::shared_ptr<const logic::ProblemItem>> &problemItems,
      unsigned numberOfTraces)
      : program(program),
        endTimePointMap(
            AnalysisPreComputation::computeEndTimePointMap(program)),
        locationToActiveVars(locationToActiveVars),
        problemItems(problemItems),
        numberOfTraces(numberOfTraces),
        inlinedVariableValues(traceTerms(numberOfTraces)) {}

  static void applyTransformations(
      std::vector<std::shared_ptr<program::Function>> &functions,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces);

  std::pair<std::vector<std::shared_ptr<const logic::Axiom>>,
            InlinedVariableValues>
  generateSemantics();

 private:
  const program::Program &program;
  const EndTimePointMap endTimePointMap;
  const std::unordered_map<std::string,
                           std::vector<std::shared_ptr<program::Variable>>>
      locationToActiveVars;
  std::vector<std::shared_ptr<const logic::ProblemItem>> &problemItems;
  const unsigned numberOfTraces;
  InlinedVariableValues inlinedVariableValues;

  // stores variables that are used in the left side of assignments, i.e.
  // symbols that need to be colored and targeted for symbol elimination
  std::unordered_map<std::string, std::shared_ptr<program::Variable>> coloredSymbols;
  // used to track start timepoints of all loops to find the first relevant
  // timepoint for target symbols
  std::vector<std::shared_ptr<const logic::Term>> loopStartTimePoints;
  // used to track start timepoints of all loops to find the last relevant
  // timepoint for target symbols
  std::vector<std::shared_ptr<const logic::Term>> loopEndTimePoints;

  std::shared_ptr<const logic::Term> generateSemantics(
      program::Statement* statement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);

  std::shared_ptr<const logic::Term> generateSemantics(
      program::Assignment *assignment, SemanticsInliner &inliner,
      std::shared_ptr<const logic::Term> trace);

  std::shared_ptr<const logic::Term> generateSemantics(
      program::IfElseStatement *ifElse, SemanticsInliner &inliner,
      std::shared_ptr<const logic::Term> trace);

  std::shared_ptr<const logic::Term> generateSemantics(
      program::WhileStatement *whileStatement, SemanticsInliner &inliner,
      std::shared_ptr<const logic::Term> trace);

  std::shared_ptr<const logic::Term> generateSemantics(
      program::SkipStatement *skipStatement, SemanticsInliner &inliner,
      std::shared_ptr<const logic::Term> trace);
  // TODO: add a notion of main function and function calls
};
}  // namespace analysis
#endif