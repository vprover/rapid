#ifndef __Semantics__
#define __Semantics__

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "Formula.hpp"
#include "Program.hpp"
#include "Statements.hpp"
#include "Problem.hpp"
#include "AnalysisPreComputation.hpp"
#include "SemanticsInliner.hpp"
#include "SemanticsHelper.hpp"

namespace analysis {

    class Semantics
    {
    public:
        Semantics(const program::Program& program,
                  std::unordered_map<std::string, std::vector<std::shared_ptr<const program::Variable>>> locationToActiveVars,
                  std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems,
                  unsigned numberOfTraces) :
        program(program),
        endTimePointMap(AnalysisPreComputation::computeEndTimePointMap(program)),
        locationToActiveVars(locationToActiveVars),
        problemItems(problemItems),
        numberOfTraces(numberOfTraces),
        inlinedVariableValues(traceTerms(numberOfTraces)) {}
        std::pair<std::vector<std::shared_ptr<const logic::Axiom>>, InlinedVariableValues> generateSemantics();

    private:

        const program::Program& program;
        const EndTimePointMap endTimePointMap;
        const std::unordered_map<std::string, std::vector<std::shared_ptr<const program::Variable>>> locationToActiveVars;
        std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems;
        const unsigned numberOfTraces;
        InlinedVariableValues inlinedVariableValues;

        //stores variables that are used in the left side of assignments, i.e. symbols that need to be colored and targeted for symbol elimination
        std::unordered_map<std::string, std::shared_ptr<const program::Variable>> coloredSymbols;
        //used to track start timepoints of all loops to find the first relevant timepoint for target symbols
        std::vector<std::shared_ptr<const logic::Term>> loopStartTimePoints;
                //used to track start timepoints of all loops to find the last relevant timepoint for target symbols
        std::vector<std::shared_ptr<const logic::Term>> loopEndTimePoints;


        std::shared_ptr<const logic::Formula> generateSemantics(const program::Statement* statement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::IntAssignment* intAssignment, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::IfElse* ifElse, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::WhileStatement* whileStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::SkipStatement* skipStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        // TODO: add break, continue
        // TODO: add a notion of main function and function calls
    };
}
#endif