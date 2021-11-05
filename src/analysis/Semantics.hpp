#ifndef __Semantics__
#define __Semantics__

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>
#include <set>
#include <tuple>

#include "Formula.hpp"
#include "Program.hpp"
#include "Statements.hpp"
#include "Problem.hpp"
#include "AnalysisPreComputation.hpp"
#include "SemanticsInliner.hpp"
#include "SemanticsHelper.hpp"
#include "../util/Options.hpp"

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
        inlinedVariableValues(traceTerms(numberOfTraces)) {
            bool containsPointerVariable = false;
            for(auto vars : locationToActiveVars){
                for(auto v: vars.second){
                   if(v->isPointer()){
                       containsPointerVariable = true;
                       break;
                   }
                }
            }

            if(util::Configuration::instance().inlineSemantics() && containsPointerVariable){
                std::cout << "Ignoring request to inline semantics as inlining is currently not sound in the presence of ponter variables" << std::endl;
                util::Configuration::instance().setDontInline();
            }
        }
        std::pair<std::vector<std::shared_ptr<const logic::Axiom>>, InlinedVariableValues> generateSemantics();
        std::vector<std::shared_ptr<const logic::Axiom>> generateBounds();

        std::shared_ptr<const logic::Conjecture> getMemorySafetyConj1(){
            auto conj = logic::Formulas::disjunctionSimp(memSafetyDisjuncts);
            return std::make_shared<logic::Conjecture>(conj, "Conjecture stating that there exists an invalid memory access");
        }

        std::shared_ptr<const logic::Conjecture> getMemorySafetyConj2(){
            auto conj = logic::Formulas::conjunctionSimp(memSafetyConjuncts);
            return std::make_shared<logic::Conjecture>(conj, "Conjecture stating that all memory accesses are valid");
        }

    private:
        
        void createLeftHandsSides(std::shared_ptr<const logic::Term> lhs, std::vector<std::shared_ptr<const logic::Term>>& lhSides);

        const program::Program& program;
        const EndTimePointMap endTimePointMap;
        const std::unordered_map<std::string, std::vector<std::shared_ptr<const program::Variable>>> locationToActiveVars;
        std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems;
        const unsigned numberOfTraces;
        InlinedVariableValues inlinedVariableValues;
        std::vector<std::shared_ptr<const logic::Formula>> memSafetyDisjuncts;
        std::vector<std::shared_ptr<const logic::Formula>> memSafetyConjuncts;

        std::shared_ptr<const logic::Formula> generateSemantics(const program::Statement* statement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::VarDecl* varDecl, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);        
        std::shared_ptr<const logic::Formula> generateSemantics(const program::Assignment* intAssignment, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::IfElse* ifElse, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::WhileStatement* whileStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
        std::shared_ptr<const logic::Formula> generateSemantics(const program::SkipStatement* skipStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace);
    };
}
#endif