#ifndef __PropertiesTime__
#define __PropertiesTime__

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "Expression.hpp"
#include "Formula.hpp"
#include "Problem.hpp"
#include "Program.hpp"
#include "ProgramTraverser.hpp"
#include "SemanticsInliner.hpp"
#include "Sort.hpp"
#include "Term.hpp"
#include "Variable.hpp"

namespace analysis {

std::vector<std::shared_ptr<const logic::ProblemItem>> generateTraceLemmas(
    const program::Program& program,
    std::unordered_map<std::string,
                       std::vector<std::shared_ptr<const program::Variable>>>
        locationToActiveVars,
    unsigned numberOfTraces,
    std::vector<std::shared_ptr<const logic::Axiom>> programSemantics,
    InlinedVariableValues& inlinedVarValues);
}

#endif
