#ifndef __PropertiesTime__
#define __PropertiesTime__

#include <vector>
#include <map>
#include <utility>

#include "Formula.hpp"
#include "Sort.hpp"
#include "Term.hpp"
#include "Expression.hpp"
#include "Variable.hpp"
#include "Program.hpp"

namespace analysis {
    
    class TraceLemmas
    {
    public:
        TraceLemmas(const program::Program& program,
                  const program::ProgramGlobalProperties& maps) :
        program(program),
        iteratorMap(maps.iteratorMap),
        lastIterationMap(maps.lastIterationMap),
        enclosingIteratorsMap(maps.enclosingIteratorsMap),
        locationSymbolMap(maps.locationSymbolMap){}
        
        std::vector<std::shared_ptr<const logic::Formula>> generate();
        
    private:
        const program::Program& program;
        const program::IteratorMap& iteratorMap;
        const program::LastIterationMap& lastIterationMap;
        const program::EnclosingIteratorsMap& enclosingIteratorsMap;
        const program::LocationSymbolMap& locationSymbolMap;
        
        enum class InductionKind { Equal, Less, Greater, LessEqual, GreaterEqual};
        
        void generateStandardInductionLemmas(std::vector<std::shared_ptr<const logic::Formula>>& lemmas);
        void generateStandardInductionLemmas(const program::Statement* statement,
                                             const std::vector<std::shared_ptr<const program::IntVariable>>& intVars,
                                             const std::vector<std::shared_ptr<const program::IntArrayVariable>>& intArrayVars,
                                             std::vector<std::shared_ptr<const logic::Formula>>& lemmas);
        void generateStandardInductionLemmas(const program::WhileStatement* whileStatement,
                                             const std::vector<std::shared_ptr<const program::IntVariable>>& intVars,
                                             const std::vector<std::shared_ptr<const program::IntArrayVariable>>& intArrayVars,
                                             std::vector<std::shared_ptr<const logic::Formula>>& lemmas,
                                             const InductionKind kind);
    };
}

#endif

