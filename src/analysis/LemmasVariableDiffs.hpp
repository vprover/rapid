#ifndef __LemmasVariableDiffs__
#define __LemmasVariableDiffs__

#include <vector>
#include <memory>
#include <unordered_set>

#include "ProgramTraverser.hpp"
#include "Problem.hpp"
#include "Program.hpp"
#include "SemanticsInliner.hpp"

namespace analysis {

    /**
     * Adds lemmas that link the value of variables before a loop
     * to their value after a loop. For example in the case of the loop
     *  
     *  x = 0
     *  while(cond){
     *    x = x + 1
     *  }
     *
     *  the lemma x(l2(nl2)) = x(l2(zero)) + to-int(nl2)
     *  is added
     */

    class VariableDiffLemmas : public ProgramTraverser<std::vector<std::shared_ptr<const logic::ProblemItem>>>
    {
    public:

        VariableDiffLemmas(const program::Program& program,
                           std::unordered_map<std::string, 
                           std::vector<std::shared_ptr<const program::Variable>>> locationToActiveVars,
                           unsigned numberOfTraces) :
        ProgramTraverser<std::vector<std::shared_ptr<const logic::ProblemItem>>>(program, locationToActiveVars, numberOfTraces)
        {
          addToIntAxs = false;
        }

        inline bool addToIntLemmas() const {
            return addToIntAxs;
        }

        void addToIntAxioms(std::vector<std::shared_ptr<const logic::ProblemItem>>& items);

    private:

        bool addToIntAxs;
        virtual void generateOutputFor(const program::WhileStatement* statement,  std::vector<std::shared_ptr<const logic::ProblemItem>>& items) override;
    };

}

#endif

