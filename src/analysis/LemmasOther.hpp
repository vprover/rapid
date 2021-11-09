#ifndef __LemmasOther__
#define __LemmasOther__

#include <memory>
#include <vector>

#include "Problem.hpp"
#include "Program.hpp"
#include "ProgramTraverser.hpp"
#include "SemanticsInliner.hpp"

namespace analysis {

/*
 * We use the lemmas in this header to cover additional (inductive) reasoning
 * which doesn't fit in any particular category.
 */

/*
 * LEMMA 1
 * if the loop condition holds at the first iteration, then there exists an
 * iteration whose successor is the last iteration.
 * TODO:    It would probably improve the lemma if we replace the conclusion
 * with "then n is different from 0" (from which we can also conclude the
 * current conclusion)
 *
 * TODO:    It is unclear why this lemma is useful at all. It doesn't cover any
 * inductive reasoning we couldn't conclude from other axioms. It could be the
 * case that it is useful, since superposition doesn't propergate disequality
 * eagerly, that is, from P(0) and not P(n) we can't conclude 0!=n. Instead we
 * use the negated disequality 0=n in a clause n=0 \/ C to rewrite not P(n) to
 * not P(0) and combine the resulting clause with P(0) to derive C.
 */
class AtLeastOneIterationLemmas
    : public ProgramTraverser<
          std::vector<std::shared_ptr<const logic::ProblemItem>>> {
 public:
  AtLeastOneIterationLemmas(
      const program::Program& program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars,
      unsigned numberOfTraces,
      std::vector<std::shared_ptr<const logic::Axiom>> programSemantics,
      InlinedVariableValues& inlinedVarValues)
      : ProgramTraverser<
            std::vector<std::shared_ptr<const logic::ProblemItem>>>(
            program, locationToActiveVars, numberOfTraces),
        programSemantics(programSemantics),
        inlinedVarValues(inlinedVarValues) {}

 private:
  std::vector<std::shared_ptr<const logic::Axiom>> programSemantics;
  InlinedVariableValues& inlinedVarValues;

  virtual void generateOutputFor(
      const program::WhileStatement* statement,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& items) override;

};

class LoopConditionAnalysisLemmas
    : public ProgramTraverser<
          std::vector<std::shared_ptr<const logic::ProblemItem>>> {
 public:
  LoopConditionAnalysisLemmas(
      const program::Program& program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars,
      unsigned numberOfTraces,
      std::vector<std::shared_ptr<const logic::Axiom>> programSemantics)
      : ProgramTraverser<
            std::vector<std::shared_ptr<const logic::ProblemItem>>>(
            program, locationToActiveVars, numberOfTraces),
        programSemantics(programSemantics) {}

 private:
  std::vector<std::shared_ptr<const logic::Axiom>> programSemantics;

  bool doesNotChangeInLoop(
      std::unordered_set<std::shared_ptr<const program::Variable>>&
          assignedVars,
      std::shared_ptr<const program::IntExpression> expr);

  virtual void generateOutputFor(
      const program::WhileStatement* statement,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& items) override;
};

}  // namespace analysis

#endif
