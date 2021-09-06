#ifndef __SemanticsInliner__
#define __SemanticsInliner__

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "AnalysisPreComputation.hpp"
#include "Expression.hpp"
#include "Problem.hpp"
#include "Term.hpp"
#include "Variable.hpp"

namespace analysis {
class SemanticsInliner {
 public:
  SemanticsInliner(
      std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems,
      std::shared_ptr<const logic::Term> trace)
      : persistentVarTerms(),
        persistentConstVarTerms(),
        currTimepoint(nullptr),
        trace(trace),
        cachedIntVarValues(),
        cachedArrayVarTimepoints() {
    assert(trace != nullptr);
    computePersistentTerms(problemItems);
  }

  /*
   * the timepoint we are at currently in the (simulated) execution of the
   * program
   */
  std::shared_ptr<const logic::Term> currTimepoint;

  // note:
  // - we handle persistent terms referencing a timepoint as soon as we visit
  // the location of the timepoint.
  // - since a const variable is formalized as term without a
  // timepoint/location, we would miss to handle persistance for such terms.
  // - we solve this by handling persistance for terms which formalize const
  // variables immediately when they are declared in
  // setIntVarValue/setArrayVarTimepoint.

  // returns formula which defines persistent terms (if necessary) for variables
  // in 'activeVars'. note: at the timepoint of calling this method we assume
  // that the variable-values (which can be changed using
  // setCurrentVariableValue()) are already set to the values for timepoint
  // 'timepoint'.
  std::shared_ptr<const logic::Formula> handlePersistence(
      std::shared_ptr<const logic::Term> timepoint,
      const std::vector<std::shared_ptr<const program::Variable>>& activeVars,
      std::string label = "");
  std::shared_ptr<const logic::Formula> handlePersistenceOfLoop(
      std::shared_ptr<const logic::Term> startTimepoint,
      std::shared_ptr<const logic::Term> iterationTimepoint,
      const std::vector<std::shared_ptr<const program::Variable>>& vars);

  // update the currently cached value for the given variable
  // note that for integers we cache the actual variable value, while for arrays
  // we cache the last relevant timepoint the intVar-version handles persistance
  // of const vars.
  std::shared_ptr<const logic::Formula> setIntVarValue(
      std::shared_ptr<const program::Variable> var,
      std::shared_ptr<const logic::Term> value);
  void setArrayVarTimepoint(std::shared_ptr<const program::Variable> arrayVar,
                            std::shared_ptr<const logic::Term> timepoint);

  // methods to convert variables and more general expressions to terms, while
  // using the cached variable values. note: 'timePoint' is only used in the
  // case where no value for 'var' is currently cached (in which case the cache
  // gets initialized with 'timepoint').
  std::shared_ptr<const logic::Term> toCachedTermFull(
      std::shared_ptr<const program::Variable> var);
  std::shared_ptr<const logic::Term> toCachedTermFull(
      std::shared_ptr<const program::Variable> arrayVar,
      std::shared_ptr<const logic::Term> position);
  std::shared_ptr<const logic::Term> toCachedTerm(
      std::shared_ptr<const program::IntExpression> expr);
  std::shared_ptr<const logic::Formula> toCachedFormula(
      std::shared_ptr<const program::BoolExpression> expr);

  const std::unordered_map<std::shared_ptr<const program::Variable>,
                           std::shared_ptr<const logic::Term>>&
  getCachedIntVarValues() {
    return cachedIntVarValues;
  }
  const std::unordered_map<std::shared_ptr<const program::Variable>,
                           std::shared_ptr<const logic::Term>>&
  getCachedArrayVarTimepoints() {
    return cachedArrayVarTimepoints;
  }

 private:
  std::shared_ptr<const logic::Term> trace;

  typedef std::unordered_map<std::string, std::vector<std::string>>
      MapVarNameToLocationName;
  typedef std::unordered_set<std::string> SetConstVarNames;

  /*
   * a dictionary mapping the name of each non-const var to the name of the
   * location where the var is referenced in some input conjecture (or in some
   * input axiom/lemma) Note that we don't (need to) know the exact term (of the
   * conjecture/axiom/lemma) that occurs (we don't care about the exact
   * iteration or the position in the array) We keep track of these terms, since
   * the semantics must define those terms in order to be complete.
   */
  MapVarNameToLocationName persistentVarTerms;
  /*
   * a set containg the name of each const var which is referenced in some input
   * conjecture (or in some input axiom/lemma) Note that we don't (need to) save
   * the exact term (of the conjecture/axiom/lemma) that occurs (we don't care
   * about the position in the array) We keep track of these terms, since the
   * semantics must define those terms in order to be complete.
   */
  SetConstVarNames persistentConstVarTerms;
  void computePersistentTerms(
      std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems);
  void computePersistentTermsRec(std::shared_ptr<const logic::Formula> f);
  void computePersistentTermsRec(std::shared_ptr<const logic::Term> t);

  typedef std::unordered_map<std::shared_ptr<const program::Variable>,
                             std::shared_ptr<const logic::Term>>
      IntVarValues;
  typedef std::unordered_map<std::shared_ptr<const program::Variable>,
                             std::shared_ptr<const logic::Term>>
      ArrayVarValues;
  /*
   * dictionaries to keep track of the current variable values.
   * for array-variables we keep track of the last timepoint the array was
   * assigned for integer-variables, we could do the same, but we do even more:
   * - we keep track of the term describing the actual value of the variable
   * - note that this is not possible for arrays, since the actual value of all
   * positions might not be expressible in our language
   */
  IntVarValues cachedIntVarValues;
  ArrayVarValues cachedArrayVarTimepoints;
};

/*
 * data structure which keeps track of the values inlined while generating the
 * semantics of a program. It is needed for generating the trace lemmas, as
 * these lemmas need to use the same inlining as the semantics (we could also
 * inline the user conjecture(s), but we want to keep them in their original
 * form)
 *
 * For generating correct trace lemmas, we depend on the fact that variables,
 * which get assigned in a loop, are never inlined for that loop. We check and
 * ensure this property in the InlinedVariableValues-class.
 */
class InlinedVariableValues {
 public:
  InlinedVariableValues(std::vector<std::shared_ptr<const logic::Term>> traces);

  void initializeWhileStatement(const program::WhileStatement* whileStatement);
  void setValue(const program::WhileStatement* whileStatement,
                std::shared_ptr<const program::Variable> var,
                std::shared_ptr<const logic::Term> trace,
                std::shared_ptr<const logic::Term> value);
  void setArrayTimepoint(const program::WhileStatement* whileStatement,
                         std::shared_ptr<const program::Variable> arrayVar,
                         std::shared_ptr<const logic::Term> trace,
                         std::shared_ptr<const logic::Term> timepoint);

  // the following four methods provide access to the value of the given
  // expression at the after inlining has been performed for each of the
  // following two methods getValue(...) we require that a corresponding value
  // has been set earlier using setValue(...).
  std::shared_ptr<const logic::Term> toInlinedTerm(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const program::Variable> var,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Term> toInlinedTerm(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const program::Variable> arrayVar,
      std::shared_ptr<const logic::Term> position,
      std::shared_ptr<const logic::Term> trace);

  // evaluate the given expr at the given timepoint, while using inlined values
  // for whileStatement for all variables, which are not assigned in that
  // WhileStatement.
  std::shared_ptr<const logic::Term> toInlinedTerm(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const program::IntExpression> expr,
      std::shared_ptr<const logic::Term> timepoint,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> toInlinedFormula(
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const program::BoolExpression> expr,
      std::shared_ptr<const logic::Term> timepoint,
      std::shared_ptr<const logic::Term> trace);

 private:
  class TermPointerHash {
   public:
    std::size_t operator()(const std::shared_ptr<const logic::Term>& p) const {
      return std::hash<const logic::Term>()(*p);
    }
  };
  class TermPointerEqual {
   public:
    bool operator()(const std::shared_ptr<const logic::Term>& p1,
                    const std::shared_ptr<const logic::Term>& p2) const {
      return *p1 == *p2;
    }
  };

  typedef std::unordered_map<std::shared_ptr<const program::Variable>,
                             std::shared_ptr<const logic::Term>>
      VarToValueMap;
  typedef std::unordered_map<const program::WhileStatement*, VarToValueMap>
      LoopToVarToValueMap;
  typedef std::unordered_map<std::shared_ptr<const logic::Term>,
                             LoopToVarToValueMap, TermPointerHash,
                             TermPointerEqual>
      TraceToLoopToVarToValueMap;

  typedef std::unordered_map<std::shared_ptr<const program::Variable>,
                             std::shared_ptr<const logic::Term>>
      ArrayVarToTimepointMap;
  typedef std::unordered_map<const program::WhileStatement*,
                             ArrayVarToTimepointMap>
      LoopToArrayVarToTimepointMap;
  typedef std::unordered_map<std::shared_ptr<const logic::Term>,
                             LoopToArrayVarToTimepointMap, TermPointerHash,
                             TermPointerEqual>
      TraceToLoopToArrayVarToTimepointMap;

  TraceToLoopToVarToValueMap values;
  TraceToLoopToArrayVarToTimepointMap arrayValues;
};
}  // namespace analysis
#endif