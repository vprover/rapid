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
#include "LogicProblem.hpp"
#include "Program.hpp"
#include "SemanticsHelper.hpp"
#include "SemanticsInliner.hpp"
#include "Statements.hpp"
#include "InvariantGenerator.hpp"

#include "Output.hpp"

namespace analysis {

class Semantics {
 public:
   
  enum class MemoryModel {
    TYPED,
    UNTYPED
  };

  Semantics(
      const program::Program& program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<const program::Variable>>>
          locationToActiveVars,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems,
      unsigned numberOfTraces,
      bool containsSelfPointer,
      bool containsNondetU)
      : program(program),
        endTimePointMap(
            AnalysisPreComputation::computeEndTimePointMap(program)),
        locationToActiveVars(locationToActiveVars),
        problemItems(problemItems),
        numberOfTraces(numberOfTraces),
        containsSelfPointer(containsSelfPointer),
        containsNondetU(containsNondetU),
        inlinedVariableValues(traceTerms(numberOfTraces)) {

    auto model = util::Configuration::instance().memoryModel();
    if(model == "typed"){
      _model = MemoryModel::TYPED;
    } else {
      _model = MemoryModel::UNTYPED;
    }

    _ig = new InvariantGenerator(_model == MemoryModel::TYPED, locationToActiveVars, endTimePointMap, containsSelfPointer);
   
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
      util::Output::warning("Ignoring request to inline semantics as inlining is "
                   "currently not sound in the presence of pointer variables");
      util::Configuration::instance().setDontInline();
    }
  }

  ~Semantics(){
    delete _ig;
  }  

  std::pair<std::vector<std::shared_ptr<const logic::Axiom>>,
            InlinedVariableValues>
  generateSemantics();


 private:

  InvariantGenerator* _ig;
  MemoryModel _model;

  const int SMALL_STRUCT_SIZE = 5;

  const program::Program& program;
  const EndTimePointMap endTimePointMap;
  const std::unordered_map<
      std::string, std::vector<std::shared_ptr<const program::Variable>>>
      locationToActiveVars;
  std::vector<std::shared_ptr<const logic::ProblemItem>>& problemItems;
  const unsigned numberOfTraces;
  const bool containsSelfPointer;
  const bool containsNondetU;
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

  // used to hold axioms that assert that final loop counters are 
  // not negative
  std::vector<std::shared_ptr<const logic::Axiom>> finalCountersNotNeg;
  // used to hold axioms that assert that malloc returns a fresh location
  // not in the support of any existing chains
  std::vector<std::shared_ptr<const logic::Axiom>> mallocFreshAxioms;


  std::vector<std::pair<std::shared_ptr<const logic::Term>, int>> mallocStatements;
  std::set<std::pair<std::string, std::string>> frameAxiomsToAdd;
  std::set<std::pair<std::string, std::string>> sameChainAxiomsToAdd;
  std::set<std::string> sameAxiomsToAdd;

  // as we generate semantics, we record all the statements
  // whose semantics we wish to try and strengthen
  std::vector<std::pair<const program::Statement*, 
              std::shared_ptr<const logic::Formula>>> _statementsToStrengthen;

  void addAllSameAxioms();

  std::shared_ptr<const logic::Formula> explode(
      std::shared_ptr<const logic::Term> m1, int size1,
      std::shared_ptr<const logic::Term> m2, int size2);

  void addMallocFreshnessAxiom(
     const program::Assignment* assignment,
     std::shared_ptr<const logic::Term> tp,
     std::shared_ptr<const logic::Term> assignedToVar,     
     std::shared_ptr<const logic::Term> mallocTerm);
  void generateMemoryLocationSemantics(
      std::vector<std::shared_ptr<const logic::Axiom>>& axioms,
      std::vector<std::shared_ptr<const logic::Axiom>>& axioms2);

  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::Statement* statement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace,
      // conjunction of the conditions (coming from if statements)
      // required to reach this statement
      std::shared_ptr<const logic::Formula> condition);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::VarDecl* varDecl, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::Assignment* assignment, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::IfElse* ifElse, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace,
      std::shared_ptr<const logic::Formula> condition);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::WhileStatement* whileStatement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace,
      std::shared_ptr<const logic::Formula> condition);
  std::shared_ptr<const logic::Formula> generateSemantics(
      const program::SkipStatement* skipStatement, SemanticsInliner& inliner,
      std::shared_ptr<const logic::Term> trace);
};
}  // namespace analysis
#endif