#include "AssertAssumeProcessor.hpp"

#include <algorithm>
#include <cassert>
#include <memory>
#include <unordered_set>
#include <vector>

#include "Formula.hpp"
#include "Options.hpp"
#include "Sort.hpp"
#include "SymbolDeclarations.hpp"
#include "Term.hpp"
#include "Theory.hpp"

namespace analysis {

void AssertAssumeProcessor::process() {

  for (const auto& function : program.functions) {
    std::vector<std::shared_ptr<const logic::Formula>> conjunctsFunction;

    for (const auto& trace : traceTerms(numberOfTraces)) {
      std::vector<std::shared_ptr<const logic::Formula>> conjunctsTrace;

      for (const auto& statement : function->statements) {
        process(statement.get(), trace, Formulas::trueFormula());
      }
    }
  }
}


void AssertAssumeProcessor::process(
    const program::Statement* statement,
    std::shared_ptr<const logic::Term> trace,
    std::shared_ptr<const logic::Formula> condition) {

  auto lNext = endTimePointMap.at(statement);        

  auto freeVarSymbols = enclosingIteratorsSymbols(statement);

  if(statement->type() == program::Statement::Type::Assertion){
    auto castedStatement = static_cast<const program::Assertion*>(statement);
    auto assertion = toFormula(castedStatement->formula, lNext, trace);
    assertion = Formulas::universal(freeVarSymbols,
      Formulas::implicationSimp(condition,assertion));

    // TODO add line number
    problemItems.push_back(std::make_shared<logic::Conjecture>(
      assertion, "User assertion"));
  } else if(statement->type() == program::Statement::Type::Assumption){
    auto castedStatement = static_cast<const program::Assumption*>(statement);
    auto assumption = toFormula(castedStatement->formula, lNext, trace);
    assumption = Formulas::universal(freeVarSymbols,
      Formulas::implicationSimp(condition,assumption));

    // TODO add line number
    problemItems.push_back(std::make_shared<logic::Axiom>(
      assumption, "User assumption"));
  } if (statement->type() == program::Statement::Type::IfElse) {
    auto castedStatement = static_cast<const program::IfElse*>(statement);
    process(castedStatement, trace, condition);
  } else if (statement->type() == program::Statement::Type::WhileStatement) {
    auto castedStatement =
        static_cast<const program::WhileStatement*>(statement);
    process(castedStatement, trace, condition);
  }
}

void AssertAssumeProcessor::process(
    const program::IfElse* ifElse,
    std::shared_ptr<const logic::Term> trace, 
    std::shared_ptr<const logic::Formula> cond) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto lStart = startTimepointForStatement(ifElse);

  auto condition = toFormula(ifElse->condition, lStart, trace);
  auto negatedCondition = logic::Formulas::negation(condition);

  auto conditionIf = Formulas::conjunctionSimp({cond, condition});
  auto conditionElse = Formulas::conjunctionSimp({cond, negatedCondition});

  // Part 2: collect all formulas describing semantics of branches and assert
  // them conditionally
  for (const auto& statement : ifElse->ifStatements) {
    process(statement.get(), trace, conditionIf);
  }

  for (const auto& statement : ifElse->elseStatements) {
    process(statement.get(), trace, conditionElse);
  }
}

void AssertAssumeProcessor::process(
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> trace, 
    std::shared_ptr<const logic::Formula> condition) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto itSymbol = iteratorSymbol(whileStatement);
  auto it = logic::Terms::var(itSymbol);
  auto n = lastIterationTermForLoop(whileStatement, numberOfTraces, trace);
  auto zero = logic::Theory::zero();

  std::shared_ptr<const logic::Formula> newCondition;

  if (util::Configuration::instance().integerIterations()) {
    newCondition = Formulas::conjunctionSimp({
      condition,
      Theory::lessEq(Theory::zero(), it),
      Theory::less(it, n)
    });
  } else {
    newCondition = Formulas::conjunctionSimp({
      condition,
      Theory::less(it, n)
    });      
  }

  for (const auto& statement : whileStatement->bodyStatements) {
    process(statement.get(), trace, newCondition);
  }
 
}

}  // namespace analysis