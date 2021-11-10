#include "GenerateMemConjectures.hpp"

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

std::vector<std::shared_ptr<const logic::Conjecture>>
MemConjectureGenerator::generateMemSafetyConjectures() {
  // generate semantics compositionally
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  for (const auto& function : program.functions) {
    std::vector<std::shared_ptr<const logic::Formula>> conjunctsFunction;

    auto trace = traceTerm(0);

    for (const auto& statement : function->statements) {
      generateConjectures(statement.get(), trace);
    }
  }

  std::vector<std::string> emp = {};

  auto disjunct = logic::Formulas::disjunctionSimp(memSafetyDisjuncts);
  auto conj1 = std::make_shared<logic::Conjecture>(
       disjunct, "Conjecture stating that there exists an invalid memory access", emp, false, true);

  auto conjunct = logic::Formulas::conjunctionSimp(memSafetyConjuncts);
  auto conj2 =  std::make_shared<logic::Conjecture>(
       conjunct, "Conjecture stating that all memory accesses are valid", emp, true, false);

  std::vector<std::shared_ptr<const logic::Conjecture>> conjectures;
  conjectures.push_back(conj1);
  conjectures.push_back(conj2);
  return conjectures;
}


void MemConjectureGenerator::createLeftHandsSides(
    std::shared_ptr<const logic::Term> lhs,
    std::vector<std::shared_ptr<const logic::Term>>& lhSides) {
  if (lhs->type() == logic::Term::Type::FuncTerm) {
    auto castedLhs = std::static_pointer_cast<const logic::FuncTerm>(lhs);

    if (castedLhs->isDerefAt()) {
      lhSides.push_back(lhs);
    }

    if (castedLhs->isValueAt() || castedLhs->isDerefAt()) {
      assert(castedLhs->subterms.size() == 2);
      auto location = castedLhs->subterms[1];
      createLeftHandsSides(location, lhSides);
    }
  }
}

void MemConjectureGenerator::generateConjectures(
    const program::Statement* statement,
    std::shared_ptr<const logic::Term> trace) {
  if (statement->type() == program::Statement::Type::Assignment) {
    auto castedStatement = static_cast<const program::Assignment*>(statement);
    generateConjectures(castedStatement, trace);
  } else if (statement->type() == program::Statement::Type::IfElse) {
    auto castedStatement = static_cast<const program::IfElse*>(statement);
    generateConjectures(castedStatement, trace);
  } else if (statement->type() == program::Statement::Type::WhileStatement) {
    auto castedStatement =
        static_cast<const program::WhileStatement*>(statement);
    generateConjectures(castedStatement, trace);
  }
}

void MemConjectureGenerator::generateConjectures(
    const program::Assignment* assignment,
    std::shared_ptr<const logic::Term> trace) {

  auto isIntArrayApp = [](std::shared_ptr<const program::Expression> e) {
    return (e->type() == program::Type::IntArrayApplication);
  };

  auto l2 = endTimePointMap.at(assignment);
  auto lhs = assignment->lhs;
  std::shared_ptr<const logic::Term> lhsTerm;

  // a[expr1] = expr2
  if (isIntArrayApp(lhs)) {
    lhsTerm = toTerm(lhs, l2, trace, true);
  } else {
    lhsTerm = toTerm(lhs, l2, trace);    	
  }

  std::vector<std::shared_ptr<const logic::Term>> leftHandSides;
  createLeftHandsSides(lhsTerm, leftHandSides);
  for (auto& lhs : leftHandSides) {
    auto eq = logic::Formulas::equality(lhs, logic::Theory::nullLoc());
    auto diseq =
        logic::Formulas::disequality(lhs, logic::Theory::nullLoc());

    // false means use existential quantification
    // we hypothesise that these exists and iteration such
    // that the dereference at that reference is invalid
    memSafetyDisjuncts.push_back(quantifyAndGuard(eq, assignment, false));
    memSafetyConjuncts.push_back(quantifyAndGuard(diseq, assignment));
  }
}


void MemConjectureGenerator::generateConjectures(
    const program::IfElse* ifElse, 
    std::shared_ptr<const logic::Term> trace) {

  for (const auto& statement : ifElse->ifStatements) {
    generateConjectures(statement.get(), trace);
  }

  for (const auto& statement : ifElse->elseStatements) {
    generateConjectures(statement.get(), trace);
  }
}

void MemConjectureGenerator::generateConjectures(
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> trace) {

  for (const auto& statement : whileStatement->bodyStatements) {
    generateConjectures(statement.get(), trace);
  }
}


}