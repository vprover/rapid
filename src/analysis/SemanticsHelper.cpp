#include "SemanticsHelper.hpp"

#include <cassert>

#include "Options.hpp"
#include "SymbolDeclarations.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "Variable.hpp"

namespace analysis {
#pragma mark - Methods for generating most used variables

std::shared_ptr<const logic::LVariable> posVar() {
  return logic::Terms::var(posVarSymbol());
}

#pragma mark - Methods for generating most used trace terms

std::shared_ptr<const logic::Term> traceTerm(unsigned traceNumber) {
  return logic::Terms::func(traceSymbol(traceNumber), {});
}

std::vector<std::shared_ptr<const logic::Term>> traceTerms(
    unsigned numberOfTraces) {
  std::vector<std::shared_ptr<const logic::Term>> traces;
  for (unsigned traceNumber = 1; traceNumber < numberOfTraces + 1;
       traceNumber++) {
    traces.push_back(traceTerm(traceNumber));
  }
  return traces;
}

#pragma mark - Methods for generating color and target symbols for symbol elimination

std::shared_ptr<const logic::LVariable> initTargetSymbol(
    const program::Variable* var) {
  return logic::Terms::var(declareInitTargetSymbol(var));
}

std::shared_ptr<const logic::LVariable> finalTargetSymbol(
    const program::Variable* var) {
  return logic::Terms::var(declareFinalTargetSymbol(var));
}

void colorSymbol(const program::Variable* var) { declareColorSymbolLeft(var); }

std::shared_ptr<const logic::Formula> defineTargetSymbol(
    std::shared_ptr<const logic::LVariable> target,
    std::shared_ptr<const program::Variable> origin,
    std::shared_ptr<const logic::Term> tp) {
  std::shared_ptr<const logic::Formula> formula;
  std::vector<std::shared_ptr<const logic::Term>> arguments;
  auto trace = traceTerm(origin->numberOfTraces);

  if (!origin->isConstant) {
    assert(tp != nullptr);
    arguments.push_back(tp);
  }

  if (origin->isArray) {
    auto posSymbol = posVarSymbol();
    auto pos = posVar();
    arguments.push_back(pos);
    std::vector<std::shared_ptr<const logic::Term>> targetArguments;
    targetArguments.push_back(pos);

    formula = logic::Formulas::universal(
        {posSymbol},
        logic::Formulas::equality(
            logic::Terms::func(target->symbol->name, targetArguments,
                               logic::Sorts::intSort()),
            toTerm(origin, tp, pos, trace)));
  } else {
    formula = logic::Formulas::equality(
        logic::Terms::func(target->symbol->name, {}, logic::Sorts::intSort()),
        logic::Terms::func(origin->name, arguments, logic::Sorts::intSort()));
  }
  return formula;
}

#pragma mark - Methods for generating most used timepoint terms and symbols

std::shared_ptr<const logic::LVariable> iteratorTermForLoop(
    const program::WhileStatement* whileStatement) {
  assert(whileStatement != nullptr);

  if (util::Configuration::instance().integerIterations()) {
    return intIteratorTermForLoop(whileStatement);
  }

  return logic::Terms::var(iteratorSymbol(whileStatement));
}

std::shared_ptr<const logic::Term> lastIterationTermForLoop(
    const program::WhileStatement* whileStatement, unsigned numberOfTraces,
    std::shared_ptr<const logic::Term> trace) {
  assert(whileStatement != nullptr);
  assert(trace != nullptr);

  if (util::Configuration::instance().integerIterations()) {
    return intLastIterationTermForLoop(whileStatement, numberOfTraces, trace);
  }

  auto symbol = lastIterationSymbol(whileStatement, numberOfTraces);
  std::vector<std::shared_ptr<const logic::Term>> subterms;
  for (const auto& loop : *whileStatement->enclosingLoops) {
    subterms.push_back(iteratorTermForLoop(loop));
  }
  if (numberOfTraces > 1) {
    subterms.push_back(trace);
  }
  return logic::Terms::func(symbol, subterms);
}

std::shared_ptr<const logic::Term> timepointForNonLoopStatement(
    const program::Statement* statement) {
  assert(statement != nullptr);
  assert(statement->type() != program::Statement::Type::WhileStatement);

  if (util::Configuration::instance().integerIterations()) {
    return intTimepointForNonLoopStatement(statement);
  }

  auto enclosingLoops = *statement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto& enclosingLoop : enclosingLoops) {
    auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(enclosingIteratorSymbol));
  }

  return logic::Terms::func(locationSymbolForStatement(statement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> timepointForLoopStatement(
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> innerIteration) {
  assert(whileStatement != nullptr);
  assert(innerIteration != nullptr);

  if (util::Configuration::instance().integerIterations()) {
    return intTimepointForLoopStatement(whileStatement, innerIteration);
  }

  auto enclosingLoops = *whileStatement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto& enclosingLoop : enclosingLoops) {
    auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(enclosingIteratorSymbol));
  }
  enclosingIteratorTerms.push_back(innerIteration);
  return logic::Terms::func(locationSymbolForStatement(whileStatement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> startTimepointForStatement(
    const program::Statement* statement) {
  if (util::Configuration::instance().integerIterations()) {
    return intStartTimepointForStatement(statement);
  }

  if (statement->type() != program::Statement::Type::WhileStatement) {
    return timepointForNonLoopStatement(statement);
  } else {
    auto whileStatement =
        static_cast<const program::WhileStatement*>(statement);
    return timepointForLoopStatement(whileStatement, logic::Theory::natZero());
  }
}

std::vector<std::shared_ptr<const logic::Symbol>> enclosingIteratorsSymbols(
    const program::Statement* statement) {
  if (util::Configuration::instance().integerIterations()) {
    return intEnclosingIteratorsSymbols(statement);
  }
  auto enclosingIteratorsSymbols =
      std::vector<std::shared_ptr<const logic::Symbol>>();
  for (const auto& enclosingLoop : *statement->enclosingLoops) {
    enclosingIteratorsSymbols.push_back(iteratorSymbol(enclosingLoop));
  }
  return enclosingIteratorsSymbols;
}

#pragma mark - Methods for generating most used timepoint terms and symbols in integer sort

std::shared_ptr<const logic::LVariable> intIteratorTermForLoop(
    const program::WhileStatement* whileStatement) {
  assert(whileStatement != nullptr);

  return logic::Terms::var(intIteratorSymbol(whileStatement));
}

std::shared_ptr<const logic::Term> intLastIterationTermForLoop(
    const program::WhileStatement* whileStatement, unsigned numberOfTraces,
    std::shared_ptr<const logic::Term> trace) {
  assert(whileStatement != nullptr);
  assert(trace != nullptr);

  auto symbol = intLastIterationSymbol(whileStatement, numberOfTraces);
  std::vector<std::shared_ptr<const logic::Term>> subterms;
  for (const auto& loop : *whileStatement->enclosingLoops) {
    subterms.push_back(intIteratorTermForLoop(loop));
  }
  if (numberOfTraces > 1) {
    subterms.push_back(trace);
  }
  return logic::Terms::func(symbol, subterms);
}

std::shared_ptr<const logic::Term> intTimepointForNonLoopStatement(
    const program::Statement* statement) {
  assert(statement != nullptr);
  assert(statement->type() != program::Statement::Type::WhileStatement);

  auto enclosingLoops = *statement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto& enclosingLoop : enclosingLoops) {
    auto intEnclosingIteratorSymbol = intIteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(intEnclosingIteratorSymbol));
  }

  return logic::Terms::func(locationSymbolForStatement(statement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> intTimepointForLoopStatement(
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> innerIteration) {
  assert(whileStatement != nullptr);
  assert(innerIteration != nullptr);

  auto enclosingLoops = *whileStatement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto& enclosingLoop : enclosingLoops) {
    auto enclosingIteratorSymbol = intIteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(enclosingIteratorSymbol));
  }
  enclosingIteratorTerms.push_back(innerIteration);
  return logic::Terms::func(locationSymbolForStatement(whileStatement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> intStartTimepointForStatement(
    const program::Statement* statement) {
  if (statement->type() != program::Statement::Type::WhileStatement) {
    return intTimepointForNonLoopStatement(statement);
  } else {
    auto whileStatement =
        static_cast<const program::WhileStatement*>(statement);
    return intTimepointForLoopStatement(whileStatement,
                                        logic::Theory::intZero());
  }
}

std::vector<std::shared_ptr<const logic::Symbol>> intEnclosingIteratorsSymbols(
    const program::Statement* statement) {
  auto enclosingIteratorsSymbols =
      std::vector<std::shared_ptr<const logic::Symbol>>();
  for (const auto& enclosingLoop : *statement->enclosingLoops) {
    enclosingIteratorsSymbols.push_back(intIteratorSymbol(enclosingLoop));
  }
  return enclosingIteratorsSymbols;
}

#pragma mark - Methods for generating most used terms/predicates denoting program-expressions
std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::Variable> var,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  assert(var != nullptr);
  assert(trace != nullptr);

  assert(!var->isArray);

  std::vector<std::shared_ptr<const logic::Term>> arguments;

  if (!var->isConstant) {
    assert(timePoint != nullptr);
    arguments.push_back(timePoint);
  }
  if (var->numberOfTraces > 1) {
    arguments.push_back(trace);
  }

  return logic::Terms::func(var->name, arguments, logic::Sorts::intSort());
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::Variable> var,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> position,
    std::shared_ptr<const logic::Term> trace) {
  assert(var != nullptr);
  assert(position != nullptr);
  assert(trace != nullptr);

  assert(var->isArray);

  std::vector<std::shared_ptr<const logic::Term>> arguments;

  if (!var->isConstant) {
    assert(timePoint != nullptr);
    arguments.push_back(timePoint);
  }

  arguments.push_back(position);

  if (var->numberOfTraces > 1) {
    arguments.push_back(trace);
  }

  return logic::Terms::func(var->name, arguments, logic::Sorts::intSort());
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::IntExpression> expr,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  assert(expr != nullptr);
  assert(timePoint != nullptr);

  switch (expr->type()) {
    case program::IntExpression::Type::ArithmeticConstant: {
      auto castedExpr =
          std::static_pointer_cast<const program::ArithmeticConstant>(expr);
      return logic::Theory::intConstant(castedExpr->value);
    }
    case program::IntExpression::Type::Addition: {
      auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
      return logic::Theory::intAddition(
          toTerm(castedExpr->summand1, timePoint, trace),
          toTerm(castedExpr->summand2, timePoint, trace));
    }
    case program::IntExpression::Type::Subtraction: {
      auto castedExpr =
          std::static_pointer_cast<const program::Subtraction>(expr);
      return logic::Theory::intSubtraction(
          toTerm(castedExpr->child1, timePoint, trace),
          toTerm(castedExpr->child2, timePoint, trace));
    }
    case program::IntExpression::Type::Modulo: {
      auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
      return logic::Theory::intModulo(
          toTerm(castedExpr->child1, timePoint, trace),
          toTerm(castedExpr->child2, timePoint, trace));
    }
    case program::IntExpression::Type::Multiplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::Multiplication>(expr);
      return logic::Theory::intMultiplication(
          toTerm(castedExpr->factor1, timePoint, trace),
          toTerm(castedExpr->factor2, timePoint, trace));
    }
    case program::IntExpression::Type::IntVariableAccess: {
      auto castedExpr =
          std::static_pointer_cast<const program::IntVariableAccess>(expr);
      return toTerm(castedExpr->var, timePoint, trace);
    }
    case program::IntExpression::Type::IntArrayApplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::IntArrayApplication>(expr);
      return toTerm(castedExpr->array, timePoint,
                    toTerm(castedExpr->index, timePoint, trace), trace);
    }
  }
}

std::shared_ptr<const logic::Formula> toFormula(
    std::shared_ptr<const program::BoolExpression> expr,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  assert(expr != nullptr);
  assert(timePoint != nullptr);

  switch (expr->type()) {
    case program::BoolExpression::Type::BooleanConstant: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanConstant>(expr);
      return castedExpr->value ? logic::Theory::boolTrue()
                               : logic::Theory::boolFalse();
    }
    case program::BoolExpression::Type::BooleanAnd: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanAnd>(expr);
      return logic::Formulas::conjunction(
          {toFormula(castedExpr->child1, timePoint, trace),
           toFormula(castedExpr->child2, timePoint, trace)});
    }
    case program::BoolExpression::Type::BooleanOr: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanOr>(expr);
      return logic::Formulas::disjunction(
          {toFormula(castedExpr->child1, timePoint, trace),
           toFormula(castedExpr->child2, timePoint, trace)});
    }
    case program::BoolExpression::Type::BooleanNot: {
      auto castedExpr =
          std::static_pointer_cast<const program::BooleanNot>(expr);
      return logic::Formulas::negation(
          toFormula(castedExpr->child, timePoint, trace));
    }
    case program::BoolExpression::Type::ArithmeticComparison: {
      auto castedExpr =
          std::static_pointer_cast<const program::ArithmeticComparison>(expr);
      switch (castedExpr->kind) {
        case program::ArithmeticComparison::Kind::GT:
          return logic::Theory::intGreater(
              toTerm(castedExpr->child1, timePoint, trace),
              toTerm(castedExpr->child2, timePoint, trace));
        case program::ArithmeticComparison::Kind::GE:
          return logic::Theory::intGreaterEqual(
              toTerm(castedExpr->child1, timePoint, trace),
              toTerm(castedExpr->child2, timePoint, trace));
        case program::ArithmeticComparison::Kind::LT:
          return logic::Theory::intLess(
              toTerm(castedExpr->child1, timePoint, trace),
              toTerm(castedExpr->child2, timePoint, trace));
        case program::ArithmeticComparison::Kind::LE:
          return logic::Theory::intLessEqual(
              toTerm(castedExpr->child1, timePoint, trace),
              toTerm(castedExpr->child2, timePoint, trace));
        case program::ArithmeticComparison::Kind::EQ:
          return logic::Formulas::equality(
              toTerm(castedExpr->child1, timePoint, trace),
              toTerm(castedExpr->child2, timePoint, trace));
      }
    }
  }
}

std::shared_ptr<const logic::Formula> varEqual(
    std::shared_ptr<const program::Variable> v,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace) {
  if (!v->isArray) {
    return logic::Formulas::equality(toTerm(v, timePoint1, trace),
                                     toTerm(v, timePoint2, trace));
  } else {
    auto posSymbol = posVarSymbol();
    auto pos = posVar();
    return logic::Formulas::universal(
        {posSymbol},
        logic::Formulas::equality(toTerm(v, timePoint1, pos, trace),
                                  toTerm(v, timePoint2, pos, trace)));
  }
}

std::shared_ptr<const logic::Formula> allVarEqual(
    const std::vector<std::shared_ptr<const program::Variable>>& activeVars,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace, std::string label) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;
  for (const auto& var : activeVars) {
    if (!var->isConstant) {
      conjuncts.push_back(varEqual(var, timePoint1, timePoint2, trace));
    }
  }
  return logic::Formulas::conjunction(conjuncts, label);
}
}  // namespace analysis
