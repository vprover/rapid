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

std::shared_ptr<const logic::Term> defineTargetSymbol(
    std::shared_ptr<const logic::LVariable> target,
    std::shared_ptr<program::Variable> origin,
    std::shared_ptr<const logic::Term> tp) {
  std::shared_ptr<const logic::Term> formula;
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
    program::WhileStatement *whileStatement) {
  assert(whileStatement != nullptr);

  if (util::Configuration::instance().integerIterations()) {
    return intIteratorTermForLoop(whileStatement);
  }

  return logic::Terms::var(iteratorSymbol(whileStatement));
}

std::shared_ptr<const logic::Term> lastIterationTermForLoop(
    program::WhileStatement *whileStatement, unsigned numberOfTraces,
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
    program::Statement *statement) {
  assert(statement != nullptr);
  assert(typeid(*statement) != typeid(program::WhileStatement));

  if (util::Configuration::instance().integerIterations()) {
    return intTimepointForNonLoopStatement(statement);
  }

  auto enclosingLoops = *statement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto &enclosingLoop : enclosingLoops) {
    auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(enclosingIteratorSymbol));
  }

  return logic::Terms::func(locationSymbolForStatement(statement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> timepointForLoopStatement(
    program::WhileStatement *whileStatement,
    std::shared_ptr<const logic::Term> innerIteration) {
  assert(whileStatement != nullptr);
  assert(innerIteration != nullptr);

  if (util::Configuration::instance().integerIterations()) {
    return intTimepointForLoopStatement(whileStatement, innerIteration);
  }

  auto enclosingLoops = *whileStatement->enclosingLoops;
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  for (const auto &enclosingLoop : enclosingLoops) {
    auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
    enclosingIteratorTerms.push_back(
        logic::Terms::var(enclosingIteratorSymbol));
  }
  enclosingIteratorTerms.push_back(innerIteration);
  return logic::Terms::func(locationSymbolForStatement(whileStatement),
                            enclosingIteratorTerms);
}

std::shared_ptr<const logic::Term> startTimepointForStatement(
    program::Statement* statement) {
  if (util::Configuration::instance().integerIterations()) {
    return intStartTimepointForStatement(statement);
  }
  if (typeid(*statement) != typeid(program::WhileStatement)) {
    return timepointForNonLoopStatement(statement);
  } else {
    auto whileStatement = static_cast<program::WhileStatement *>(statement);
    return timepointForLoopStatement(whileStatement, logic::Theory::natZero());
  }
}

std::vector<std::shared_ptr<const logic::Symbol>> enclosingIteratorsSymbols(
    program::Statement* statement) {
  if (util::Configuration::instance().integerIterations()) {
    return intEnclosingIteratorsSymbols(statement);
  }
  auto enclosingIteratorsSymbols =
      std::vector<std::shared_ptr<const logic::Symbol>>();
  for (const auto &enclosingLoop : *statement->enclosingLoops) {
    enclosingIteratorsSymbols.push_back(iteratorSymbol(enclosingLoop));
  }
  return enclosingIteratorsSymbols;
}

#pragma mark - Methods for generating most used timepoint terms and symbols in integer sort

std::shared_ptr<const logic::LVariable> intIteratorTermForLoop(
    program::WhileStatement* whileStatement) {
  assert(whileStatement != nullptr);

  return logic::Terms::var(intIteratorSymbol(whileStatement));
}

std::shared_ptr<const logic::Term> intLastIterationTermForLoop(
    program::WhileStatement* whileStatement, unsigned numberOfTraces,
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
    program::Statement* statement) {
  assert(statement != nullptr);
  assert(typeid(*statement) != typeid(program::WhileStatement));

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
    program::WhileStatement* whileStatement,
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
    program::Statement* statement) {
  if (typeid(*statement) != typeid(program::WhileStatement)) {
    return intTimepointForNonLoopStatement(statement);
  } else {
    auto whileStatement = static_cast<program::WhileStatement*>(statement);
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

#pragma mark - Methods for generating most used formulas

std::shared_ptr<const logic::Term> getDensityFormula(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    std::string nameSuffix, bool increasing) {
  std::vector<std::shared_ptr<const logic::Term>> freeVars = {};
  for (const auto& symbol : freeVarSymbols) {
    freeVars.push_back(logic::Terms::var(symbol));
  }

  std::string direction = increasing ? "increasing" : "decreasing";

  return logic::Formulas::lemmaPredicate(
      "Dense-" + direction + "-" + nameSuffix, freeVars);
}

std::shared_ptr<const logic::Term> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<program::Expression> expr,
    std::string nameSuffix, std::shared_ptr<const logic::Symbol> itSymbol,
    std::shared_ptr<const logic::LVariable> it,
    std::shared_ptr<const logic::Term> lStartIt,
    std::shared_ptr<const logic::Term> lStartSuccOfIt,
    std::shared_ptr<const logic::Term> n,
    std::shared_ptr<const logic::Term> trace, bool increasing) {
  // add density definition
  auto dense = getDensityFormula(freeVarSymbols, nameSuffix, increasing);

  auto denseFormula = logic::Formulas::universal(
      {itSymbol},
      logic::Formulas::implication(
          logic::Theory::natSub(it, n),
          logic::Formulas::disjunction(
              {logic::Formulas::equality(toTerm(expr, lStartSuccOfIt, trace),
                                         toTerm(expr, lStartIt, trace)),
               logic::Formulas::equality(
                   toTerm(expr, lStartSuccOfIt, trace),
                   (increasing ? logic::Theory::intAddition(
                                     toTerm(expr, lStartIt, trace),
                                     logic::Theory::intConstant(1))
                               : logic::Theory::intSubtraction(
                                     toTerm(expr, lStartIt, trace),
                                     logic::Theory::intConstant(1))))})));

  return logic::Formulas::universal(
      freeVarSymbols, logic::Formulas::equivalence(dense, denseFormula));
}

std::shared_ptr<const logic::Term> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<program::Variable> var, std::string nameSuffix,
    std::shared_ptr<const logic::Symbol> itSymbol,
    std::shared_ptr<const logic::LVariable> it,
    std::shared_ptr<const logic::Term> lStartIt,
    std::shared_ptr<const logic::Term> lStartSuccOfIt,
    std::shared_ptr<const logic::Term> n,
    std::shared_ptr<const logic::Term> trace, bool increasing) {
  // add density definition
  auto dense = getDensityFormula(freeVarSymbols, nameSuffix, increasing);

  auto denseFormula = logic::Formulas::universal(
      {itSymbol},
      logic::Formulas::implication(
          logic::Theory::natSub(it, n),
          logic::Formulas::disjunction(
              {logic::Formulas::equality(toTerm(var, lStartSuccOfIt, trace),
                                         toTerm(var, lStartIt, trace)),
               logic::Formulas::equality(
                   toTerm(var, lStartSuccOfIt, trace),
                   (increasing ? logic::Theory::intAddition(
                                     toTerm(var, lStartIt, trace),
                                     logic::Theory::intConstant(1))
                               : logic::Theory::intSubtraction(
                                     toTerm(var, lStartIt, trace),
                                     logic::Theory::intConstant(1))))})));

  return logic::Formulas::universal(
      freeVarSymbols, logic::Formulas::equivalence(dense, denseFormula));
}

#pragma mark - Methods for generating most used terms/predicates denoting program-expressions

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Variable> var,
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

  logic::Symbol::SymbolType typ = logic::Symbol::SymbolType::ProgramVar;
  if (var->isConstant) {
    typ = logic::Symbol::SymbolType::ConstProgramVar;
  }

   if (var->type() == program::ValueType::Bool) {
    return logic::Formulas::predicate(var->name, arguments);
  }

  return logic::Terms::func(var->name, arguments, logic::Sorts::intSort(),
                            false, typ);
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Variable> var,
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

  logic::Symbol::SymbolType typ = logic::Symbol::SymbolType::ProgramVar;
  if (var->isConstant) {
    typ = logic::Symbol::SymbolType::ConstProgramVar;
  }

  if (var->type() == program::ValueType::Bool) {
    return logic::Formulas::predicate(var->name, arguments);
  }
  return logic::Terms::func(var->name, arguments, logic::Sorts::intSort(),
                            false, typ);
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Expression> expr,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  assert(expr != nullptr);
  assert(timePoint != nullptr);

  if (typeid(*expr) == typeid(program::ArithmeticConstant)) {
    auto castedExpr =
        std::static_pointer_cast<const program::ArithmeticConstant>(expr);
    return logic::Theory::intConstant(castedExpr->value);
  } else if (typeid(*expr) == typeid(program::Addition)) {
    auto castedExpr = std::static_pointer_cast<program::Addition>(expr);
    return logic::Theory::intAddition(
        toTerm(castedExpr->child1, timePoint, trace),
        toTerm(castedExpr->child2, timePoint, trace));
  } else if (typeid(*expr) == typeid(program::Subtraction)) {
    auto castedExpr = std::static_pointer_cast<program::Subtraction>(expr);
    return logic::Theory::intSubtraction(
        toTerm(castedExpr->child1, timePoint, trace),
        toTerm(castedExpr->child2, timePoint, trace));
  } else if (typeid(*expr) == typeid(program::Modulo)) {
    auto castedExpr = std::static_pointer_cast<program::Modulo>(expr);
    return logic::Theory::intModulo(
        toTerm(castedExpr->child1, timePoint, trace),
        toTerm(castedExpr->child2, timePoint, trace));
  } else if (typeid(*expr) == typeid(program::Multiplication)) {
    auto castedExpr = std::static_pointer_cast<program::Multiplication>(expr);
    return logic::Theory::intMultiplication(
        toTerm(castedExpr->child1, timePoint, trace),
        toTerm(castedExpr->child2, timePoint, trace));
  } else if (typeid(*expr) == typeid(program::VariableAccess)) {
    auto castedExpr = std::static_pointer_cast<program::VariableAccess>(expr);
    return toTerm(castedExpr->var, timePoint, trace);
  } else if (typeid(*expr) == typeid(program::ArrayApplication)) {
    auto castedExpr = std::static_pointer_cast<program::ArrayApplication>(expr);
    return toTerm(castedExpr->array, timePoint,
                  toTerm(castedExpr->index, timePoint, trace), trace);
  } else if (typeid(*expr) == typeid(program::BooleanConstant)) {
    auto castedExpr =
        std::static_pointer_cast<const program::BooleanConstant>(expr);
    return castedExpr->value ? logic::Theory::boolTrue()
                             : logic::Theory::boolFalse();
  } else if (typeid(*expr) == typeid(program::BooleanAnd)) {
    auto castedExpr = std::static_pointer_cast<program::BooleanAnd>(expr);
    return logic::Formulas::conjunction(
        {toTerm(castedExpr->child1, timePoint, trace),
         toTerm(castedExpr->child2, timePoint, trace)});
  } else if (typeid(*expr) == typeid(program::BooleanOr)) {
    auto castedExpr = std::static_pointer_cast<const program::BooleanOr>(expr);
    return logic::Formulas::disjunction(
        {toTerm(castedExpr->child1, timePoint, trace),
         toTerm(castedExpr->child2, timePoint, trace)});
  } else if (typeid(*expr) == typeid(program::BooleanNot)) {
    auto castedExpr = std::static_pointer_cast<const program::BooleanNot>(expr);
    return logic::Formulas::negation(
        toTerm(castedExpr->child, timePoint, trace));
  } else if (typeid(*expr) == typeid(program::ArithmeticComparison)) {
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
  assert(0);
}

std::shared_ptr<const logic::Term> varEqual(
    std::shared_ptr<program::Variable> v,
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

std::shared_ptr<const logic::Term> allVarEqual(
    const std::vector<std::shared_ptr<program::Variable>> &activeVars,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace, std::string label) {
  std::vector<std::shared_ptr<const logic::Term>> conjuncts;
  for (const auto &var : activeVars) {
    if (!var->isConstant) {
      conjuncts.push_back(varEqual(var, timePoint1, timePoint2, trace));
    }
  }
  return logic::Formulas::conjunction(conjuncts, label);
}
}  // namespace analysis
