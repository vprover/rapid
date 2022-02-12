#include "SemanticsHelper.hpp"

#include <cassert>

#include "SymbolDeclarations.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "Variable.hpp"

namespace analysis {

typedef std::shared_ptr<const program::Variable> programVar;

bool getDiff(programVar v, const program::Statement* s, int& diff,
             bool topLevel) {
  // basic first attempt type of thing. Lots of potential to expand
  // here, but not sure how helpful it would be.

  auto isVarV = [](programVar v, std::shared_ptr<const program::Expression> e) {
    if (e->type() == program::Type::VariableAccess) {
      auto castedExpr =
          std::static_pointer_cast<const program::VariableAccess>(e);
      return castedExpr->var == v;
    }
    return false;
  };

  auto isIntConstant = [](std::shared_ptr<const program::Expression> e) {
    return e->type() == program::Type::IntegerConstant;
  };

  auto getIntConstant = [](std::shared_ptr<const program::Expression> e) {
    auto castedExpr =
        std::static_pointer_cast<const program::ArithmeticConstant>(e);
    return castedExpr->value;
  };

  if (s->type() == program::Statement::Type::Assignment) {
    auto castedStatement = static_cast<const program::Assignment*>(s);

    if (isVarV(v, castedStatement->lhs)) {
      // v = rhs
      auto rhs = castedStatement->rhs;
      if (rhs->type() == program::Type::Addition) {
        auto castedAdd = std::static_pointer_cast<const program::Addition>(rhs);
        auto summand1 = castedAdd->summand1;
        auto summand2 = castedAdd->summand2;
        if (isVarV(v, summand1) && isIntConstant(summand2)) {
          diff = diff + getIntConstant(summand2);
          return true;
        } else if (isVarV(v, summand2) && isIntConstant(summand1)) {
          diff = diff + getIntConstant(summand1);
          return true;
        }
      } else if (rhs->type() == program::Type::Subtraction) {
        auto castedSub =
            std::static_pointer_cast<const program::Subtraction>(rhs);
        auto child1 = castedSub->child1;
        auto child2 = castedSub->child2;
        if (isVarV(v, child1) && isIntConstant(child2)) {
          diff = diff - getIntConstant(child2);
          return true;
        }
      }
      return false;
    }
    // updates some other variable
    return true;
  } else if (s->type() == program::Statement::Type::IfElse) {
    auto castedStatement = static_cast<const program::IfElse*>(s);

    int diff1 = 0;
    int diff2 = 0;
    for (auto statement : castedStatement->ifStatements) {
      bool canCalculate = getDiff(v, statement.get(), diff1, false);
      if (!canCalculate) return false;
    }

    for (auto statement : castedStatement->elseStatements) {
      bool canCalculate = getDiff(v, statement.get(), diff2, false);
      if (!canCalculate) return false;
    }
    if (diff1 != diff2) {
      return false;
    }
    diff = diff + diff1;
    return true;
  } else if (s->type() == program::Statement::Type::WhileStatement) {
    auto castedStatement = static_cast<const program::WhileStatement*>(s);

    int diff1 = 0;
    for (auto statement : castedStatement->bodyStatements) {
      bool canCalculate = getDiff(v, statement.get(), diff1, false);
      if (!canCalculate || (diff1 != 0 && !topLevel)) return false;
    }
    diff = diff + diff1;
    return true;
  } else {
    assert(s->type() == program::Statement::Type::SkipStatement);
    diff = diff + 0;
    return true;
  }
}

std::shared_ptr<const logic::Term> 
rectifyVars(
    std::shared_ptr<const logic::Term> mallocTerm,
    std::vector<std::shared_ptr<const logic::Symbol>>& varSyms,
    unsigned startingFrom)
{
  assert(mallocTerm->isMallocFun());
  auto mtaf = std::static_pointer_cast<const logic::FuncTerm>(mallocTerm);
  auto tpTerm = (*mtaf)[0];
  auto tpaf = std::static_pointer_cast<const logic::FuncTerm>(tpTerm);
  
  std::vector<std::shared_ptr<const logic::Term>> vars;
  for(unsigned i = startingFrom; i < tpaf->subterms.size() + startingFrom; i++){
    auto rectifiedVar = natVarSymbol("it" + std::to_string(i));
    varSyms.push_back(rectifiedVar);
    vars.push_back(logic::Terms::var(rectifiedVar));
  }
  auto rectifiedTP = logic::Terms::func(tpaf->symbol,vars);
  return logic::Theory::mallocFun(rectifiedTP);
}

#pragma mark - Methods for generating most used variables

std::shared_ptr<const logic::LVariable> posVar() {
  return logic::Terms::var(posVarSymbol());
}

std::shared_ptr<const logic::LVariable> memLocVar() {
  return logic::Terms::var(locVarSymbol());
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
  //TODO FIX below
  /*std::vector<std::shared_ptr<const logic::Term>> arguments;  
  auto trace = traceTerm(origin->numberOfTraces); 
  if (!origin->isConstant) {  
    assert(tp != nullptr);  
    arguments.push_back(tp);  
  } 
  if (origin->isArray()) {  
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
  } */
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

#pragma mark - Methods for generating most used formulas

std::shared_ptr<const logic::Formula> getDensityFormula(
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

std::shared_ptr<const logic::Formula> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<const program::Expression> expr,
    std::string nameSuffix, std::shared_ptr<const logic::Symbol> itSymbol,
    std::shared_ptr<const logic::LVariable> it,
    std::shared_ptr<const logic::Term> lStartIt,
    std::shared_ptr<const logic::Term> lStartSuccOfIt,
    std::shared_ptr<const logic::Term> n,
    std::shared_ptr<const logic::Term> trace, bool increasing) {
  // add density definition
  auto dense = getDensityFormula(freeVarSymbols, nameSuffix, increasing);
   
  static bool integerIts = util::Configuration::instance().integerIterations();

  auto conjunctLeft = integerIts ? 
      logic::Theory::intLessEqual(logic::Theory::intZero(), it) :
      logic::Theory::boolTrue();

  auto denseFormula = logic::Formulas::universal(
      {itSymbol},
      logic::Formulas::implication(
          logic::Formulas::conjunctionSimp(
            {conjunctLeft,
             logic::Theory::less(it, n)}),
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

std::shared_ptr<const logic::Formula> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<const program::Variable> var, std::string nameSuffix,
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

#pragma mark - Methods for generating sorts

#pragma mark - Methods for generating most used terms/predicates denoting program-expressions
std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::Expression> expr,
    std::shared_ptr<const logic::Term> tp,    
    std::shared_ptr<const logic::Term> trace, 
    std::shared_ptr<const logic::Term> innerTp,
    bool lhsOfAssignment) {
  assert(expr != nullptr);
  assert(tp != nullptr);

  if (expr->isArithmeticExpr()) {
    return toIntTerm(expr, tp, trace, innerTp, lhsOfAssignment);
  }
  
  if (expr->isPointerExpr() || expr->isStructExpr()) {
    switch (expr->type()) {
      case program::Type::VariableAccess: {
        auto castedExpr =
            std::static_pointer_cast<const program::VariableAccess>(expr);
        return toTerm(castedExpr->var, tp, trace);
      }
      case program::Type::PointerDeref: {
        auto castedExpr =
            std::static_pointer_cast<const program::DerefExpression>(expr);
        return toTerm(castedExpr, tp, trace, innerTp);
      }
      case program::Type::FieldAccess: {
        auto castedExpr =
            std::static_pointer_cast<const program::StructFieldAccess>(expr);
        assert(innerTp != nullptr);
        return logic::Theory::valueAt(tp, toTerm(castedExpr, innerTp, trace));    
      }      
      case program::Type::MallocFunc: {
        return logic::Theory::mallocFun(tp);
      }
      case program::Type::NullPtr: {
        return logic::Theory::nullLoc();
      }      
      default :
        assert(false);
    }
  }

  assert(false);
  // to silence compiler warnings, but we should never reach here
  return toTerm(expr, tp, trace);
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::IntArrayApplication> app,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  auto array = toTerm(app->array, timePoint, trace);
  auto index = toTerm(app->index, timePoint, trace);
  return logic::Terms::arraySelect(array, index);
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::DerefExpression> e,
    std::shared_ptr<const logic::Term> tp,
    std::shared_ptr<const logic::Term> trace,
    std::shared_ptr<const logic::Term> innerTp) {
  std::shared_ptr<const logic::Term> exprToTerm;
  // the expression being dereferenced
  auto expr = e->expr;

  //if (expr->type() == program::Type::VariableAccess) {
  //  exprToTerm = toTerm(expr, tp, VariableAccess); //logic::Terms::locConstant(expr->toString());
  //} else {
  //  auto castedExpr =
  //      std::static_pointer_cast<const program::DerefExpression>(expr);
    if(innerTp != nullptr){
      exprToTerm = toTerm(expr, innerTp, trace);
    } else {
      exprToTerm = toTerm(expr, tp, trace);      
    }
  //}
 
  //auto term = logic::Theory::valueAt(timePoint, exprToTerm);
  exprToTerm = logic::Theory::valueAt(tp, exprToTerm, false);
  return exprToTerm;
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::StructFieldAccess> e,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {

  auto struc = e->getStruct();
  auto field = e->getField();
  bool structIsPointer = struc->isPointerExpr();

  //TODO see if there is a nicer way than the horrid static cast below
  auto structType = std::static_pointer_cast<const program::StructType>(
    structIsPointer ?
      struc->exprType()->getChild() :
      struc->exprType());

  auto offSet = structType->getFieldPos(field->name);

  std::shared_ptr<const logic::Term> structTerm;
  if(struc->type() == program::Type::VariableAccess) {
    structTerm = logic::Terms::locConstant(struc->toString());
  } else {
    structTerm = toTerm(struc, timePoint, trace);    
  }

  if(structIsPointer){
    structTerm = logic::Theory::valueAt(timePoint, structTerm, false);
  }

  if(offSet > 0){
    auto offSetTerm = logic::Theory::intConstant(offSet);
    structTerm = logic::Theory::intAddition(structTerm, offSetTerm);
  }
  return structTerm;

  //TODO false since at the moment we don't allow const fields
  //Or so I think!
  //TODO, this should be pushed into caller. At the moment, the translation
  // is not correct for example car.door.handle
  //return logic::Theory::valueAt(timePoint, structTerm, false);  
}

std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<const program::Variable> var,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace) {
  assert(var != nullptr);
  assert(trace != nullptr);

  //    if (!var->isConstant)
  //    {
  assert(timePoint != nullptr);
  //    arguments.push_back(timePoint);

  logic::Symbol::SymbolType typ = logic::Symbol::SymbolType::ProgramVar;
  if (var->isConstant) {
    typ = logic::Symbol::SymbolType::ConstProgramVar;
  }
  
  auto varAsConst = logic::Terms::func(var->name, {}, logic::Sorts::intSort(), false, typ);
  return logic::Theory::valueAt(timePoint, varAsConst, var->isConstant);
}

std::shared_ptr<const logic::Term> toIntTerm(
    std::shared_ptr<const program::Expression> expr,
    std::shared_ptr<const logic::Term> tp,    
    std::shared_ptr<const logic::Term> trace, 
    std::shared_ptr<const logic::Term> innerTp,     
    bool lhsOfAssignment) {
  assert(expr != nullptr);
  assert(tp != nullptr);

  switch (expr->type()) {
    case program::Type::IntegerConstant: {
      auto castedExpr =
          std::static_pointer_cast<const program::ArithmeticConstant>(expr);
      return logic::Theory::intConstant(castedExpr->value);
    }
    case program::Type::Addition: {
      auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
      return logic::Theory::intAddition(
          toTerm(castedExpr->summand1, tp, trace, tp),
          toTerm(castedExpr->summand2, tp, trace, tp));
    }
    case program::Type::Subtraction: {
      auto castedExpr =
          std::static_pointer_cast<const program::Subtraction>(expr);
      return logic::Theory::intSubtraction(
          toTerm(castedExpr->child1, tp, trace, tp),
          toTerm(castedExpr->child2, tp, trace, tp));
    }
    case program::Type::Modulo: {
      auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
      return logic::Theory::intModulo(
          toTerm(castedExpr->child1, tp, trace, tp),
          toTerm(castedExpr->child2, tp, trace, tp));
    }
    case program::Type::Multiplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::Multiplication>(expr);
      return logic::Theory::intMultiplication(
          toTerm(castedExpr->factor1, tp, trace, tp),
          toTerm(castedExpr->factor2, tp, trace, tp));
    }
    case program::Type::FieldAccess: {
      auto castedExpr =
          std::static_pointer_cast<const program::StructFieldAccess>(expr);
      assert(innerTp != nullptr);
      return logic::Theory::valueAt(tp, toTerm(castedExpr, innerTp, trace));    
    }
    case program::Type::VariableAccess: {
      auto castedExpr =
          std::static_pointer_cast<const program::VariableAccess>(expr);         
      return toTerm(castedExpr->var, tp, trace);
    }
    case program::Type::IntArrayApplication: {
      auto castedExpr =
          std::static_pointer_cast<const program::IntArrayApplication>(expr);
      if (lhsOfAssignment) {
        return toTerm(castedExpr->array, tp, trace);
      } else {
        return toTerm(castedExpr, tp, trace);
      }
    }
    case program::Type::PointerDeref: {
      auto castedExpr =
          std::static_pointer_cast<const program::DerefExpression>(expr);
      return toTerm(castedExpr, tp, trace, innerTp);
    }
    default :
      assert(false);
  }
  // to silence compiler warnings, but we should never reach here
  return toTerm(expr, tp, trace);
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
  assert(false);
  // to silence compiler warnings, but we should never reach here
  return toFormula(expr, timePoint, trace);
}

std::shared_ptr<const logic::Formula> quantifyAndGuard(
    std::shared_ptr<const logic::Formula> f,
    const program::Statement* statement,
    bool universal) {
  auto enclosingIteratorsSymbols =
      std::vector<std::shared_ptr<const logic::Symbol>>();
  auto enclosingIteratorTerms =
      std::vector<std::shared_ptr<const logic::Term>>();
  auto enclosingFinalLoopCounts =
      std::vector<std::shared_ptr<const logic::Term>>();

  for (const auto& enclosingLoop : *statement->enclosingLoops) {
    auto itSymbol = iteratorSymbol(enclosingLoop);
    // Note that by using 0, we are no longer trace reasoning compatible
    auto lastItSymbol = lastIterationSymbol(enclosingLoop, 0);

    enclosingIteratorsSymbols.push_back(itSymbol);
    // Code below assumes that enclosing loops are iterated over from outermost
    // to innermost
    enclosingFinalLoopCounts.push_back(
        logic::Terms::func(lastItSymbol, enclosingIteratorTerms));
    enclosingIteratorTerms.push_back(logic::Terms::var(itSymbol));
  }

  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;
  for (unsigned i = 0; i < enclosingIteratorTerms.size(); i++) {
    conjuncts.push_back(logic::Theory::natSub(enclosingIteratorTerms[i],
                                              enclosingFinalLoopCounts[i]));
  }
  auto guard = logic::Formulas::conjunctionSimp(conjuncts);
  auto form = universal ? 
    logic::Formulas::implicationSimp(guard, f) :
    logic::Formulas::conjunctionSimp({guard, f});    
  auto quantified =
    universal ?
      logic::Formulas::universalSimp(enclosingIteratorsSymbols, form) :
      logic::Formulas::existentialSimp(enclosingIteratorsSymbols, form);
  return quantified;
}


std::shared_ptr<const logic::Formula> varEqual(
    std::shared_ptr<const program::Variable> v,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace) {
  auto lhs = toTerm(v, timePoint1, trace);
  auto rhs = toTerm(v, timePoint2, trace);

  return logic::Formulas::equality(lhs, rhs);
}

std::shared_ptr<const logic::Formula> allVarEqual(
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace, std::string label) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto locSymbol = locVarSymbol();
  auto loc = memLocVar();  
  
  auto valueAtTp1 = logic::Theory::valueAt(timePoint1, loc);
  auto valueAtTp2 = logic::Theory::valueAt(timePoint2, loc);
  conjuncts.push_back(logic::Formulas::equality(valueAtTp1, valueAtTp2));

  return logic::Formulas::universal({locSymbol},logic::Formulas::conjunction(conjuncts, label));
}

}  // namespace analysis
