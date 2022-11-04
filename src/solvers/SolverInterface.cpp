#include "SolverInterface.hpp"

namespace solvers {

typedef Vampire::Expression VExpr;

VampireSolver::VampireSolver()
 : _solver(Vampire::Solver::getSolverPtr(Vampire::Solver::Logic::SMT_LIB)) {
}


VExpr VampireSolver::solverPlus(VExpr v1, VExpr v2) const
{
  return _solver->sum(v1,v2);
}

VExpr VampireSolver::solverMin(VExpr v1, VExpr v2) const
{
  return _solver->difference(v1,v2);
}

VExpr VampireSolver::solverIntConst(int i) const
{
  return _solver->integerConstant(i);  
}   

VExpr VampireSolver::solverVar(std::shared_ptr<const Term> t) const
{
  auto varSort = convertSort(t->sort());
  auto var = _solver->var(t->symbol->name, varSort);
  return _solver->varTerm(var);
}

VExpr VampireSolver::solverFalse() const
{
  return _solver->falseFormula();
}

VExpr VampireSolver::solverTrue() const
{
  return _solver->trueFormula();
}

VExpr VampireSolver::solverEquiv(VExpr v1, VExpr v2) const
{
  return _solver->iff(v1, v2);
}


VExpr VampireSolver::solverExi(std::vector<std::shared_ptr<const Symbol>> vars, 
                               VExpr expr) const
{
  for(auto v : vars){
    auto var = _solver->var(v->name, convertSort(v->rngSort));
    expr = _solver->exists(var, expr);
  }
  return expr;
}

VExpr VampireSolver::solverUni(std::vector<std::shared_ptr<const Symbol>> vars, 
                               VExpr expr) const
{
  for(auto v : vars){
    auto var = _solver->var(v->name, convertSort(v->rngSort));
    expr = _solver->forall(var, expr);
  }
  return expr;
}

VExpr VampireSolver::solverImp(VExpr v1, VExpr v2) const
{
  return _solver->implies(v1, v2);
}

VExpr VampireSolver::solverGt(VExpr v1, VExpr v2) const
{ 
  return _solver->gt(v1, v2);  
}

VExpr VampireSolver::solverGte(VExpr v1, VExpr v2) const
{
  return _solver->geq(v1, v2);  
}

VExpr VampireSolver::solverLt(VExpr v1, VExpr v2) const
{
  return _solver->lt(v1, v2);  
}

VExpr VampireSolver::solverLte(VExpr v1, VExpr v2) const
{
  return _solver->leq(v1, v2);  
}

VExpr VampireSolver::solverApp( 
  std::shared_ptr<const Symbol> sym,
  std::vector<VExpr> args) const
{
  std::vector<Vampire::Sort> argSorts;
  for(auto& sort : sym->argSorts){
    argSorts.push_back(convertSort(sort));
  }

  auto convert = [](logic::Symbol::SymbolType st){
    switch(st){
      case logic::Symbol::SymbolType::LemmaPredicate:
        return Vampire::RapidSym::LEMMA_PRED;
      case logic::Symbol::SymbolType::ProgramVar:
        return Vampire::RapidSym::PROGRAM_VAR;      
      case logic::Symbol::SymbolType::ConstProgramVar:
        return Vampire::RapidSym::CONST_VAR;   
      case logic::Symbol::SymbolType::FinalLoopCount:
        return Vampire::RapidSym::FN_LOOP_COUNT;
      case logic::Symbol::SymbolType::TimePoint:
        return Vampire::RapidSym::TIME_POINT;   
      case logic::Symbol::SymbolType::MallocFunc:
        return Vampire::RapidSym::MALLOC;
      case logic::Symbol::SymbolType::ChainFunc:
        return Vampire::RapidSym::CHAIN;
      case logic::Symbol::SymbolType::NullPtr:
        return Vampire::RapidSym::NULL_PTR;        
      case logic::Symbol::SymbolType::ObjectArray:
        return Vampire::RapidSym::OBJ_ARRAY; 
      default:
        return Vampire::RapidSym::NONE;                                                           
    }
  };

  Vampire::Symbol vSym;
  Vampire::RapidSym rSym = convert(sym->symbolType);

  if(sym->isPredicateSymbol()){
    vSym =  _solver->predicate(sym->name, argSorts.size(), argSorts, rSym);
  } else {
    auto rangeSort = convertSort(sym->rngSort);
    vSym =  _solver->function(sym->name, argSorts.size(), rangeSort, argSorts, rSym);
  }
  
  return _solver->term(vSym, args);
}

VExpr VampireSolver::solverNeg(VExpr f) const
{
  return _solver->negation(f);
}

VExpr VampireSolver::solverDisj(std::vector<VExpr> disjuncts) const
{
  return _solver->orFormula(disjuncts);
}

VExpr VampireSolver::solverConj(std::vector<VExpr> conjuncts) const
{
  return _solver->andFormula(conjuncts);
}

VExpr VampireSolver::solverEq(VExpr l, VExpr r, bool pol) const
{
  return _solver->equality(l, r, pol);
}

Vampire::Sort VampireSolver::convertSort(const Sort* s) const
{
  if(s->isIntSort()){
    return _solver->integerSort();
  }

  if(s->isBoolSort()){
    return _solver->boolSort();
  }

  if(s->isTimeSort()){
    return _solver->timeSort();
  }

  // TODO deal with arrays and perhaps other interpreted sorts
  return _solver->sort(s->name);
}

void VampireSolver::setStrategy(std::string strat) const
{
  _solver->setOptions(strat);
}

void VampireSolver::setTimeLimit(int t) const
{
  _solver->setTimeLimit(t);
}

void VampireSolver::solverAssert(VExpr v) const
{
  _solver->assertFormula(v);
}

void VampireSolver::addConjecture(VExpr v) const 
{
  _solver->addConjecture(v);
}

void VampireSolver::declareSymbol(std::shared_ptr<const Symbol> sym) const
{

  //TODO remove code duplication
  std::vector<Vampire::Sort> argSorts;
  for(auto& sort : sym->argSorts){
    argSorts.push_back(convertSort(sort));
  }

  auto convert = [](logic::Symbol::SymbolType st){
    switch(st){
      case logic::Symbol::SymbolType::LemmaPredicate:
        return Vampire::RapidSym::LEMMA_PRED;
      case logic::Symbol::SymbolType::ProgramVar:
        return Vampire::RapidSym::PROGRAM_VAR;      
      case logic::Symbol::SymbolType::ConstProgramVar:
        return Vampire::RapidSym::CONST_VAR;   
      case logic::Symbol::SymbolType::FinalLoopCount:
        return Vampire::RapidSym::FN_LOOP_COUNT;
      case logic::Symbol::SymbolType::TimePoint:
        return Vampire::RapidSym::TIME_POINT;   
      case logic::Symbol::SymbolType::MallocFunc:
        return Vampire::RapidSym::MALLOC;
      case logic::Symbol::SymbolType::ChainFunc:
        return Vampire::RapidSym::CHAIN;
      case logic::Symbol::SymbolType::NullPtr:
        return Vampire::RapidSym::NULL_PTR;        
      case logic::Symbol::SymbolType::ObjectArray:
        return Vampire::RapidSym::OBJ_ARRAY; 
      default:
        return Vampire::RapidSym::NONE;                                                           
    }
  };

  Vampire::RapidSym rSym = convert(sym->symbolType);

  if(sym->isPredicateSymbol()){
    _solver->predicate(sym->name, argSorts.size(), argSorts, rSym);
  } else {
    auto rangeSort = convertSort(sym->rngSort);
    _solver->function(sym->name, argSorts.size(), rangeSort, argSorts, rSym);
  }
}

void VampireSolver::declareStruct(Sort* sort) const
{ 
  std::string structName = sort->name;
  std::string lowerName = logic::toLower(structName);
  std::string nullName = lowerName + "_null_loc";

  std::vector<Vampire::Field> fields;

  auto structSort = static_cast<logic::StructSort*>(sort);
  for(auto& sel : structSort->selectors()){
    auto sym = logic::Signature::fetch(sel);
    const Sort* range = sym->rngSort;
    Vampire::Sort s = convertSort(range);
    if(range == sort){
      std::string chain = sel + "_chain";
      std::string support = "in_support_" + sel + "_chain";
      fields.push_back(_solver->field(sel, s, chain, support));
    } else {
      fields.push_back(_solver->field(sel, s));      
    }
  }
  _solver->declareStruct(structName, nullName, fields);
}

bool VampireSolver::solve()
{
  Vampire::Result res;
  try{
    res = _solver->solveWithCasc();
  } catch (Vampire::ApiException& e){
    std::cout<< "Exception: "<<e.msg()<<std::endl;
    return 0;
  } catch (Vampire::FormulaBuilderException& f) {
    std::cout<< "Exception: "<<f.msg()<<std::endl;
    return 0;    
  }

  if(res.unsatisfiable()){
    return true;
  }
  return false;
}

bool VampireSolver::solveWithSched(Vampire::Solver::Schedule sched)
{
  Vampire::Result res;
  try{
    res = _solver->solveWithSched(sched);
  } catch (Vampire::ApiException& e){
    std::cout<< "Exception: "<<e.msg()<<std::endl;
    return 0;
  } catch (Vampire::FormulaBuilderException& f) {
    std::cout<< "Exception: "<<f.msg()<<std::endl;
    return 0;    
  }

  if(res.unsatisfiable()){
    return true;
  }
  return false;  
}

VampireSolver VampireSolver::_instance;

}  // namespace solvers
