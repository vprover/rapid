#include "Semantics.hpp"

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
#include "Solver.hpp"

namespace analysis {

std::vector<std::shared_ptr<const program::Variable>> intersection(
    std::vector<std::shared_ptr<const program::Variable>> v1,
    std::vector<std::shared_ptr<const program::Variable>> v2) {
  std::vector<std::shared_ptr<const program::Variable>> v3;

  std::sort(v1.begin(), v1.end());
  std::sort(v2.begin(), v2.end());

  std::set_intersection(v1.begin(), v1.end(), v2.begin(), v2.end(),
                        back_inserter(v3));
  return v3;
}

std::vector<std::shared_ptr<const program::Variable>> difference(
    std::vector<std::shared_ptr<const program::Variable>> v1,
    std::vector<std::shared_ptr<const program::Variable>> v2) {
  std::vector<std::shared_ptr<const program::Variable>> v3;

  std::sort(v1.begin(), v1.end());
  std::sort(v2.begin(), v2.end());

  std::set_difference(v1.begin(), v1.end(), v2.begin(), v2.end(),
                      back_inserter(v3));
  return v3;
}

template <class T>
std::vector<T> vecUnion(std::vector<T> v1, std::vector<T> v2) {
  std::vector<T> v3;

  std::sort(v1.begin(), v1.end());
  std::sort(v2.begin(), v2.end());

  std::set_union(v1.begin(), v1.end(), v2.begin(), v2.end(), back_inserter(v3));
  return v3;
}

std::vector<std::shared_ptr<const logic::Axiom>> Semantics::generateBounds() {
  std::vector<std::shared_ptr<const program::Variable>> allVars;

  for (auto it : locationToActiveVars) {
    allVars = vecUnion<std::shared_ptr<const program::Variable>>(it.second, allVars);
  }

  std::vector<std::shared_ptr<const logic::Axiom>> axioms;

  auto locSymbol = locationSymbol("tp", 0);
  auto lVar = logic::Terms::var(locSymbol);
  auto z = logic::Theory::intConstant(0);

  for (const auto& var : allVars) {
    if (var->isNat()) {
      for (const auto& trace : traceTerms(numberOfTraces)) {
        auto axiom =
            logic::Theory::intGreaterEqual(toTerm(var, lVar, trace), z);

        if (!var->isConstant) {
          axiom = logic::Formulas::universal({locSymbol}, axiom);
        }
      
        axioms.push_back(std::make_shared<logic::Axiom>(axiom));
      }
    }
  }

  return axioms;
}

std::pair<std::vector<std::shared_ptr<const logic::Axiom>>,
          InlinedVariableValues>
Semantics::generateSemantics() {

  // generate semantics compositionally
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  for (const auto& function : program.functions) {
    std::vector<std::shared_ptr<const logic::Formula>> conjunctsFunction;

    for (const auto& trace : traceTerms(numberOfTraces)) {
      std::vector<std::shared_ptr<const logic::Formula>> conjunctsTrace;

      SemanticsInliner inliner(problemItems, trace);
      for (const auto& statement : function->statements) {
        auto semantics = generateSemantics(statement.get(), inliner, trace);
        conjunctsTrace.push_back(semantics);
      }
      if (util::Configuration::instance().inlineSemantics()) {
        // handle persistence of last statement of the function
        auto lEnd = endTimePointMap.at(function->statements.back().get());
        inliner.currTimepoint = lEnd;
        auto f = inliner.handlePersistence(
            lEnd, locationToActiveVars.at(lEnd->symbol->name),
            "Define referenced terms denoting variable values at " +
                lEnd->symbol->name);
        conjunctsTrace.push_back(f);
      }

      std::vector<std::shared_ptr<const logic::Formula>> targetSymbolAxioms;

      // postcondition mode
      // TODO: handling for multiple traces
      if (util::Configuration::instance().postcondition()) {
        for (auto i = coloredSymbols.begin(); i != coloredSymbols.end(); ++i) {
          auto name = i->first;
          auto var = i->second;
          auto variable = var.get();

          // add target-symbols
          auto symInit = initTargetSymbol(variable);
          auto symFinal = finalTargetSymbol(variable);
          colorSymbol(variable);
          // hack to get the start and end timepoint of the first (outermost)
          // while loop
          auto lEnd = loopEndTimePoints.front();
          auto lStart = loopStartTimePoints.front();

          // add definitions for final and initial values
          targetSymbolAxioms.push_back(
              defineTargetSymbol(symInit, var, lStart));
          targetSymbolAxioms.push_back(defineTargetSymbol(symFinal, var, lEnd));
        }
      }      

      Vampire::Solver& solver = Vampire::Solver::getSolver();
      std::cout << "Vampire version " << solver.version() << std::endl;
      std::cout << "Vampire commit " << solver.commit() << std::endl;


      if (numberOfTraces > 1) {
        conjunctsFunction.push_back(logic::Formulas::conjunctionSimp(
            conjunctsTrace, "Semantics of trace " + trace->symbol->name));
      } else {
        // if there is only one trace, don't group semantics by trace but use
        // semantics directly
        conjunctsFunction = conjunctsTrace;
      }
    }

    auto axiomFormula = logic::Formulas::conjunctionSimp(conjunctsFunction);
    axioms.push_back(std::make_shared<logic::Axiom>(
        axiomFormula, "Semantics of function " + function->name,
        logic::ProblemItem::Visibility::Implicit));
  }

  auto tp = tpVarSymbol("tp");
  auto tp2 = tpVarSymbol("tp2");
  auto memLocSymbol = locVarSymbol("m1");

  if(_model == MemoryModel::UNTYPED){
    axioms.push_back(logic::Theory::untypedFrameAxiom(tp, tp2, memLocSymbol));
  } else {
    axioms.push_back(logic::Theory::typedFrameAxiom(tp, tp2, memLocSymbol));
  }

  for(auto& pair : frameAxiomsToAdd){
    axioms.push_back(logic::Theory::frameAxiom(tp, tp2, pair.first, pair.second));
  }
  for(auto& name : sameAxiomsToAdd){
    axioms.push_back(logic::Theory::allSameAxiom(tp, tp2, name));
  }
  
  generateMemoryLocationSemantics(axioms);
  return std::make_pair(axioms, inlinedVariableValues);
}

void Semantics::generateMemoryLocationSemantics(
    std::vector<std::shared_ptr<const logic::Axiom>>& axioms)
{
  std::vector<std::shared_ptr<const program::Variable>> allVars;
  for (auto vars : locationToActiveVars) {
    // WARNING if there are multiple vars with the same name, but in different
    // scope this is dangerous!
    //TODO break this down by scope?
    allVars = vecUnion<std::shared_ptr<const program::Variable>>(allVars, vars.second);
  }

  std::vector<std::shared_ptr<const logic::Formula>> memFormulas;

  auto memLocSymbol = locVarSymbol("m1");
  auto memLocSymbol2 = locVarSymbol("m2");

  auto size1Sym = locVarSymbol("size1");
  auto size2Sym = locVarSymbol("size2");

  bool needDisjoint2Axiom = false;
  bool needDisjoint1Axiom = false;

  // adding axioms to ensure memory disjointness. For example a != b
  // for distinct variables a and b
  for (int i = 0; i < allVars.size(); i++) {
    auto var = allVars[i];
    auto varAsTerm = logic::Terms::func(logic::Signature::fetch(var->name), {});

    if(_model == MemoryModel::UNTYPED){
      // in the typed case, the aixoms below are not needed
      // since separation between heap and stack is enforced via typing

      // no local variable is a heap location
      auto notHeapLoc = logic::Formulas::negation(logic::Theory::heapLoc(varAsTerm));
      memFormulas.push_back(notHeapLoc);

      // no variable is equal to the null location
      auto notNull =
          logic::Formulas::disequality(varAsTerm, logic::Theory::nullLoc());
      memFormulas.push_back(notNull);
    }

    //pairwise disjointness of variables
    for (int j = i + 1; j < allVars.size(); j++) {
      auto var2 = allVars[j];
      auto var2AsTerm =
          logic::Terms::func(logic::Signature::fetch(var2->name), {});
      memFormulas.push_back(logic::Formulas::disequality(varAsTerm, var2AsTerm));
    }
  }

  // disjointess between heap locations
  for(unsigned k = 0; k < mallocStatements.size(); k++){
    auto mallocStatement = mallocStatements[k].first;
    int size = mallocStatements[k].second;    
    auto sizeTerm = logic::Theory::intConstant(size);

    // in the typed case, structs are treated as atomic entities
    // that cannot be decomposed.
    bool untypedModel = (_model == MemoryModel::UNTYPED);

    std::vector<std::shared_ptr<const logic::Symbol>> varSyms;
    mallocStatement = rectifyVars(mallocStatement, varSyms);
    
    //for dynamic allocations within a loop, no two allocations
    //return the same memory location 
    if(varSyms.size()){
      std::vector<std::shared_ptr<const logic::Symbol>> varSyms2;
      auto mallocStatement2 = rectifyVars(mallocStatement, varSyms2, varSyms.size());
      
      std::shared_ptr<const logic::Formula> diffLocs;
      if(size > 1 && untypedModel){
        if(util::Configuration::instance().explodeMemRegions() && size < SMALL_STRUCT_SIZE){
           diffLocs = explode(mallocStatement, size, mallocStatement2, size); 
        } else {
          needDisjoint1Axiom = true;
          diffLocs = logic::Theory::disjoint1(mallocStatement, sizeTerm, mallocStatement2, sizeTerm);
        }
      } else {
        diffLocs = logic::Formulas::disequality(mallocStatement, mallocStatement2);        
      }

      std::vector<std::shared_ptr<const logic::Formula>> forms;    
      for(unsigned i = 0; i < varSyms.size(); i++){
        auto var1 = logic::Terms::var(varSyms[i]);
        auto var2 = logic::Terms::var(varSyms2[i]);
        forms.push_back(logic::Formulas::disequality(var1, var2));
      }
      auto prem = logic::Formulas::conjunctionSimp(forms);
      auto imp = logic::Formulas::implicationSimp(prem, diffLocs);

      memFormulas.push_back(logic::Formulas::universalSimp(
        vecUnion<std::shared_ptr<const logic::Symbol>>(varSyms, varSyms2), imp));      
    }

    // Is heap location and is not null
    std::shared_ptr<const logic::Formula> notNull;
    std::shared_ptr<const logic::Formula> isHeapLoc;    
    if(size > 1 && untypedModel){
      if(util::Configuration::instance().explodeMemRegions() && size < SMALL_STRUCT_SIZE){
         notNull = explode(mallocStatement, size, logic::Theory::nullLoc(), 1); 
       
        std::vector<std::shared_ptr<const logic::Formula>> forms;    
        forms.push_back(logic::Theory::heapLoc(mallocStatement));
        for(unsigned i = 1; i < size; i++){
          forms.push_back(logic::Theory::heapLoc(
            logic::Theory::intAddition(mallocStatement, logic::Theory::intConstant(i))));
        }
        isHeapLoc = logic::Formulas::conjunctionSimp(forms);         
      } else {
        needDisjoint2Axiom = true;
        notNull = logic::Theory::disjoint2(mallocStatement, sizeTerm, logic::Theory::nullLoc());
        //TODO isHeapLoc
      }
    } else {
      notNull = logic::Formulas::disequality(mallocStatement, 
                  logic::Theory::nullLoc(mallocStatement->sort()->name));
      if(untypedModel)
        // only extend the signature as needed
        isHeapLoc = logic::Theory::heapLoc(mallocStatement);        
    }    
    memFormulas.push_back(logic::Formulas::universalSimp(varSyms, notNull));
    if(untypedModel)
      memFormulas.push_back(logic::Formulas::universalSimp(varSyms, isHeapLoc));

    // No two memory regions are the same
    for (int l = k + 1; l < mallocStatements.size(); l++) {
      auto mallocStatement2 = mallocStatements[l].first;
      int size2 = mallocStatements[l].second;    
      auto sizeTerm2 = logic::Theory::intConstant(size2);

      std::vector<std::shared_ptr<const logic::Symbol>> varSyms2;
      mallocStatement2 = rectifyVars(mallocStatement2, varSyms2, varSyms.size());

      std::shared_ptr<const logic::Formula> diffLocs;
      if((size > 1 || size2 > 1) && untypedModel){
        if(util::Configuration::instance().explodeMemRegions() && size < SMALL_STRUCT_SIZE){
           diffLocs = explode(mallocStatement, size, mallocStatement2, size2); 
        } else {
          needDisjoint1Axiom = true;          
          diffLocs = logic::Theory::disjoint1(mallocStatement, sizeTerm, mallocStatement2, sizeTerm2);
        }
      } else {
        diffLocs = logic::Formulas::disequality(mallocStatement, mallocStatement2);        
      }

      memFormulas.push_back(logic::Formulas::universalSimp(
        vecUnion<std::shared_ptr<const logic::Symbol>>(varSyms, varSyms2), diffLocs));  
    }
  }

  if(needDisjoint1Axiom) 
    axioms.push_back(logic::Theory::disjoint1Axiom(memLocSymbol,size1Sym,memLocSymbol2,size2Sym));
  
  if(needDisjoint2Axiom)
    axioms.push_back(logic::Theory::disjoint2Axiom(memLocSymbol,memLocSymbol2,size2Sym));

  // TODO see how useful the axiom below is
  /*auto value = logic::Theory::valueAt(tpVar, memLocVar);
  auto valueFormula = logic::Formulas::disequality(memLocVar, value);
  auto valueNotIdentity =
      logic::Formulas::universal({tp, memLocSymbol}, valueFormula);
  memFormulas.push_back(valueNotIdentity);*/

  auto memSemantics = logic::Formulas::conjunctionSimp(memFormulas);

  axioms.push_back(std::make_shared<logic::Axiom>(
      memSemantics, "Semantics of memory locations",
      logic::ProblemItem::Visibility::Implicit));
}

std::shared_ptr<const logic::Formula> Semantics::explode(
    std::shared_ptr<const logic::Term> m1, int size1,
    std::shared_ptr<const logic::Term> m2, int size2)
{

  std::vector<std::shared_ptr<const logic::Formula>> forms;    
  
  forms.push_back(logic::Formulas::disequality(m1, m2));
  for(unsigned i = 1; i < size2; i++){
    auto sum = logic::Theory::intAddition(m2, logic::Theory::intConstant(i));
    forms.push_back(logic::Formulas::disequality(m1, sum));
  }

  for(unsigned i = 1; i < size1; i++){
    auto sum = logic::Theory::intAddition(m1, logic::Theory::intConstant(i));   
    forms.push_back(logic::Formulas::disequality(sum, m2));
    
    for(unsigned j = 1; j < size2; j++){
      auto sum2 = logic::Theory::intAddition(m2, logic::Theory::intConstant(j));   
      forms.push_back(logic::Formulas::disequality(sum, sum2));     
    }
  }

  return logic::Formulas::conjunctionSimp(forms);
}

void Semantics::addAllSameAxioms() {
  sameAxiomsToAdd.insert("value");
  for(auto sort : logic::Sorts::structSorts()){
    sameAxiomsToAdd.insert(sort->name);
  }  
}


std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::Statement* statement, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  if (statement->type() == program::Statement::Type::VarDecl) {
    auto castedStatement = static_cast<const program::VarDecl*>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else if (statement->type() == program::Statement::Type::Assignment) {
    auto castedStatement = static_cast<const program::Assignment*>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else if (statement->type() == program::Statement::Type::IfElse) {
    auto castedStatement = static_cast<const program::IfElse*>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else if (statement->type() == program::Statement::Type::WhileStatement) {
    auto castedStatement =
        static_cast<const program::WhileStatement*>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else {
    assert(statement->type() == program::Statement::Type::SkipStatement);
    auto castedStatement =
        static_cast<const program::SkipStatement*>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  }
}

std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::VarDecl* varDecl, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  //TODO just ignore declarations that are at the end of scope?
  if (util::Configuration::instance().memSafetyMode()) {
    auto var = varDecl->var;
    if (var->isPointer()) {
      // initialse pointers to point to null location
      auto l2 = endTimePointMap.at(varDecl);
      auto eq = logic::Formulas::equality(
          toTerm(var, l2, trace), logic::Theory::nullLoc(),
          "Initialising pointer " + var->name + " to null at location " +
              varDecl->location);
      return eq;
    }
  }
  return logic::Theory::boolTrue();
}

std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::Assignment* assignment, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto l1 = startTimepointForStatement(assignment);
  auto l2 = endTimePointMap.at(assignment);
  auto l1Name = l1->symbol->name;
  auto l2Name = l2->symbol->name;
  auto activeVars = intersection(locationToActiveVars.at(l1Name),
                                 locationToActiveVars.at(l2Name));
  auto varsGoingOutOfScope = 
    difference(locationToActiveVars.at(l1Name),
               locationToActiveVars.at(l2Name));

  if (util::Configuration::instance().inlineSemantics()) {
    // This is safe as we assume no pointers when using the inliner

    if (assignment->lhs->type() == program::Type::VariableAccess) {
      auto castedLhs =
          std::static_pointer_cast<const program::VariableAccess>(
              assignment->lhs);

      inliner.currTimepoint = l1;
      auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
      conjuncts.push_back(f1);

      auto f2 = inliner.setIntVarValue(castedLhs->var,
                                       inliner.toCachedTerm(assignment->rhs));
      conjuncts.push_back(f2);

      return logic::Formulas::conjunctionSimp(
          conjuncts, "Update variable " + castedLhs->var->name +
                         " at location " + assignment->location);

    } else {
      auto application =
          std::static_pointer_cast<const program::IntArrayApplication>(
              assignment->lhs);

      inliner.currTimepoint = l1;
      auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
      conjuncts.push_back(f1);

      // val_int a l2 = store (var_int a last_set) index cached(rhs)

      auto var = application->array;

      auto array_now = toTerm(var, l2, trace);
      auto array_before = inliner.toCachedTermFull(var);

      auto index = inliner.toCachedTerm(application->index);
      auto toStore = inliner.toCachedTerm(assignment->rhs);

      auto rhs = logic::Terms::arrayStore(array_before, index, toStore);

      auto eq1 = logic::Formulas::equality(array_now, rhs);
      conjuncts.push_back(eq1);

      // set last assignment of a to l2
      inliner.setArrayVarTimepoint(var, l2);

      return logic::Formulas::conjunctionSimp(
          conjuncts, "Update array variable " + application->array->name +
                         " at location " + assignment->location);
    }
  } else {
    // Deal with array and non-array variables together.

    // assignment must be of the form:
    //  x = t
    //  x = #y
    //  *...*x = t
    //  *...*x = #y
    //  x[expr] = expr

    auto lhs = assignment->lhs;
    auto rhs = assignment->rhs;

    auto isVar = [](std::shared_ptr<const program::Expression> e) {
      return (e->type() == program::Type::VariableAccess);
    };

    auto isDerefExpr = [](std::shared_ptr<const program::Expression> e) {
      return (e->type() == program::Type::PointerDeref);     
    };

    auto isRefExpr = [](std::shared_ptr<const program::Expression> e) {
      return (e->type() == program::Type::VarReference);
    };

    auto isIntArrayApp = [](std::shared_ptr<const program::Expression> e) {
      return (e->type() == program::Type::IntArrayApplication);
    };

    auto isNonVarIntExpr = [&isVar](std::shared_ptr<const program::Expression> e) {
      return (!isVar(e) && e->isArithmeticExpr());
    };

    std::shared_ptr<const logic::Term> lhsTerm;
    std::shared_ptr<const logic::Term> rhsTerm;

    //[*...*]x = term
    if (!isIntArrayApp(lhs) && !isRefExpr(rhs)) {
      lhsTerm = toTerm(lhs, l2, trace, l1);
      rhsTerm = toTerm(rhs, l1, trace, l1);
    }

    //[*...*]x = #y
    if (isRefExpr(rhs)) {
      auto castedRhs =
          std::static_pointer_cast<const program::VarReference>(rhs);

      if(std::find(varsGoingOutOfScope.begin(), varsGoingOutOfScope.end(),
         castedRhs->referent) != varsGoingOutOfScope.end()){
        //rhs variable about to go out of scope
        rhsTerm = logic::Theory::nullLoc();
      } else{
        rhsTerm = logic::Terms::locConstant(castedRhs->referent->name);
      }
      lhsTerm = toTerm(lhs, l2, trace, l1);
    }

    // a[expr1] = expr2
    if (isIntArrayApp(lhs)) {
      auto asArrayApp =
          std::static_pointer_cast<const program::IntArrayApplication>(lhs);
      auto index = toTerm(asArrayApp->index, l1, trace);
      auto toStore = toTerm(rhs, l1, trace);
      auto array = toTerm(asArrayApp->array, l1, trace);
      rhsTerm = logic::Terms::arrayStore(array, index, toStore);
      lhsTerm = toTerm(lhs, l2, trace, nullptr, true);
    }

    if(rhsTerm->isMallocFun()){
      mallocStatements.push_back(make_pair(rhsTerm, lhs->exprType()->getChild()->size()));
    }

    // lhs(l2) = rhs(l1);
    // We have a problem here
    // Parser sensibly allows the following: 
    //   const Int a = 10;
    // however, the code below assums non-const ness
    auto eq = logic::Formulas::equality(lhsTerm, rhsTerm);
    auto lhsAsFunc = std::static_pointer_cast<const logic::FuncTerm>(lhsTerm);
    auto array = lhsAsFunc;

    conjuncts.push_back(eq);

    auto arrayAccessedAt = (*std::static_pointer_cast<const logic::FuncTerm>(array))[1];
    //auto locSymbol = locVarSymbol();
   // auto loc = memLocVar();
 
    bool activeVarsContainsPointerVars = false;


    std::string suffix = "";
    if(array->symbol->isSelectorSymbol()){
      auto selectorName = array->symbol->name;
      auto sortName = arrayAccessedAt->sort()->name;
      suffix = "_" + selectorName;
      frameAxiomsToAdd.insert(std::make_pair(sortName, selectorName));
    }
    conjuncts.push_back(logic::Theory::framePred(arrayAccessedAt, l1, l2, suffix));
    for(auto sort : logic::Sorts::structSorts()){
      if(sort->name != arrayAccessedAt->sort()->name){
        conjuncts.push_back(logic::Theory::allSame(l1, l2, sort->name));
        sameAxiomsToAdd.insert(sort->name);
      }
    }
    if(suffix != ""){
      // just updated a memory object
      // variable values stay unchaged
      conjuncts.push_back(logic::Theory::allSame(l1, l2, "value"));
      sameAxiomsToAdd.insert("value");
    }

    return logic::Formulas::conjunction(
        conjuncts, "Update variable " + lhs->toString() + " at location " +
                       assignment->location);
  }
}

std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::IfElse* ifElse, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto lStart = startTimepointForStatement(ifElse);
  auto lEnd = endTimePointMap.at(ifElse);
  auto lLeftStart =
      startTimepointForStatement(ifElse->ifStatements.front().get());
  auto lRightStart =
      startTimepointForStatement(ifElse->elseStatements.front().get());

  if (util::Configuration::instance().inlineSemantics()) {
    // Part 1: visit start-location
    inliner.currTimepoint = lStart;
    auto f1 = inliner.handlePersistence(
        lStart, locationToActiveVars.at(lStart->symbol->name),
        "Define referenced terms denoting variable values at " +
            ifElse->location);
    conjuncts.push_back(f1);

    // Part 2: go through branches: collect all formulas describing semantics of
    // branches and assert them conditionally note: we need to generate
    // condition and negatedCondition here, since they depend on the state of
    // the inliner.
    auto condition = inliner.toCachedFormula(ifElse->condition);
    auto negatedCondition = logic::Formulas::negation(condition);

    std::vector<std::shared_ptr<const logic::Formula>> conjunctsLeft;
    std::vector<std::shared_ptr<const logic::Formula>> conjunctsRight;
    SemanticsInliner inlinerLeft(inliner);
    SemanticsInliner inlinerRight(inliner);

    for (const auto& statement : ifElse->ifStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inlinerLeft, trace);
      conjunctsLeft.push_back(semanticsOfStatement);
    }
    for (const auto& statement : ifElse->elseStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inlinerRight, trace);
      conjunctsRight.push_back(semanticsOfStatement);
    }

    // Part 3: define variable values at the merge of branches
    auto cachedIntVarValues = inliner.getCachedIntVarValues();
    auto cachedArrayVarTimepoints = inliner.getCachedArrayVarTimepoints();
    auto cachedIntVarValuesLeft = inlinerLeft.getCachedIntVarValues();
    auto cachedArrayVarTimepointsLeft =
        inlinerLeft.getCachedArrayVarTimepoints();
    auto cachedIntVarValuesRight = inlinerRight.getCachedIntVarValues();
    auto cachedArrayVarTimepointsRight =
        inlinerRight.getCachedArrayVarTimepoints();

    std::unordered_set<std::shared_ptr<const program::Variable>> mergeVars;
    for (const auto& pair : cachedIntVarValuesLeft) {
      auto var = pair.first;
      if (cachedIntVarValues.find(var) == cachedIntVarValues.end() ||
          *cachedIntVarValues[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }
    for (const auto& pair : cachedIntVarValuesRight) {
      auto var = pair.first;
      if (cachedIntVarValues.find(var) == cachedIntVarValues.end() ||
          *cachedIntVarValues[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }
    for (const auto& pair : cachedArrayVarTimepointsLeft) {
      auto var = pair.first;
      if (cachedArrayVarTimepoints.find(var) ==
              cachedArrayVarTimepoints.end() ||
          *cachedArrayVarTimepoints[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }
    for (const auto& pair : cachedArrayVarTimepointsRight) {
      auto var = pair.first;
      if (cachedArrayVarTimepoints.find(var) ==
              cachedArrayVarTimepoints.end() ||
          *cachedArrayVarTimepoints[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }

    for (const auto& var : mergeVars) {
      auto varLEnd = toTerm(var, lEnd, trace);

      // define the value of var at lEnd as the merge of values at the end of
      // the two branches
      conjunctsLeft.push_back(logic::Formulas::equalitySimp(
          varLEnd, inlinerLeft.toCachedTermFull(var)));
      conjunctsRight.push_back(logic::Formulas::equalitySimp(
          varLEnd, inlinerRight.toCachedTermFull(var)));

      // remember that lEnd is the last timepoint where var was set
      assert(!var->isConstant);
      if (var->isArray()) {
        inliner.setArrayVarTimepoint(var, lEnd);
      } else {
        auto result = inliner.setIntVarValue(var, varLEnd);
      }
    }

    conjuncts.push_back(logic::Formulas::implicationSimp(
        condition, logic::Formulas::conjunctionSimp(conjunctsLeft),
        "Semantics of left branch"));
    conjuncts.push_back(logic::Formulas::implicationSimp(
        negatedCondition, logic::Formulas::conjunctionSimp(conjunctsRight),
        "Semantics of right branch"));

    return logic::Formulas::conjunctionSimp(
        conjuncts, "Semantics of IfElse at location " + ifElse->location);
  } else {
    auto condition = toFormula(ifElse->condition, lStart, trace);
    auto negatedCondition = logic::Formulas::negation(condition);

    // Part 1: values at the beginning of any branch are the same as at the
    // beginning of the ifElse-statement don't need to take the intersection
    // with active vars at lLeftStart/lRightStart, since the active vars at
    // lStart are always a subset of those at lLeftStart/lRightStart
    auto activeVars = locationToActiveVars.at(lStart->symbol->name);
  
    addAllSameAxioms();
    auto implicationIfBranch = logic::Formulas::implication(
        condition, allVarEqual(lLeftStart, lStart, trace),
        "Jumping into the left branch doesn't change the variable values");
    auto implicationElseBranch = logic::Formulas::implication(
        negatedCondition, allVarEqual(lRightStart, lStart, trace),
        "Jumping into the right branch doesn't change the variable values");

    conjuncts.push_back(implicationIfBranch);
    conjuncts.push_back(implicationElseBranch);

    // Part 2: collect all formulas describing semantics of branches and assert
    // them conditionally
    for (const auto& statement : ifElse->ifStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inliner, trace);
      auto implication = logic::Formulas::implication(
          condition, semanticsOfStatement, "Semantics of left branch");
      conjuncts.push_back(implication);
    }

    for (const auto& statement : ifElse->elseStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inliner, trace);
      auto implication = logic::Formulas::implication(
          negatedCondition, semanticsOfStatement, "Semantics of right branch");
      conjuncts.push_back(implication);
    }

    return logic::Formulas::conjunction(
        conjuncts, "Semantics of IfElse at location " + ifElse->location);
  }
}

std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::WhileStatement* whileStatement, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

  auto itSymbol = iteratorSymbol(whileStatement);
  auto it = logic::Terms::var(itSymbol);
  auto n = lastIterationTermForLoop(whileStatement, numberOfTraces, trace);

  auto lStart0 =
      timepointForLoopStatement(whileStatement, logic::Theory::zero());
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(whileStatement, logic::Theory::succ(it));
  auto lStartN = timepointForLoopStatement(whileStatement, n);
  auto lBodyStartIt =
      startTimepointForStatement(whileStatement->bodyStatements.front().get());
  auto lEnd = endTimePointMap.at(whileStatement);

  auto posSymbol = posVarSymbol();
  auto pos = posVar();

  auto activeVars = locationToActiveVars.at(lStart0->symbol->name);

  if (util::Configuration::instance().inlineSemantics()) {
    auto assignedVars =
        AnalysisPreComputation::computeAssignedVars(whileStatement);
    // Part 0: custom persistence handling: handle all vars which 1) are active,
    // 2) keep the same value throughout the loop, 3) are non-const, and 4) are
    // persistent at the loop condition check note: condition 3) is a
    // requirement since otherwise the defining formulas could be unsound.
    // Condition 4) does not lead to incompleteness of the formalization, since
    // the value of variables, which change their value in the loop, will be
    // defined afterwards anyway.
    std::vector<std::shared_ptr<const program::Variable>> vars;
    for (const auto& var : activeVars) {
      if (assignedVars.find(var) == assignedVars.end() && !var->isConstant) {
        vars.push_back(var);
      }
    }
    auto f1 = inliner.handlePersistenceOfLoop(lStart0, lStartIt, vars);
    conjuncts.push_back(logic::Formulas::universalSimp(
        {itSymbol},
        logic::Formulas::implicationSimp(logic::Theory::lessEq(it, n), f1),
        "Define referenced terms denoting variable values at " +
            whileStatement->location));

    // Part 1: define values of assignedVars at iteration zero
    std::vector<std::shared_ptr<const logic::Formula>> conjPart1;

    inliner.currTimepoint = lStart0;
    for (const auto& var : assignedVars) {
      conjPart1.push_back(logic::Formulas::equalitySimp(
          toTerm(var, lStart0, trace), inliner.toCachedTermFull(var)));
    }

    conjuncts.push_back(logic::Formulas::conjunctionSimp(
        conjPart1, "Define variable values at beginning of loop"));

    // Part 2a: Loop condition holds at main-loop-location for all iterations
    // before n
    inliner.currTimepoint = lStartIt;
    for (const auto& var : assignedVars) {
      if (!var->isArray()) {
        assert(!var->isConstant);
        auto result = inliner.setIntVarValue(var, toTerm(var, lStartIt, trace));
      } else {
        inliner.setArrayVarTimepoint(var, lStartIt);
      }
    }

    conjuncts.push_back(logic::Formulas::universal(
        {itSymbol},
        logic::Formulas::implication(
            logic::Theory::less(it, n),
            inliner.toCachedFormula(whileStatement->condition)),
        "The loop-condition holds always before the last iteration"));

    // Extra part: collect in inlinedVarValues the values of all variables,
    // which occur in the loop condition but are not assigned to.
    inlinedVariableValues.initializeWhileStatement(whileStatement);
    std::unordered_set<std::shared_ptr<const program::Variable>>
        loopConditionVars;
    AnalysisPreComputation::computeVariablesContainedInLoopCondition(
        whileStatement->condition, loopConditionVars);

    for (const auto& var : loopConditionVars) {
      if (assignedVars.find(var) == assignedVars.end()) {
        if (var->isArray()) {
          inlinedVariableValues.setArrayTimepoint(
              whileStatement, var, trace,
              inliner.getCachedArrayVarTimepoints().at(var));
        } else {
          inlinedVariableValues.setValue(
              whileStatement, var, trace,
              inliner.getCachedIntVarValues().at(var));
        }
      }
    }

    // Part 3: collect all formulas describing semantics of the body, and define
    // values of assignedVars at all iterations s(it)
    assert(*inliner.currTimepoint == *lStartIt);

    std::vector<std::shared_ptr<const logic::Formula>> conjunctsBody;
    for (const auto& statement : whileStatement->bodyStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inliner, trace);
      conjunctsBody.push_back(semanticsOfStatement);
    }

    inliner.currTimepoint = lStartSuccOfIt;
    for (const auto& var : assignedVars) {
      conjunctsBody.push_back(logic::Formulas::equalitySimp(
          toTerm(var, lStartSuccOfIt, trace), inliner.toCachedTermFull(var),
          "Define value of variable " + var->name +
              " at beginning of next iteration"));
    }

    conjuncts.push_back(logic::Formulas::universalSimp(
        {itSymbol},
        logic::Formulas::implicationSimp(
            logic::Theory::less(it, n),
            logic::Formulas::conjunctionSimp(conjunctsBody)),
        "Semantics of the body"));

    // Part 4: define values of assignedVars after the execution of the loop
    inliner.currTimepoint = lStartN;
    for (const auto& var : assignedVars) {
      if (!var->isArray()) {
        assert(!var->isConstant);
        auto result = inliner.setIntVarValue(var, toTerm(var, lStartN, trace));
      } else {
        inliner.setArrayVarTimepoint(var, lStartN);
      }
    }

    // Part 2b: loop condition doesn't hold at n
    assert(*inliner.currTimepoint == *lStartN);
    conjuncts.push_back(logic::Formulas::negation(
        inliner.toCachedFormula(whileStatement->condition),
        "The loop-condition doesn't hold in the last iteration"));

    // for iterations of sort integer, assert last iteration nl >= 0
    if (util::Configuration::instance().integerIterations()) {
      conjuncts.push_back(logic::Theory::lessEq(
          logic::Theory::zero(), n,
          "The last iteration is >= 0 when of sort integer"));
    }

    return logic::Formulas::conjunctionSimp(
        conjuncts, "Loop at location " + whileStatement->location);
  } else {
    // Part 1: values at the beginning of body are the same as at the beginning
    // of the while-statement
    addAllSameAxioms();
    auto part1 = logic::Formulas::universal(
        {itSymbol},
        logic::Formulas::implication(
            logic::Theory::less(it, n),
            allVarEqual(lBodyStartIt, lStartIt, trace)),
        "Jumping into the loop body doesn't change the variable values");

    if (util::Configuration::instance().integerIterations()) {
      part1 = logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              allVarEqual(lBodyStartIt, lStartIt, trace)),
          "Jumping into the loop body doesn't change the variable values");
    }
    conjuncts.push_back(part1);

    // Part 2: collect all formulas describing semantics of body
    std::vector<std::shared_ptr<const logic::Formula>> conjunctsBody;
    for (const auto& statement : whileStatement->bodyStatements) {
      auto conjunct = generateSemantics(statement.get(), inliner, trace);
      conjunctsBody.push_back(conjunct);
    }
    auto bodySemantics = logic::Formulas::universal(
        {itSymbol},
        logic::Formulas::implication(
            logic::Theory::less(it, n),
            logic::Formulas::conjunction(conjunctsBody)),
        "Semantics of the body");

    if (util::Configuration::instance().integerIterations()) {
      bodySemantics = logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              logic::Formulas::conjunction(conjunctsBody)),
          "Semantics of the body");
    }
    conjuncts.push_back(bodySemantics);

    // Part 3: Define last iteration
    // Loop condition holds at main-loop-location for all iterations before n
    auto universal = logic::Formulas::universal(
        {itSymbol},
        logic::Formulas::implication(
            logic::Theory::less(it, n),
            toFormula(whileStatement->condition, lStartIt, trace)),
        "The loop-condition holds always before the last iteration");

    if (util::Configuration::instance().integerIterations()) {
      universal = logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              toFormula(whileStatement->condition, lStartIt, trace)),
          "The loop-condition holds always before the last iteration");
    }    
    conjuncts.push_back(universal);

    // loop condition doesn't hold at n
    auto negConditionAtN = logic::Formulas::negation(
        toFormula(whileStatement->condition, lStartN, trace),
        "The loop-condition doesn't hold in the last iteration");
    conjuncts.push_back(negConditionAtN);

    // Part 4: The values after the while-loop are the values from the timepoint
    // with location lStart and iteration n
    auto part4 = allVarEqual(lEnd, lStartN, trace,
                             "The values after the while-loop are the values "
                             "from the last iteration");
    conjuncts.push_back(part4);

    return logic::Formulas::conjunction(
        conjuncts, "Loop at location " + whileStatement->location);
  }
}

std::shared_ptr<const logic::Formula> Semantics::generateSemantics(
    const program::SkipStatement* skipStatement, SemanticsInliner& inliner,
    std::shared_ptr<const logic::Term> trace) {
  auto l1 = startTimepointForStatement(skipStatement);

  if (util::Configuration::instance().inlineSemantics()) {
    inliner.currTimepoint = l1;
    return inliner.handlePersistence(l1,
                                     locationToActiveVars.at(l1->symbol->name));
  } else {
    auto l2 = endTimePointMap.at(skipStatement);

    auto l1Name = l1->symbol->name;
    auto l2Name = l2->symbol->name;
    auto activeVars = intersection(locationToActiveVars.at(l1Name),
                                   locationToActiveVars.at(l2Name));
    auto varsGoingOutOfScope = 
      difference(locationToActiveVars.at(l1Name),
                 locationToActiveVars.at(l2Name));
   
    if(!varsGoingOutOfScope.empty()){
      auto locSymbol = locVarSymbol();
      auto loc = memLocVar();

      auto lhs2 = logic::Theory::valueAt(l2, loc);
      auto rhs2 = logic::Theory::valueAt(l1, loc);

      std::vector<std::shared_ptr<const logic::Formula>> disjs;
      std::vector<std::shared_ptr<const logic::Formula>> conjs;

      if(util::Configuration::instance().memSafetyMode()){
        for(auto var : varsGoingOutOfScope){
          auto f1 =
            logic::Formulas::equality(rhs2, logic::Terms::locConstant(var->name));
          auto f2 =
            logic::Formulas::disequality(rhs2, logic::Terms::locConstant(var->name));          
          disjs.push_back(f1);  
          conjs.push_back(f2);  
        }
      }

      std::vector<std::shared_ptr<const logic::Formula>> forms;
      if(util::Configuration::instance().memSafetyMode()){
        auto disjForm = logic::Formulas::disjunctionSimp(disjs);
        auto eq2 = logic::Formulas::equality(lhs2, logic::Theory::nullLoc());
        forms.push_back(logic::Formulas::implicationSimp(disjForm, eq2));
      }

      auto conjForm = logic::Formulas::conjunctionSimp(conjs);
      auto eq3 = logic::Formulas::equality(lhs2, rhs2);
      forms.push_back(logic::Formulas::implicationSimp(conjForm, eq3));

      auto conj = logic::Formulas::conjunctionSimp(forms);
      auto conjunct = logic::Formulas::universal({locSymbol}, conj, 
        "Pointer to vars going out of scope after skip set to point to null at " +
                         skipStatement->location);

      return conjunct;
    } else {

      // identify startTimePoint and endTimePoint
      auto eq = logic::Formulas::equality(l1, l2, "Ignore any skip statement");
      return eq;
    }
  }
}
}  // namespace analysis