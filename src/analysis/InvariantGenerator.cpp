#include "InvariantGenerator.hpp"

#include "Term.hpp"
#include "Theory.hpp"
#include "SemanticsHelper.hpp"
#include "AnalysisPreComputation.hpp"

#include "Output.hpp"

#include <set>

using namespace logic;

namespace analysis {

    
void InvariantTask::setStatus(Status status){ 
  _status = status; 
}

void InvariantTask::removeStandardConclusion(){
  assert(_conclusions.size() == 3);
  _conclusions.erase(_conclusions.begin());
}

void InvariantTask::removeVariantConclusion(){
  assert(_conclusions.size() == 3);
  _conclusions.erase(_conclusions.begin() + 1);
}

void InvariantGenerator::generateInvariants( 
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Formula> semantics)
{

  _chainsSameProved.clear();

  auto semanticsAxiom = std::make_shared<Axiom>(semantics);

  generateStaticVarInvariants(whileStatement, semanticsAxiom);
  generateDenseInvariants(whileStatement, semanticsAxiom);

  generatePointsToNullInvariants(whileStatement, semanticsAxiom);
  if(_typed){
    generateStructsStaySameInvariants(whileStatement, semanticsAxiom);
  } 
  generateMallocInLoopInvariants(whileStatement, semanticsAxiom);
  // TODO in the untyped case we want to generate invariants over active mallocs
  // we should actually add such invariants as fall backs even in the typed case
  // as well
  generateChainingInvariants(whileStatement, semanticsAxiom);

}

void InvariantGenerator::generatePointsToNullInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics)
{

  auto lStart0 = timepointForLoopStatement(whileStatement, Theory::zero());

  auto activeVars = _locationToActiveVars.at(lStart0->symbol->name);  
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);     
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);

  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  for(auto& var : activeVars){
    if(assignedVars.contains(var) && var->vt->isPointerToStruct()){
      auto childType = var->vt->getChild();
      assert(childType->isStructType());      
      auto structType = std::static_pointer_cast<const program::StructType>(childType);
      for(auto& field : structType->getFields()){
        if(field->vt->isPointerToStruct()){

          std::string structSortName = structType->getName();
          std::string selectorName = toLower(structSortName) + "_" + field->name;

          auto trace = traceTerm(1);
          auto n = lastIterationTermForLoop(whileStatement, 1, trace); 

          auto nullTerm = Theory::nullLoc(structSortName);

          auto inductionHypothesis =
          [&](std::shared_ptr<const logic::Term> arg) {
            auto lStartArg = timepointForLoopStatement(whileStatement, arg);
            auto lhs = Theory::selectorAt(selectorName, lStartArg, toTerm(var, lStartArg, trace));
            return Formulas::equality(lhs, nullTerm);
          };

          auto [baseCase, stepCase, conclusion, concVariant] = 
          inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                         inductionHypothesis, n ,freeVarSymbols, boundsFromEnclosingLoops); 

          auto conclusionInstance = 
            std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, 
              Formulas::implicationSimp(
                boundsFromEnclosingLoops,
                inductionHypothesis(n))), 
            "Useful instance of above invariant");

          auto rtBase = new ReasoningTask({semantics}, baseCase);
          auto rtStep = new ReasoningTask({semantics}, stepCase);

          InvariantTaskList itl(TaskType::OTHER);
          itl.addTask(InvariantTask(rtBase, rtStep, {conclusion, conclusionInstance}, whileStatement->location));
          _potentialInvariants.push_back(itl);  
        }
      }
    }
  }

}

void InvariantGenerator::generateMallocInLoopInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{

  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);

  auto lStartZero = timepointForLoopStatement(whileStatement, Theory::zero());

  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace); 

  bool loopContainsMalloc = false;

  // try and prove invariant that after object malloced in a loop
  // from next iteration, it does not change
  for (const auto& statement : whileStatement->bodyStatements) {
        
    if(statement->type() == program::Statement::Type::Assignment){
      auto castedStatement = static_cast<const program::Assignment*>(statement.get());
      auto rhs = castedStatement->rhs;
      if(rhs->type() == program::Type::MallocFunc){

        loopContainsMalloc = true;

        if(_typed){
          auto type = rhs->exprType();
          auto childType = type->getChild();
          assert(childType->isStructType());
          auto structType = std::static_pointer_cast<const program::StructType>(childType);
          for(auto& field : structType->getFields()){
            std::string selectorName = toLower(structType->getName()) + "_" + field->name;

            auto inductionHypothesis2 =
            [&](std::shared_ptr<const logic::Term> arg1, 
                std::shared_ptr<const logic::Term> arg2) {
              auto asFuncTerm = std::static_pointer_cast<const logic::FuncTerm>(arg1);

              auto lStartArg1 = timepointForLoopStatement(whileStatement, arg1);
              auto lStartArg2 = timepointForLoopStatement(whileStatement, arg2);  
              auto lStartBl = timepointForNonLoopStatement(castedStatement, asFuncTerm->subterms[0]);

              // really dirty hack here as want malloc(l15(bl)) and not
              // malloc(l15(bl + 2)) or malloc(l15(bl + 1))
              auto mallocTerm = toTerm(rhs, lStartBl, trace);           

              auto lhs = Theory::selectorAt(selectorName, lStartArg1, mallocTerm);
              auto rhs = Theory::selectorAt(selectorName, lStartArg2, mallocTerm);
              return Formulas::equality(lhs, rhs);
            };  
 
            auto [stepCase1, conclusion1] = 
            inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                            inductionHypothesis2, 1, n ,freeVarSymbols,boundsFromEnclosingLoops); 

            auto [stepCase2, conclusion2] = 
            inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                            inductionHypothesis2, 2, n ,freeVarSymbols,boundsFromEnclosingLoops); 

            auto rt1 = new ReasoningTask({semantics}, stepCase1);
            auto rt2 = new ReasoningTask({semantics}, stepCase2);

            InvariantTaskList itl(TaskType::MALLOC); 
            itl.addTask(InvariantTask(rt1, {conclusion1}, whileStatement->location, TaskType::MALLOC));
            itl.addTask(InvariantTask(rt2, {conclusion2}, whileStatement->location, TaskType::MALLOC));

            _potentialInvariants.push_back(itl);
          }
        }
        
        // TODO add untyped generation here
       
      }

    }
  }


  if(!loopContainsMalloc){
    auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);
    auto assignedFields = AnalysisPreComputation::computeAssignedFields(whileStatement);

    // TODO it is not clear that we really want assigned vars here
    // perhaps we want all variables that hold pointer to structs which have some field
    // modified. E.g. if code is f->next = ... then try and prove something about f...
    for(auto& var : assignedVars){
      // what about if it is a struct itself?
      if(var->vt->isPointerToStruct()){
        auto varSort = toSort(var->vt);
        assert(varSort->isStructSort());
        auto structSort = static_cast<logic::StructSort*>(varSort);

        if(assignedFields.contains(varSort->name)){
          auto modifiedFields = assignedFields[varSort->name];

          for(auto& sel : structSort->selectors()){
            
            if(modifiedFields.contains(sel)){

              auto inductionHypothesis =
              [&](std::shared_ptr<const logic::Term> arg1, 
                  std::shared_ptr<const logic::Term> arg2) {
                auto asFuncTerm = std::static_pointer_cast<const logic::FuncTerm>(arg1);

                auto lStartArg1 = timepointForLoopStatement(whileStatement, arg1);
                auto lStartArg2 = timepointForLoopStatement(whileStatement, arg2);  

                auto term = toTerm(var, lStartArg1, trace);           

                auto lhs = Theory::selectorAt(sel, lStartArg1, term);
                auto rhs = Theory::selectorAt(sel, lStartArg2, term);
                return Formulas::equality(lhs, rhs);
              };  
   
              auto [stepCase1, conclusion1] = 
              inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                              inductionHypothesis, 1, n ,freeVarSymbols,boundsFromEnclosingLoops); 


             // std::cout << stepCase1->formula->prettyString() << std::endl;
             // std::cout << conclusion1->formula->prettyString() << std::endl;

              auto rt1 = new ReasoningTask({semantics}, stepCase1);

              InvariantTaskList itl(TaskType::STAY_SAME); 
              itl.addTask(InvariantTask(rt1, {conclusion1}, whileStatement->location, TaskType::STAY_SAME));

              _potentialInvariants.push_back(itl);
            }
          }
        }
      }
    }

  }


}

void InvariantGenerator::generateStructsStaySameInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);
  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);    

  auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
  auto it = Terms::var(itSym); 
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartZero = timepointForLoopStatement(whileStatement, Theory::zero());

  auto assignedFields = AnalysisPreComputation::computeAssignedFields(whileStatement);

  auto activeVars = _locationToActiveVars.at(lStartZero->symbol->name);
  std::vector<Sort*> sorts;
  for(auto& v : activeVars){
    sorts.push_back(toSort(v->vt));
  }

  auto addBounds = [&](std::shared_ptr<const logic::Formula> form){
    return 
    Formulas::implicationSimp(
      Formulas::conjunctionSimp({
        boundsFromEnclosingLoops,
        Theory::lessEq(Theory::zero(), it),
        Theory::lessEq(it,n)
      }), 
      form
    );
  };

  auto structSorts = logic::Sorts::structSorts();
  for(auto& sort : structSorts){

    auto structSort = static_cast<logic::StructSort*>(sort);
    
    std::vector<std::shared_ptr<const logic::Axiom>> axioms;

    freeVarSymbols.push_back(itSym);

    if(!assignedFields.contains(sort->name)){
      // no variable of this struct sort is changed in the loop
      auto same = Theory::allSame(lStartZero, lStartIt,sort->name);
      axioms.push_back(std::make_shared<logic::Axiom>(
        Formulas::universal(freeVarSymbols, addBounds(same))));

      for(auto sel : structSort->recursiveSelectors()){
        same = Theory::allSame(lStartZero, lStartIt, sel + "_chain");
        axioms.push_back(std::make_shared<logic::Axiom>(
          Formulas::universal(freeVarSymbols, addBounds(same))));
        _chainsSameProved.insert(sel);
      }

    } else {

      auto modifiedFields = assignedFields[sort->name];

      for(auto& field : structSort->selectors()){
        if(!modifiedFields.contains(field)){
          auto varName = logic::toLower(sort->name) + "_var";
          auto varSym = logic::Signature::varSymbol(varName, sort);
          auto var = Terms::var(varSym);

          freeVarSymbols.push_back(varSym);
       
          auto lhs = Theory::selectorAt(field, lStartZero, var);
          auto rhs = Theory::selectorAt(field, lStartIt, var);
          auto same = Formulas::equality(lhs,rhs);
          axioms.push_back(std::make_shared<logic::Axiom>(
            Formulas::universal(freeVarSymbols, addBounds(same))));

          freeVarSymbols.pop_back();
        }
      }

      for(auto sel : structSort->recursiveSelectors()){
        if(!modifiedFields.contains(sel)){
          auto same = Theory::allSame(lStartZero, lStartIt, sel + "_chain");
          axioms.push_back(std::make_shared<logic::Axiom>(
            Formulas::universal(freeVarSymbols, addBounds(same))));
          _chainsSameProved.insert(sel);
        }
      } 
    }

    InvariantTaskList itl(TaskType::OTHER);
    itl.addTask(InvariantTask(axioms, whileStatement->location));

    _potentialInvariants.push_back(itl);
  }
}


void InvariantGenerator::generateDenseInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{


  auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
  auto it = Terms::var(itSym); 

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);  

  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt = timepointForLoopStatement(whileStatement, Theory::succ(it));
  auto lStartZero = timepointForLoopStatement(whileStatement, Theory::zero());
  auto lStartN = timepointForLoopStatement(whileStatement, n);    

  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);
  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  auto activeVars = _locationToActiveVars.at(lStartZero->symbol->name);
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement);

  auto loc = whileStatement->location;

  auto cond = whileStatement->condition;
  if (cond->type() == program::BoolExpression::Type::ArithmeticComparison) {

    auto condCasted =
        std::static_pointer_cast<const program::ArithmeticComparison>(cond);
    auto left = condCasted->child1;
    auto right = condCasted->child2;
    if (AnalysisPreComputation::doNotOccurIn(assignedVars, right)) {
      // Right is constant through the loop. 
      // This is a cheap way of statically dsicovering this.
      // A better method would be to make this a part of the proof obligation 

      // TODO, the above is unsafe in the presence of pointers...!

      auto newLeft = toTerm(left, lStartZero, trace);
      auto newRight = toTerm(right, lStartZero, trace);

      auto conc = logic::Formulas::equality(
        toTerm(left, lStartN, trace), 
          toTerm(right, lStartN, trace));

      auto op = condCasted->kind;
      bool lessThan = false;

      switch (op) {
        case program::ArithmeticComparison::Kind::LT: {
          lessThan = true;
          break;
        }

        case program::ArithmeticComparison::Kind::LE: {
          lessThan = true;
          auto one = Theory::intConstant(1);
          newRight = Theory::intAddition(newRight, one);
          break;
        }

        case program::ArithmeticComparison::Kind::GT: {
          break;
        }

        default: {
          // the equality case should never occur
          auto one = Theory::intConstant(1);
          newRight = Theory::intSubtraction(newRight, one);
          break;
        }
      }
      
      auto prem =
          lessThan ? Theory::lessEq(newLeft, newRight)
                   : Theory::intGreaterEqual(newLeft, newRight);
      
      auto lemma = logic::Formulas::universal(
            freeVarSymbols, 
              Formulas::implicationSimp(
                boundsFromEnclosingLoops,
                logic::Formulas::implication(prem, conc)));

      auto conclusionAx = std::make_shared<Axiom>(lemma, 
        "Invariant of loop at location " + loc);

      auto denseFormula = 
         densityDefinition(left, itSym, it, lStartIt, lStartSuccOfIt, n, trace, boundsFromEnclosingLoops, lessThan);
      denseFormula = Formulas::universalSimp(freeVarSymbols, denseFormula);

      auto toProve = std::make_shared<Conjecture>(denseFormula);

      auto rt = new ReasoningTask({semantics}, toProve);

      InvariantTaskList itl(TaskType::DENSE1);
      itl.addTask(InvariantTask(rt, {conclusionAx}, loc, TaskType::DENSE1));
      _potentialInvariants.push_back(itl);     
    }
  }

  for (auto& v : activeVars) {
    if(assignedVars.contains(v) && !v->isConstant && v->isInt()){ 
      // unlikely but possible that a constant is declared (and assigned) in a loop

      auto varExpr = 
        std::shared_ptr<const program::VariableAccess>(new program::VariableAccess(v));
      auto varAtStart = toTerm(varExpr, lStartZero, trace);
      auto varAtIt    = toTerm(varExpr, lStartIt, trace);
      auto varAtEnd   = toTerm(varExpr, lStartN, trace);  

      
      auto addBounds = [&](std::shared_ptr<const logic::Formula> form){
        auto zeroLessIt = Theory::lessEq(Theory::zero(), it);
        auto itLessNl = Theory::lessEq(it,n);
        return Formulas::implication(
                Formulas::conjunctionSimp({boundsFromEnclosingLoops, zeroLessIt, itLessNl}), 
                  form);
      };

      
      auto concIncreasing1 = addBounds(Formulas::equality(varAtIt,
        Theory::intAddition(varAtStart, it))); 
      auto concIncreasing2 = Formulas::equality(n,
        Theory::intSubtraction(varAtEnd, varAtStart)); 

      auto concDecreasing1 = addBounds(Formulas::equality(varAtIt,
        Theory::intSubtraction(varAtStart, it)));
      auto concDecreasing2 = Formulas::equality(n,
        Theory::intSubtraction(varAtStart, varAtEnd)); 

      freeVarSymbols.push_back(itSym);
      auto ci1 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concIncreasing1), 
        "Invariant of loop at location " + loc);
      auto cd1 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concDecreasing1), 
        "Invariant of loop at location " + loc);
      freeVarSymbols.pop_back();

      auto ci2 = 
        std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, 
          Formulas::implicationSimp(
            boundsFromEnclosingLoops,
            concIncreasing2)), 
        "Useful instance of above invariant");

      auto cd2 = 
        std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, 
          Formulas::implicationSimp(
            boundsFromEnclosingLoops,
            concDecreasing2)), 
        "Useful instance of above invariant");

      auto stronglyDenseIncreasing = 
        densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, boundsFromEnclosingLoops, true, true);    
      auto stronglyDenseDecreasing = 
        densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, boundsFromEnclosingLoops, false, true);  

      auto toProveIncreasing = std::make_shared<Conjecture>(
        Formulas::universal(freeVarSymbols, stronglyDenseIncreasing));
      auto toProveDecreasing = std::make_shared<Conjecture>(
        Formulas::universal(freeVarSymbols, stronglyDenseDecreasing));

      auto rtIncreasing = new ReasoningTask({semantics}, toProveIncreasing);
      auto rtDecreasing = new ReasoningTask({semantics}, toProveDecreasing);

      InvariantTaskList itl(TaskType::DENSE2);
      itl.addTask(InvariantTask(rtIncreasing, {ci1, ci2}, loc, TaskType::DENSE2));
      itl.addTask(InvariantTask(rtDecreasing, {cd1, cd2}, loc, TaskType::DENSE2));
      _potentialInvariants.push_back(itl);  
    }
  }

}


void InvariantGenerator::generateChainingInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{

  auto lStartZero = timepointForLoopStatement(whileStatement, Theory::zero());

  auto activeVars = _locationToActiveVars.at(lStartZero->symbol->name);
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);

  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);
  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);    


  // two different types of chaining invariants that we attempt to prove
  // type 1:
  // chain(...) = null

  for(auto& v : activeVars){
    if(assignedVars.contains(v)){
      auto sort = toSort(v->vt);
      if(sort->isStructSort()){
        auto structSort = static_cast<logic::StructSort*>(sort);
        for(auto& selector : structSort->recursiveSelectors()){

          auto nullTerm = Theory::nullLoc(structSort->name);

          auto inductionHypothesis =
          [&](std::shared_ptr<const logic::Term> arg) {
            auto lStartArg = timepointForLoopStatement(whileStatement, arg);
            auto lhs = Theory::chain(selector, toTerm(v, lStartArg, trace), lStartArg, arg, sort->name);
            return Formulas::equality(lhs, nullTerm);
          };

          // custom base case, so we ignore the base case coming from inductionAxiom0
          auto baseCase = std::make_shared<logic::Conjecture>(
            Formulas::universal(freeVarSymbols, 
              Formulas::equality(toTerm(v, lStartZero, trace), nullTerm)));

          auto [baseCase1, stepCase1, conclusion1, concVariant] = 
            inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                           inductionHypothesis, n ,freeVarSymbols, boundsFromEnclosingLoops); 

          auto conclusionInstance = 
            std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, 
              Formulas::implicationSimp(
                boundsFromEnclosingLoops,
                inductionHypothesis(n))), 
            "Useful instance of above invariant");

          //TODO add forward chain equality here as well?

          auto rtBase = new ReasoningTask({semantics}, baseCase);
          auto rtStep = new ReasoningTask({semantics}, stepCase1);

          InvariantTaskList itl(TaskType::OTHER); // TODO fix logic here. If we set to chainy, expects 3 tasks
          itl.addTask(InvariantTask(rtBase, rtStep, {conclusion1, conclusionInstance}, 
            whileStatement->location, TaskType::CHAINY2));                     
          _potentialInvariants.push_back(itl);  
        }
      }
    }
  }
  
  // type 2 as described in .hpp file

  for (const auto& statement : whileStatement->bodyStatements) {
        
    if(statement->type() == program::Statement::Type::Assignment){
      auto castedStatement = static_cast<const program::Assignment*>(statement.get());
      auto lhs = castedStatement->lhs;
      auto rhs = castedStatement->rhs;
      auto lhsIsVar = lhs->type() == program::Type::VariableAccess;
      auto rhsIsFieldAccess = rhs->type() == program::Type::FieldAccess;
      
      if(lhsIsVar && rhsIsFieldAccess){
        auto castedRhs = std::static_pointer_cast<const program::StructFieldAccess>(rhs);
        auto strct = castedRhs->getStruct();
        auto strctIsVar = strct->type() == program::Type::VariableAccess;
        
        if(strctIsVar){
          auto lhsAsVar = std::static_pointer_cast<const program::VariableAccess>(lhs);
          auto strctAsVar = std::static_pointer_cast<const program::VariableAccess>(strct);
          
          if(lhsAsVar->var == strctAsVar->var){
             // at this point we know that the statement is of the form
             // var = var->f for some field f
            auto sort = toSort(lhsAsVar->var->vt);            

            auto selectorName = toLower(sort->name) + "_" + castedRhs->getField()->name;

            auto inductionHypothesis =
            [&](std::shared_ptr<const logic::Term> arg) {
              auto lStartArg = timepointForLoopStatement(whileStatement, arg);
              auto lhsTerm = toTerm(lhs, lStartArg, trace);
              auto rhsTerm = Theory::chain(selectorName, toTerm(lhsAsVar, lStartZero, trace), lStartArg, arg, sort->name);
              return Formulas::equality(lhsTerm, rhsTerm);
            }; 

            auto [baseCase1, stepCase1, conclusion1, concVariant] = 
            inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                           inductionHypothesis, n ,freeVarSymbols, boundsFromEnclosingLoops); 

            auto conclusionInstance = 
              std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, 
                Formulas::implicationSimp(
                  boundsFromEnclosingLoops,
                  inductionHypothesis(n))), 
              "Useful instance of above invariant");

            auto inductionHypothesis2 =
            [&](std::shared_ptr<const logic::Term> arg1, 
                std::shared_ptr<const logic::Term> arg2) {
              auto lStartArg1 = timepointForLoopStatement(whileStatement, arg1);
              auto lStartArg2 = timepointForLoopStatement(whileStatement, arg2);              
              auto lhsTerm = Theory::chain(selectorName, toTerm(lhsAsVar, lStartZero, trace), lStartArg1, arg1, sort->name);
              auto rhsTerm = Theory::chain(selectorName, toTerm(lhsAsVar, lStartZero, trace), lStartArg2, arg1, sort->name);
              return Formulas::equality(lhsTerm, rhsTerm);
            };            

            auto rt1 = new ReasoningTask({semantics}, stepCase1);

            InvariantTaskList itl(TaskType::CHAINY1); 
            if(!_chainsSameProved.contains(selectorName)){
              itl.addTask(InvariantTask(rt1, {conclusion1, concVariant, conclusionInstance}, 
                whileStatement->location, TaskType::CHAINY1));     
            } else {
              itl.addTask(InvariantTask(rt1, {conclusion1, conclusionInstance}, 
                whileStatement->location, TaskType::CHAINY1));  
            }

            // if set includes the select name,
            // means we have been able to show that all chains
            // stay the same over the loop statically. No need to prove it 
            if(!_chainsSameProved.contains(selectorName)){
              auto [stepCase2, conclusion2] = 
              inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                              inductionHypothesis2, 0, n ,freeVarSymbols, boundsFromEnclosingLoops); 
              auto rt2 = new ReasoningTask({semantics}, stepCase2);
              itl.addTask(InvariantTask(rt2, {conclusion2}, whileStatement->location, TaskType::CHAINY1));
            }

            _potentialInvariants.push_back(itl);      
          }
        }
      }
    }
  }
}

void  InvariantGenerator::generateStaticVarInvariants(
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{

  auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
  auto it = Terms::var(itSym); 

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);  

  auto lStart0 = timepointForLoopStatement(whileStatement, Theory::zero());
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt = timepointForLoopStatement(whileStatement, Theory::succ(it));
  auto lStartN = timepointForLoopStatement(whileStatement, n);
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto enclosingLastIterationTs = enclosingLastIterationTerms(whileStatement);
  auto boundsFromEnclosingLoops = createBoundsForEnclosingLoops(freeVarSymbols, enclosingLastIterationTs);

  auto zeroLessEqIt = Theory::lessEq(Theory::zero(), it);
  auto itLessNlTerm = Theory::less(it, n);
  auto itLessEqNlTerm = Theory::lessEq(it, n);

  auto activeVars = _locationToActiveVars.at(lStart0->symbol->name);
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);

  auto loc = whileStatement->location;

  for(auto& var : activeVars){
    // TODO, potentially a variable is assigned within a loop,
    // but still stays constant. We ignore that possibility for
    // now
    if(!assignedVars.contains(var) && !var->isConstant){
 
      freeVarSymbols.push_back(itSym);

      auto varAtStart = toTerm(var, lStart0, trace);
      auto varAtIt = toTerm(var, lStartIt, trace);
      auto varAtSuccIt = toTerm(var, lStartSuccOfIt, trace);
      auto varAtEnd = toTerm(var, lStartN, trace);

      auto stepCase = Formulas::universal(freeVarSymbols, 
          Formulas::implication(
            Formulas::conjunctionSimp({boundsFromEnclosingLoops,zeroLessEqIt, itLessNlTerm}),
            Formulas::equality(varAtIt, varAtSuccIt)
          )
        );
      
      auto formula = 
        Formulas::universal(freeVarSymbols,
          Formulas::implicationSimp(
            Formulas::conjunctionSimp({boundsFromEnclosingLoops,zeroLessEqIt, itLessEqNlTerm}),
            Formulas::equality(varAtStart, varAtIt)));

      freeVarSymbols.pop_back();

      auto formulaInstance = 
        Formulas::universal(freeVarSymbols,
          Formulas::implicationSimp(
            boundsFromEnclosingLoops,
            Formulas::equality(varAtStart, varAtEnd)));

      auto toProve = std::make_shared<Conjecture>(stepCase);

      auto conclusion = std::make_shared<Axiom>(formula, 
        "Invariant of loop at location " + loc);

      auto conclusionInstance = std::make_shared<Axiom>(formulaInstance, 
        "Useful instance of above invariant");

      auto rt = new ReasoningTask({semantics}, toProve);

      InvariantTaskList itl(TaskType::STATIC_VAR);
      itl.addTask(InvariantTask(rt, {conclusion, conclusionInstance}, loc, TaskType::STATIC_VAR));
      _potentialInvariants.push_back(itl); 
    }
  }

}

void InvariantGenerator::insertAxiomsIntoTasks(
  std::vector<std::shared_ptr<const Axiom>> items, 
  std::string location)
{
  for(auto& invList : _potentialInvariants){

    for(auto& task : invList.tasks()){
//      if(location.empty() || (task.loopLoc() == location))
// TODO - much optimisation that could be carried out here
// we don't really want to insert axioms into the reasoning tasks
// of every other loop. This is likely to just harm performance without helping
// yet, we do need these axioms in some circumstances
        task.addAxioms(items);
    }
  }
}

std::vector<std::shared_ptr<const logic::Axiom>>
InvariantGenerator::getProvenInvariantsAndAxioms() 
{
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  std::set<std::string> chainDefsAdded;

  for(auto& invList : _potentialInvariants){
    for(auto& invTask : invList.tasks()){
      if(invTask.status() == InvariantTask::Status::SOLVED){
        for(auto& conc : invTask.conclusions()){
          axioms.push_back(conc);          
        }    
      }
    }
  }
  /*for(auto& ax : _supportAxioms){
    axioms.push_back(ax);
  }*/
  return axioms;  
}

bool InvariantGenerator::attemptToProveInvariant(InvariantTask& item){

  // a set of conclusions that we could derive statically
  // add cinclusions to other tasks and return
  if(!item.baseCase() && !item.stepCase()){
    item.setStatus(InvariantTask::Status::SOLVED);
    insertAxiomsIntoTasks(item.conclusions(), item.loopLoc());
    return true;
  }

  std::cout << "Attempting to prove " << 
    "formula below holds for loop at location " + item.loopLoc() << "\n\n" <<
    item.conclusions()[0]->formula->prettyString() << "\n" << std::endl;

  auto& solver = solvers::VampireSolver::instance();
  bool baseCaseProven = true;
  std::string timeBase;

  if(item.baseCase()){
    std::cout << "Attempting to prove step case" << std::endl;
  }
  auto [stepCaseProven, timeStep] = solver.solveTask(*item.stepCase(), item.taskType());
  if(stepCaseProven)
    std::cout << "Proof attempt successful in " + timeStep << std::endl;
  else
    std::cout << "Proof attempt failed!" << std::endl;

  // no point trying to prove base case if we already failed to prove step case
  if(item.baseCase() && stepCaseProven){
    std::cout << "Attempting to prove base case" << std::endl;        
    std::tie(baseCaseProven, timeBase) = solver.solveTask(*item.baseCase(), item.taskType());
    if(baseCaseProven)
      std::cout << "Proof attempt successful in " + timeBase << std::endl;  
    else
      std::cout << "Proof attempt failed!" << std::endl;        
  }
  if(stepCaseProven && baseCaseProven){
    std::cout << "Formula proven to be a loop invariant! " << std::endl;
    std::cout << "---------------------------------------------------------------------\n" << std::endl;
    item.setStatus(InvariantTask::Status::SOLVED);
    insertAxiomsIntoTasks(item.conclusions(), item.loopLoc());
    return true;
  }

  std::cout << "---------------------------------------------------------------------\n" << std::endl;
  item.setStatus(InvariantTask::Status::FAILED); 
  return false;

}

void  InvariantGenerator::attemptToProveInvariants(){

  util::Output::status("Stengthening semantics with loop invariants");

  for(auto& invList : _potentialInvariants){

    switch(invList.taskType()){
      case TaskType::CHAINY1:{
        auto& task1 = invList.tasks()[0];
        if(attemptToProveInvariant(task1) && invList.tasks().size() == 2){
          auto& forwardTask = invList.tasks()[1];
          attemptToProveInvariant(forwardTask);
          task1.removeStandardConclusion();
        }
        break;
      }
      case TaskType::MALLOC:
      case TaskType::DENSE2:      
      {
        assert(invList.tasks().size() == 2);
        auto& task1 = invList.tasks()[0];
        if(!attemptToProveInvariant(task1)){
          auto& task2 = invList.tasks()[1];
          attemptToProveInvariant(task2);
        }
        break;
      }
      case TaskType::DENSE1:
      case TaskType::STATIC_VAR:
      case TaskType::STAY_SAME:
      case TaskType::OTHER: {
        assert(invList.tasks().size() == 1);
        auto& task = invList.tasks()[0];
        attemptToProveInvariant(task);
        break;
      }
      default:
        assert(false);
    }
  }
}

}  // namespace analysis
