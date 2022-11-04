#include "InvariantGenerator.hpp"

#include "Term.hpp"
#include "Theory.hpp"
#include "SemanticsHelper.hpp"
#include "AnalysisPreComputation.hpp"

#include <set>

using namespace logic;

namespace analysis {

    
void InvariantTask::setStatus(Status status){ 
  _status = status; 
}


void InvariantGenerator::generateInvariants( 
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Formula> semantics)
{

  auto semanticsAxiom = std::make_shared<Axiom>(semantics);

  generatePointsToNullInvariants(whileStatement, semanticsAxiom);
  generateMallocInLoopInvariants(whileStatement, semanticsAxiom);
  if(_typed){
    generateStructsStaySameInvariants(whileStatement, semanticsAxiom);
  } 
  generateDenseInvariants(whileStatement, semanticsAxiom);
  // TODO in the untyped case we want to generate invariants over active mallocs
  // we should actually add such invariants as fall backs even in the typed case
  // as well
  generateChainingInvariants(whileStatement, semanticsAxiom);

  generateStaticVarInvariants(whileStatement, semanticsAxiom);
}

void InvariantGenerator::generatePointsToNullInvariants(      
      const program::WhileStatement* whileStatement,
      std::shared_ptr<const logic::Axiom> semantics)
{
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);     
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  
  for(auto& var : assignedVars){
    if(var->vt->isPointerToStruct()){
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

          auto [baseCase, stepCase, conclusion] = 
          inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                         inductionHypothesis, n ,freeVarSymbols); 

          auto conclusionInstance = 
            std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, inductionHypothesis(n)), 
            "Useful instance of above invariant");

          auto rtBase = new ReasoningTask({semantics}, baseCase);
          auto rtStep = new ReasoningTask({semantics}, stepCase);
          auto itl = InvariantTaskList(InvariantTaskList::ListType::SINGLETON,
            InvariantTask(rtBase, rtStep, {conclusion, conclusionInstance}, whileStatement->location));
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

  // try and prove invariant that after object malloced in a loop
  // from next iteration, it does not change
  for (const auto& statement : whileStatement->bodyStatements) {
        
    if(statement->type() == program::Statement::Type::Assignment){
      auto castedStatement = static_cast<const program::Assignment*>(statement.get());
      auto rhs = castedStatement->rhs;
      if(rhs->type() == program::Type::MallocFunc){

        auto trace = traceTerm(1);
        auto n = lastIterationTermForLoop(whileStatement, 1, trace); 
        auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);

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
                            inductionHypothesis2, 1, n ,freeVarSymbols); 

            auto [stepCase2, conclusion2] = 
            inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                            inductionHypothesis2, 2, n ,freeVarSymbols); 

            auto rt1 = new ReasoningTask({semantics}, stepCase1);
            auto rt2 = new ReasoningTask({semantics}, stepCase2);

            auto itl = InvariantTaskList(InvariantTaskList::ListType::CONTINUE_ON_FAILURE,
              InvariantTask(rt1, {conclusion1}, whileStatement->location, TaskType::MALLOC));
            itl.addTask(InvariantTask(rt2, {conclusion2}, whileStatement->location, TaskType::MALLOC));

            _potentialInvariants.push_back(itl);
          }
        }
        
        // TODO add untyped generation here
       
      }

    }
  }

}

void InvariantGenerator::generateStructsStaySameInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);    
  auto zero = Theory::zero();
  auto lStartZero = timepointForLoopStatement(whileStatement, zero);

  auto activeVars = _locationToActiveVars.at(lStartZero->symbol->name);
  std::vector<std::string> names;
  for(auto& v : activeVars){
    names.push_back(toSort(v->vt)->name);
  }

  auto structSorts = logic::Sorts::structSorts();
  for(auto& sort : structSorts){
    if(std::find(names.begin(), names.end(), sort->name) == names.end()){
      continue;
    }

    auto varName = logic::toLower(sort->name) + "_var";
    auto varSym = logic::Signature::varSymbol(varName, sort);
    auto var = Terms::var(varSym);

    freeVarSymbols.push_back(varSym);

    auto structSort = static_cast<logic::StructSort*>(sort);

    for(auto& selector : structSort->selectors()){
      auto inductionHypothesis =
      [&](std::shared_ptr<const logic::Term> arg) {
        auto lStartArg = timepointForLoopStatement(whileStatement, arg);
        auto lhs = Theory::selectorAt(selector, lStartArg, var);
        auto rhs = Theory::selectorAt(selector, lStartZero, var);
        return Formulas::equality(lhs, rhs);
      };   

      auto [baseCase, stepCase, conclusion] = 
      inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                     inductionHypothesis, n ,freeVarSymbols); 

      auto rt = new ReasoningTask({semantics}, stepCase);
      auto itl = InvariantTaskList(InvariantTaskList::ListType::SINGLETON,
        InvariantTask(rt, {conclusion}, whileStatement->location));
      _potentialInvariants.push_back(itl);      
    }
  
  }
}


void InvariantGenerator::generateDenseInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{

  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement);

  auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
  auto it = Terms::var(itSym); 

  auto trace = traceTerm(1);
  auto n = lastIterationTermForLoop(whileStatement, 1, trace);  

  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt = timepointForLoopStatement(whileStatement, Theory::succ(it));
  auto lStartZero = timepointForLoopStatement(whileStatement, Theory::zero());
  auto lStartN = timepointForLoopStatement(whileStatement, n);    
  auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);

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
            freeVarSymbols, logic::Formulas::implication(prem, conc));

      auto conclusionAx = std::make_shared<Axiom>(lemma, 
        "Invariant of loop at location " + loc);

      auto conjunctLeft = logic::Theory::lessEq(logic::Theory::zero(), it);


      auto denseFormula = 
         densityDefinition(left, itSym, it, lStartIt, lStartSuccOfIt, n, trace, lessThan);
      denseFormula = Formulas::universalSimp(freeVarSymbols, denseFormula);

      auto toProve = std::make_shared<Conjecture>(denseFormula);

      auto rt = new ReasoningTask({semantics}, toProve);

      auto itl = InvariantTaskList(InvariantTaskList::ListType::SINGLETON,
        InvariantTask(rt, {conclusionAx}, loc, TaskType::DENSE));
      _potentialInvariants.push_back(itl);     
    }
  }

  for (auto& v : assignedVars) { 
    // unlikely but possible that a constant is declared (and assigned) in a loop
    if(v->isConstant){ continue; }
    if(!v->isInt()){ continue; }

    auto varExpr = 
      std::shared_ptr<const program::VariableAccess>(new program::VariableAccess(v));
    auto varAtStart = toTerm(varExpr, lStartZero, trace);
    auto varAtIt    = toTerm(varExpr, lStartIt, trace);
    auto varAtEnd   = toTerm(varExpr, lStartN, trace);  

    
    auto addBounds = [&](std::shared_ptr<const logic::Formula> form){
      auto zeroLessIt = Theory::lessEq(Theory::zero(), it);
      auto itLessNl = Theory::lessEq(it,n);
      return Formulas::implication(
              Formulas::conjunctionSimp({zeroLessIt, itLessNl}), 
                form);
    };

    
    auto concIncreasing1 = addBounds(Formulas::equality(varAtIt,
      Theory::intAddition(varAtStart, it))); 
    auto concIncreasing2 = addBounds(Formulas::equality(n,
      Theory::intSubtraction(varAtEnd, varAtStart))); 

    auto concDecreasing1 = Formulas::equality(varAtIt,
      Theory::intSubtraction(varAtStart, it));
    auto concDecreasing2 = Formulas::equality(n,
      Theory::intSubtraction(varAtStart, varAtEnd)); 

    freeVarSymbols.push_back(itSym);
    auto ci1 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concIncreasing1), 
      "Invariant of loop at location " + loc);
    auto cd1 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concDecreasing1), 
      "Invariant of loop at location " + loc);
    freeVarSymbols.pop_back();

    auto ci2 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concIncreasing2), 
      "Useful instance of above invariant");
    auto cd2 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concDecreasing2), 
      "Useful instance of above invariant");

    auto stronglyDenseIncreasing = 
      densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, true, true);    
    auto stronglyDenseDecreasing = 
      densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, false, true);  

    auto toProveIncreasing = std::make_shared<Conjecture>(
      Formulas::universal(freeVarSymbols, stronglyDenseIncreasing));
    auto toProveDecreasing = std::make_shared<Conjecture>(
      Formulas::universal(freeVarSymbols, stronglyDenseDecreasing));

    auto rtIncreasing = new ReasoningTask({semantics}, toProveIncreasing);

     auto itl1 = InvariantTaskList(InvariantTaskList::ListType::SINGLETON,
      InvariantTask(rtIncreasing, {ci1, ci2}, loc, TaskType::DENSE));
    _potentialInvariants.push_back(itl1);  

    auto rt = new ReasoningTask({semantics}, toProveDecreasing);

     auto itl2 = InvariantTaskList(InvariantTaskList::ListType::CONTINUE_ON_FAILURE,
      InvariantTask(rt, {cd1, cd2} , loc, TaskType::DENSE));
    _potentialInvariants.push_back(itl2); 
  }

}


void InvariantGenerator::generateChainingInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> semantics)
{
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
            auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
            auto trace = traceTerm(1);
            auto n = lastIterationTermForLoop(whileStatement, 1, trace);    
            auto zero = Theory::zero();
            auto lStartZero = timepointForLoopStatement(whileStatement, zero);
            auto sort = toSort(lhsAsVar->var->vt);            

            auto selectorName = toLower(sort->name) + "_" + castedRhs->getField()->name;

            auto inductionHypothesis =
            [&](std::shared_ptr<const logic::Term> arg) {
              auto lStartArg = timepointForLoopStatement(whileStatement, arg);
              auto lhsTerm = toTerm(lhs, lStartArg, trace);
              auto rhsTerm = Theory::chain(selectorName, toTerm(lhsAsVar, lStartZero, trace), lStartArg, arg, sort->name);
              return Formulas::equality(lhsTerm, rhsTerm);
            }; 

            auto [baseCase1, stepCase1, conclusion1] = 
            inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                           inductionHypothesis, n ,freeVarSymbols); 

            auto conclusionInstance = 
              std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, inductionHypothesis(n)), 
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

            auto [stepCase2, conclusion2] = 
            inductionAxiom3("Invariant of loop at location " + whileStatement->location,
                            inductionHypothesis2, 0, n ,freeVarSymbols); 

            auto [stepCase3, conclusion3] = 
            inductionAxiom4("Invariant of loop at location " + whileStatement->location,
                            inductionHypothesis2, n ,freeVarSymbols); 
         
            /*auto [bCase, inductiveCase, helperLemma] =
              logic::Theory::chainAxioms(selectorName, sort->name);*/

            auto rt1 = new ReasoningTask({semantics/*, bCase, inductiveCase, helperLemma*/}, stepCase1);
            auto rt2 = new ReasoningTask({semantics}, stepCase2);
            auto rt3 = new ReasoningTask({semantics}, stepCase3);

            auto itl = InvariantTaskList(InvariantTaskList::ListType::CONTINUE_ON_SUCCESS,
              InvariantTask(rt1, {conclusion1, conclusionInstance}, 
              whileStatement->location, TaskType::CHAINY /* add chainy axioms here if we really want */));
            itl.addTask(InvariantTask(rt2, {conclusion2}, whileStatement->location, TaskType::CHAINY));
            itl.addTask(InvariantTask(rt3, {conclusion3}, whileStatement->location, TaskType::CHAINY));

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
  freeVarSymbols.push_back(itSym);

  auto zeroLessEqIt = Theory::lessEq(Theory::zero(), it);
  auto itLessNlTerm = Theory::less(it, n);

  auto activeVars = _locationToActiveVars.at(lStart0->symbol->name);
  auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement, true);

  auto loc = whileStatement->location;

  auto inAssignedVars = [&](std::string varName){
    for(auto& var : assignedVars){
      if(varName == var->name){
        return true;
      }
    }
    return false;
  };


  for(auto& var : activeVars){
    // TODO, potentially a variable is assigned within a loop,
    // but still stays constant. We ignore that possibility for
    // now
    if(!inAssignedVars(var->name) && !var->isConstant){
 
      auto varAtStart = toTerm(var, lStart0, trace);
      auto varAtIt = toTerm(var, lStartIt, trace);
      auto varAtSuccIt = toTerm(var, lStartSuccOfIt, trace);
      auto varAtEnd = toTerm(var, lStartN, trace);

      auto stepCase = Formulas::universal(freeVarSymbols, 
          Formulas::implication(
            Formulas::conjunctionSimp({zeroLessEqIt, itLessNlTerm}),
            Formulas::equality(varAtIt, varAtSuccIt)
          )
        );

      auto formula = Formulas::equality(varAtStart, varAtEnd);
      auto toProve = std::make_shared<Conjecture>(stepCase);

      auto conclusionAx = std::make_shared<Axiom>(formula, 
        "Invariant of loop at location " + loc);

      auto rt = new ReasoningTask({semantics}, toProve);

      auto itl = InvariantTaskList(InvariantTaskList::ListType::SINGLETON,
        InvariantTask(rt, {conclusionAx}, loc, TaskType::OTHER));
      _potentialInvariants.push_back(itl); 
    }
  }

}

void InvariantGenerator::insertAxiomsIntoTasks(
  std::vector<std::shared_ptr<const Axiom>> items, 
  std::string location)
{
  for(auto& invList : _potentialInvariants){
    
    auto& item = invList.mainTask();
    if(location.empty() || (item.loopLoc() == location))
        item.addAxioms(items);

    for(auto& item : invList.fallBackTasks()){
      if(location.empty() || (item.loopLoc() == location))
        item.addAxioms(items);
    }
  }
}

std::vector<std::shared_ptr<const logic::Axiom>>
InvariantGenerator::getProvenInvariantsAndAxioms() 
{
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  std::set<std::string> chainDefsAdded;

  for(auto& invList : _potentialInvariants){
    for(auto& invTask : invList.allTasks()){
      if(invTask.status() == InvariantTask::Status::SOLVED){
        for(auto& conc : invTask.conclusions()){
          axioms.push_back(conc);          
        }
        /*if(item.isChainyTask()){
          for(auto& ax : item.getChainAxioms()){
            auto axName = ax->name;
            if(chainDefsAdded.find(axName) == chainDefsAdded.end()){
              chainDefsAdded.insert(axName);
              axioms.push_back(ax);
            }
          }
        }*/     
      }
    }
  }
  for(auto& ax : _supportAxioms){
    axioms.push_back(ax);
  }
  return axioms;  
}

bool InvariantGenerator::attemptToProveInvariant(InvariantTask& item){

  std::cout << "Attempting to prove " << 
    "formula below holds for loop at location " + item.loopLoc() << "\n\n" <<
    item.conclusions()[0]->formula->prettyString() << "\n" << std::endl;

  auto& solver = solvers::VampireSolver::instance();
  bool baseCaseProven = true;
  bool stepCaseProven = false;

  if(item.baseCase()){
    std::cout << "Attempting to prove step case" << std::endl;
  }

  stepCaseProven = solver.solveTask(*item.stepCase(), item.taskType());
  if(item.baseCase()){
    std::cout << "Attempting to prove base case" << std::endl;        
    baseCaseProven = solver.solveTask(*item.baseCase(), item.taskType());
  }
  if(stepCaseProven && baseCaseProven){
    std::cout << "Proof attempt successful!" << std::endl;
    std::cout << "---------------------------------------------------------------------\n" << std::endl;
    item.setStatus(InvariantTask::Status::SOLVED);
    insertAxiomsIntoTasks(item.conclusions(), item.loopLoc());
    return true;
  }

  std::cout << "Proof attempt failed!" << std::endl;
  if(item.baseCase() && !stepCaseProven){
    std::cout << "Could not prove step case" << std::endl;        
  }
  if(item.baseCase() && !baseCaseProven){
    std::cout << "Could not prove base case" << std::endl;        
  }
  std::cout << "---------------------------------------------------------------------\n" << std::endl;
  item.setStatus(InvariantTask::Status::FAILED); 
  return false;

}

void  InvariantGenerator::attemptToProveInvariants(){

  std::cout << "#### Status: ##### Stengthening semantics with loop invariants" << std::endl;

  for(auto& invList : _potentialInvariants){

    auto& item = invList.mainTask();
  
    bool proved = attemptToProveInvariant(item);

    if(( proved && invList.continueOnSuccess()) || 
       (!proved && invList.continueOnFailure())){
      
      for(auto& task : invList.fallBackTasks()){
        attemptToProveInvariant(task);
      }  

    }
  }
}

}  // namespace analysis
