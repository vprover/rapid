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
    std::shared_ptr<const logic::Formula> loopSemantics)
{

  auto loopSemanticsAxiom = std::make_shared<Axiom>(loopSemantics);

  generateMallocInLoopInvariants(whileStatement, loopSemanticsAxiom);
  if(_typed){
    generateStructsStaySameInvariants(whileStatement, loopSemanticsAxiom);
  } 
  generateDenseInvariants(whileStatement, loopSemanticsAxiom);
  // TODO in the untyped case we want to generate invariants over active mallocs
  // we should actually add such invariants as fall backs even in the typed case
  // as well
  generateChainingInvariants(whileStatement, loopSemanticsAxiom);
}

void InvariantGenerator::generateMallocInLoopInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> loopSemantics)
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
        auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
        auto it = Terms::var(itSym);       
        auto itLessNl = Theory::less(it, n);
        auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
        freeVarSymbols.push_back(itSym);

        if(_typed){
          auto type = rhs->exprType();
          auto childType = type->getChild();
          assert(childType->isStructType());
          auto structType = std::static_pointer_cast<const program::StructType>(childType);
          for(auto& field : structType->getFields()){
            std::vector<InvariantTask> rtVec;
            if(field->vt->isPointerToStruct()){
              std::string selectorName = toLower(structType->getName()) + "_" + field->name;
              auto blSym = Signature::varSymbol("bl", logic::Sorts::intSort());
              auto bl = Terms::var(blSym);
              auto succBl = Theory::succ(bl);
              auto succIt = Theory::succ(it);                                   
              auto zeroLessBl = Theory::lessEq(Theory::zero(), bl);
              auto blLessIt = Theory::less(bl, it);
              auto blLessNl = Theory::less(bl, n);              
              auto tp = timepointForNonLoopStatement(castedStatement, bl);
              auto mallocTerm = toTerm(rhs, tp, trace);

              auto inductionHypothesis =
              [&](std::shared_ptr<const logic::Term> arg) {
                auto lStartArg = timepointForLoopStatement(whileStatement, arg);
                auto lStartSuccBl = timepointForLoopStatement(whileStatement, succBl);
                auto lhs = Theory::selectorAt(selectorName, lStartSuccBl, mallocTerm);
                auto rhs = Theory::selectorAt(selectorName, lStartArg, mallocTerm);
                return Formulas::equality(lhs, rhs);
              };

              freeVarSymbols.push_back(blSym);

              auto conclusion = 
                Formulas::universal(freeVarSymbols,
                  Formulas::implication(
                    Formulas::conjunctionSimp({zeroLessBl, blLessNl}), 
                      inductionHypothesis(n)));
              // TODO add "potential" to the name here, but remove it if proof found
              auto conclusionAx = std::make_shared<Axiom>(conclusion, 
                "Invariant of loop at location " + whileStatement->location);

              auto lhsOfImp = Formulas::conjunctionSimp({zeroLessBl, blLessIt, itLessNl, inductionHypothesis(it)});
              auto rhsOfImp = inductionHypothesis(succIt);
              auto imp = Formulas::implication(lhsOfImp, rhsOfImp);
              auto toProve = Formulas::universal(freeVarSymbols, imp);
              
              auto stepCase = std::make_shared<Conjecture>(toProve);
              auto rt = new ReasoningTask({loopSemantics}, stepCase);
              rtVec.push_back(InvariantTask(rt, conclusionAx, whileStatement->location));
              _potentialInvariants.push_back(rtVec);
              freeVarSymbols.pop_back();
            }
          }
        }

        // for mallocs within a loop, we add an axiom
        // stating that the returned location is fresh and cannot
        // be in the support of any chains at the start of the loop
        for(auto sort : logic::Sorts::structSorts()){
          auto rhsSort = toSort(rhs->exprType());
          if(sort->name == rhsSort->name){
            auto structSort = static_cast<logic::StructSort*>(sort);
            for(auto& recSelName : structSort->recursiveSelectors()){
              auto startTp = timepointForLoopStatement(whileStatement, it);
              auto tp = timepointForNonLoopStatement(castedStatement, it);
              auto mallocTerm = toTerm(rhs, tp, trace);   
              auto osym = Signature::varSymbol("o", rhsSort);
              auto lsym = Signature::varSymbol("chain_len", Sorts::intSort());

              auto ovar = logic::Terms::var(osym); 
              auto len = logic::Terms::var(lsym);  

              auto notInSup = Formulas::negation(
                Theory::inChainSupport(recSelName, startTp, mallocTerm, ovar, len));

              auto bounds = Formulas::conjunction({
                Theory::lessEq(Theory::zero(), it),
                  itLessNl});

              freeVarSymbols.push_back(osym);
              freeVarSymbols.push_back(lsym);
              auto formula = Formulas::universal(freeVarSymbols, 
                Formulas::implication(bounds, notInSup));
              _supportAxioms.push_back(std::make_shared<Axiom>(formula, "Malloc returns fresh location"));
            }  
          }
        }
        
        // TODO add untyped generation here
       
      }

    }
  }

}

void InvariantGenerator::generateStructsStaySameInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> loopSemantics)
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
      std::vector<InvariantTask> rtVec;    
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

      auto rt = new ReasoningTask({loopSemantics}, stepCase);
      rtVec.push_back(InvariantTask(rt, conclusion, whileStatement->location));
      _potentialInvariants.push_back(rtVec);      
    }
  
  }
}


void InvariantGenerator::generateDenseInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> loopSemantics)
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
    if (condCasted->kind != program::ArithmeticComparison::Kind::EQ) {
      auto left = condCasted->child1;
      auto right = condCasted->child2;
      if (AnalysisPreComputation::doNotOccurIn(assignedVars, right)) {
        // Right is constant through the loop. 
        // This is a cheap way of statically dsicovering this.
        // A better method would be to make this a part of the proof obligation 

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

        std::vector<InvariantTask> rtVec; 
        auto rt = new ReasoningTask({loopSemantics}, toProve);
  
        rtVec.push_back(InvariantTask(rt, conclusionAx, loc, TaskType::DENSE));
        _potentialInvariants.push_back(rtVec);     
      }
    }
  }

  for (auto& v : assignedVars) { 
    // unlikely but possible that a constant is declared (and assigned) in a loop
    if(v->isConstant){ continue; }
    if(!v->isInt()){ continue; }

    auto varExpr = 
      std::shared_ptr<const program::VariableAccess>(new program::VariableAccess(v));
    auto varAtStart = toTerm(varExpr, lStartZero, trace);
    auto varAtEnd = toTerm(varExpr, lStartN, trace);   
    auto concIncreasing = Formulas::equality(n,
      Theory::intSubtraction(varAtEnd, varAtStart)); 
    auto concDecreasing = Formulas::equality(n,
      Theory::intSubtraction(varAtStart, varAtEnd)); 

    auto c1 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concIncreasing), 
      "Invariant of loop at location " + loc);
    auto c2 = std::make_shared<Axiom>(Formulas::universal(freeVarSymbols, concDecreasing), 
      "Invariant of loop at location " + loc);

    auto stronglyDenseIncreasing = 
      densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, true, true);    
    auto stronglyDenseDecreasing = 
      densityDefinition(varExpr, itSym, it, lStartIt, lStartSuccOfIt, n, trace, false, true);  

    auto toProveIncreasing = std::make_shared<Conjecture>(
      Formulas::universal(freeVarSymbols, stronglyDenseIncreasing));
    auto toProveDecreasing = std::make_shared<Conjecture>(
      Formulas::universal(freeVarSymbols, stronglyDenseDecreasing));

    std::vector<InvariantTask> rtVecIncreasing; 
    auto rtIncreasing = new ReasoningTask({loopSemantics}, toProveIncreasing);

    rtVecIncreasing.push_back(InvariantTask(rtIncreasing, c1, loc, TaskType::DENSE));
    _potentialInvariants.push_back(rtVecIncreasing);  

    std::vector<InvariantTask> rtVec; 
    auto rt = new ReasoningTask({loopSemantics}, toProveDecreasing);

    rtVec.push_back(InvariantTask(rt, c2, loc, TaskType::DENSE));
    _potentialInvariants.push_back(rtVec); 
  }

}


void InvariantGenerator::generateChainingInvariants(      
  const program::WhileStatement* whileStatement,
  std::shared_ptr<const logic::Axiom> loopSemantics)
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
            std::vector<InvariantTask> rtVec;    
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
              auto rhsTerm = Theory::chain(selectorName, toTerm(lhsAsVar, lStartZero, trace), lStartZero, arg, sort->name);
              return Formulas::equality(lhsTerm, rhsTerm);
            }; 

            auto [baseCase, stepCase, conclusion] = 
            inductionAxiom0("Invariant of loop at location " + whileStatement->location,
                           inductionHypothesis, n ,freeVarSymbols); 

            auto [bCase, inductiveCase, helperLemma] =
              logic::Theory::chainAxioms(selectorName, sort->name);

            auto rt = new ReasoningTask({loopSemantics, bCase, inductiveCase, helperLemma}, stepCase);
            rtVec.push_back(InvariantTask(rt, conclusion, whileStatement->location,
             TaskType::CHAINY, {bCase, inductiveCase, helperLemma}));
            _potentialInvariants.push_back(rtVec);      
          }
        }
      }
    }
  }
}

void InvariantGenerator::insertAxiomsIntoTasks(
  std::vector<std::shared_ptr<const Axiom>> items, 
  std::string location)
{
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){
      if(location.empty() || (item.loopLoc() == location))
        item.addAxioms(items);
      //item.outputSMTLIB(std::cout); 
    }
  }
}

std::vector<std::shared_ptr<const logic::Axiom>>
InvariantGenerator::getProvenInvariantsAndAxioms() 
{
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  std::set<std::string> chainDefsAdded;

  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){
      if(item.status() == InvariantTask::Status::SOLVED){
        axioms.push_back(item.conclusion());
        if(item.isChainyTask()){
          for(auto& ax : item.getChainAxioms()){
            auto axName = ax->name;
            if(chainDefsAdded.find(axName) == chainDefsAdded.end()){
              chainDefsAdded.insert(axName);
              axioms.push_back(ax);
            }
          }
        }      
      }
    }
  }
  for(auto& ax : _supportAxioms){
    axioms.push_back(ax);
  }
  return axioms;  
}

void  InvariantGenerator::attemptToProveInvariants(){
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){

      std::cout << "Attempting to prove " << 
        "formula below holds for loop at location " + item.loopLoc() << "\n\n" <<
        item.conclusion()->formula->prettyString() << "\n" << std::endl;

      auto& solver = solvers::VampireSolver::instance();
      bool baseCaseProven = true;
      bool stepCaseProven = false;
      stepCaseProven = solver.solveTask(*item.stepCase(), item.taskType());
      if(item.baseCase()){
        baseCaseProven = solver.solveTask(*item.baseCase(), item.taskType());
      }
      if(stepCaseProven && baseCaseProven){
        std::cout << "Proof attempt successful!" << std::endl;
        std::cout << "---------------------------------------------------------------------\n" << std::endl;
        item.setStatus(InvariantTask::Status::SOLVED);
        auto inv = item.conclusion();
        insertAxiomsIntoTasks({inv}, item.loopLoc());
        break; // from inner for. No need to proceed to less general invariants.
      } else {
        std::cout << "Proof attempt failed!" << std::endl;
        std::cout << "---------------------------------------------------------------------\n" << std::endl;
        item.setStatus(InvariantTask::Status::FAILED);      
      }
    }
  }
}

}  // namespace analysis
