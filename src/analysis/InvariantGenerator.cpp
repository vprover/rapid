#include "InvariantGenerator.hpp"

#include "Term.hpp"
#include "Theory.hpp"
#include "SemanticsHelper.hpp"

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
        if(_typed){
          auto type = rhs->exprType();
          auto childType = type->getChild();
          assert(childType->isStructType());
          auto structType = std::static_pointer_cast<const program::StructType>(childType);
          for(auto& field : structType->getFields()){
            std::vector<InvariantTask> rtVec;
            if(field->vt->isPointerToStruct()){
              std::string selectorName = toLower(structType->getName()) + "_" + field->name;
              auto trace = traceTerm(1);
              auto n = lastIterationTermForLoop(whileStatement, 1, trace);              
              auto blSym = Signature::varSymbol("bl", logic::Sorts::intSort());
              auto itSym = Signature::varSymbol("it", logic::Sorts::intSort());
              auto bl = Terms::var(blSym);
              auto it = Terms::var(itSym);       
              auto succBl = Theory::succ(bl);
              auto succIt = Theory::succ(it);                                   
              auto zeroLessBl = Theory::lessEq(Theory::zero(), bl);
              auto blLessIt = Theory::less(bl, it);
              auto blLessNl = Theory::less(bl, n);              
              auto itLessNl = Theory::less(it, n);
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

              auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
              freeVarSymbols.push_back(blSym);

              auto conclusion = 
                Formulas::universal(freeVarSymbols,
                  Formulas::implication(
                    Formulas::conjunctionSimp({zeroLessBl, blLessNl}), 
                      inductionHypothesis(n)));
              // TODO add "potential" to the name here, but remove it if proof found
              auto conclusionAx = std::make_shared<Axiom>(conclusion, 
                "Invariant of loop at location " + whileStatement->location);

              freeVarSymbols.push_back(itSym);

              auto lhsOfImp = Formulas::conjunctionSimp({zeroLessBl, blLessIt, itLessNl, inductionHypothesis(it)});
              auto rhsOfImp = inductionHypothesis(succIt);
              auto imp = Formulas::implication(lhsOfImp, rhsOfImp);
              auto toProve = Formulas::universal(freeVarSymbols, imp);
              
              auto stepCase = std::make_shared<Conjecture>(toProve);
              auto rt = new ReasoningTask({loopSemantics}, stepCase);
              rtVec.push_back(InvariantTask(rt, conclusionAx, whileStatement->location));
              _potentialInvariants.push_back(rtVec);
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

;      (forall ((it Int))
;         (=>
;            (and 
;               (<= 0 it)
;               (<= it nl22)
;            )
;            (= (value (l22 it) head) (next_chain head (l22 0) it))
;         )
;      ) 

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
      auto rhsIsFieldAccess = rhs->type == program::Type::FieldAccess;
      if(lhsIsVar && rhsIsFieldAccess){
        auto castedRhs = std::static_pointer_cast<const program::StructFieldAccess>(rhs);
        auto strct = castedRhs->getStruct();
        auto strctIsVar = strct->type() == program::Type::VariableAccess;
        if(strctIsVar){
          auto lhsAsVar = std::static_pointer_cast<const program::VariableAccess>(lhs);
          auto strctAsVar = std::static_pointer_cast<const program::StructFieldAccess>(strct);
          if(lhsAsVar == strctAsVar){
             // at this point we know that the statement is of the form
             // var = var->f for some field f
            auto freeVarSymbols = enclosingIteratorsSymbols(whileStatement);
            auto trace = traceTerm(1);
            auto n = lastIterationTermForLoop(whileStatement, 1, trace);    
            auto zero = Theory::zero();
            auto lStartZero = timepointForLoopStatement(whileStatement, zero);
            

            auto inductionHypothesis =
            [&](std::shared_ptr<const logic::Term> arg) {
              auto lStartArg = timepointForLoopStatement(whileStatement, arg);
              auto lhs = toTerm(lhs, lStartArg, trace);
              auto rhs = Theory::chain(selector, lStartZero, var);
              return Formulas::equality(lhs, rhs);
            }; 

          }
        }
      }
    }
  }
}

void InvariantGenerator::insertAxiomsIntoTasks(std::vector<std::shared_ptr<const Axiom>> items)
{
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){
      item.addAxioms(items);
      //item.outputSMTLIB(std::cout); 
    }
  }
}

void  InvariantGenerator::attemptToProveInvariants(){
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){

      std::cout << "Attempting to prove loop invariant:\n" << 
        "Potential invariant of loop at location " + item.loopLoc() << "\n" <<
        item.conclusion()->formula->prettyString() << std::endl;

      bool baseCaseProven = true;
      bool stepCaseProven = false;
      stepCaseProven = _solver.solveTask(*item.stepCase());
      if(item.baseCase()){
        baseCaseProven = _solver.solveTask(*item.baseCase());
      }
      if(stepCaseProven && baseCaseProven){
        std::cout << "Proof attempt successful!\n" << std::endl;
        item.setStatus(InvariantTask::Status::SOLVED);
        auto inv = item.conclusion();
        insertAxiomsIntoTasks({inv});
      } else {
        std::cout << "Proof attempt failed!\n" << std::endl;
        item.setStatus(InvariantTask::Status::FAILED);      
      }
    }
  }
}


}  // namespace analysis
