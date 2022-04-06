#include "InvariantGenerator.hpp"

#include "Term.hpp"
#include "Theory.hpp"
#include "SemanticsHelper.hpp"
#include "SolverInterface.hpp"

using namespace logic;

namespace analysis {

void InvariantGenerator::generateInvariants( 
    const program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Formula> loopSemantics)
{

  auto loopSemanticsAxiom = std::make_shared<Axiom>(loopSemantics);

  // try and prove invariant that after object malloced in a loop
  // from next iteration, it does not change
  for (const auto& statement : whileStatement->bodyStatements) {
    
    std::vector<ReasoningTask> rtVec;
    
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
              freeVarSymbols.push_back(itSym);

              auto lhsOfImp = Formulas::conjunctionSimp({zeroLessBl, blLessIt, itLessNl, inductionHypothesis(it)});
              auto rhsOfImp = inductionHypothesis(succIt);
              auto imp = Formulas::implication(lhsOfImp, rhsOfImp);
              auto toProve = Formulas::universal(freeVarSymbols, imp);
              
              auto conjecture = std::make_shared<Conjecture>(toProve);
              rtVec.push_back(ReasoningTask({loopSemanticsAxiom}, conjecture));
              _potentialInvariants.push_back(rtVec);
            }
          }


        }
        
        // TODO add untyped generation here
       
      }

    }
  }



}

void InvariantGenerator::insertAxiomsIntoTasks(std::vector<std::shared_ptr<const Axiom>> items)
{
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){
      item.addAxioms(items);
      item.outputSMTLIB(std::cout);
    }
  }
}

void  InvariantGenerator::attemptToProveInvariants(){
  for(auto& vec : _potentialInvariants){
    for(auto& item : vec){
      auto solver = solvers::VampireSolver(item);
      solver.setTimeLimit(30);
      if(solver.solve()){
        item.status = ReasoningTask::Status::SOLVED;
        auto conj = item.conjecture;
        auto inv = std::make_shared<Axiom>(conj->formula);
        insertAxiomsIntoTasks({inv});
      } else {
        item.status = ReasoningTask::Status::FAILED;        
      }
    }
  }
}


}  // namespace analysis
