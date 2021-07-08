#include "SemanticsHelper.hpp"

#include <cassert>

#include "Variable.hpp"
#include "Term.hpp"
#include "Theory.hpp"

#include "SymbolDeclarations.hpp"

namespace analysis {

    typedef std::shared_ptr<const program::Variable> programVar;

    bool getDiff(programVar v, const program::Statement* s, int& diff, bool topLevel)
    {
        //basic first attempt type of thing. Lots of potential to expand
        //here, but not sure how helpful it would be.

        auto isVarV = [](programVar v, std::shared_ptr<const program::Expression> e)
        {
            if(e->type() == program::Type::IntOrNatVariableAccess)
            {
                auto castedExpr = std::static_pointer_cast<const program::IntOrNatVariableAccess>(e);
                return castedExpr->var == v;
            }
            return false;
        };

        auto isIntConstant = [](std::shared_ptr<const program::Expression> e)
        {
            return e->type() == program::Type::ArithmeticConstant;
        };

        auto getIntConstant = [](std::shared_ptr<const program::Expression> e)
        {
            auto castedExpr = std::static_pointer_cast<const program::ArithmeticConstant>(e);
            return castedExpr->value;
        };
   

        if (s->type() == program::Statement::Type::Assignment)
        {
            auto castedStatement = static_cast<const program::Assignment*>(s);
            
            if(isVarV(v, castedStatement->lhs)){
                //v = rhs
                auto rhs = castedStatement->rhs;
                if(rhs->type() == program::Type::Addition)
                {
                    auto castedAdd = std::static_pointer_cast<const program::Addition>(rhs);
                    auto summand1 = castedAdd->summand1;
                    auto summand2 = castedAdd->summand2;
                    if(isVarV(v, summand1) && isIntConstant(summand2)) {
                        diff = diff + getIntConstant(summand2);
                        return true;
                    } else if (isVarV(v, summand2) && isIntConstant(summand1)) {
                        diff = diff + getIntConstant(summand1);
                        return true;
                    }
                } else if (rhs->type() == program::Type::Subtraction){
                    auto castedSub = std::static_pointer_cast<const program::Subtraction>(rhs);
                    auto child1 = castedSub->child1;
                    auto child2 = castedSub->child2;
                    if(isVarV(v, child1) && isIntConstant(child2)) {
                        diff = diff - getIntConstant(child2);
                        return true;
                    }
                }
                return false;
            }
            //updates some other variable
            return true;
        }
        else if (s->type() == program::Statement::Type::IfElse)
        {
            auto castedStatement = static_cast<const program::IfElse*>(s);

            int diff1 = 0;
            int diff2 = 0;
            for (auto statement : castedStatement->ifStatements){
               bool canCalculate = getDiff(v, statement.get(), diff1, false);
               if(!canCalculate) return false;
            }

            for (auto statement : castedStatement->elseStatements){
               bool canCalculate = getDiff(v, statement.get(), diff2, false);
               if(!canCalculate) return false;
            }
            if(diff1 != diff2){
                return false;
            }
            diff = diff + diff1;
            return true;            
        }
        else if (s->type() == program::Statement::Type::WhileStatement)
        {
            auto castedStatement = static_cast<const program::WhileStatement*>(s);
            
            int diff1 = 0;
            for (auto statement : castedStatement->bodyStatements){
               bool canCalculate = getDiff(v, statement.get(), diff1, false);
               if(!canCalculate || (diff1 != 0 && !topLevel)) return false;
            }
            diff = diff + diff1;
            return true;
        }
        else
        {
            assert(s->type() == program::Statement::Type::SkipStatement);
            diff = diff + 0;
            return true;
        }      
    }

# pragma mark - Methods for generating most used variables

    std::shared_ptr<const logic::LVariable> posVar()
    {
        return logic::Terms::var(posVarSymbol());
    }

    std::shared_ptr<const logic::LVariable> locVar()
    {
        return logic::Terms::var(locationSymbol("tp",0));
    }

    std::shared_ptr<const logic::LVariable> memLocVar()
    {
        return logic::Terms::var(locVarSymbol());
    }

# pragma mark - Methods for generating most used trace terms
    
    std::shared_ptr<const logic::Term> traceTerm(unsigned traceNumber)
    {
        return logic::Terms::func(traceSymbol(traceNumber), {});
    }

    std::vector<std::shared_ptr<const logic::Term>> traceTerms(unsigned numberOfTraces)
    {
         std::vector<std::shared_ptr<const logic::Term>> traces;
        for (unsigned traceNumber = 1; traceNumber < numberOfTraces+1; traceNumber++)
        {
            traces.push_back(traceTerm(traceNumber));
        }
        return traces;
    }


# pragma mark - Methods for generating most used timepoint terms and symbols
    
    std::shared_ptr<const logic::LVariable> iteratorTermForLoop(const program::WhileStatement* whileStatement)
    {
        assert(whileStatement != nullptr);
        
        return logic::Terms::var(iteratorSymbol(whileStatement));
    }
    
    std::shared_ptr<const logic::Term> lastIterationTermForLoop(const program::WhileStatement* whileStatement, unsigned numberOfTraces, std::shared_ptr<const logic::Term> trace)
    {
        assert(whileStatement != nullptr);
        assert(trace != nullptr);

        auto symbol = lastIterationSymbol(whileStatement, numberOfTraces);
        std::vector<std::shared_ptr<const logic::Term>> subterms;
        for (const auto& loop : *whileStatement->enclosingLoops)
        {
            subterms.push_back(iteratorTermForLoop(loop));
        }
        if (numberOfTraces > 1)
        {
            subterms.push_back(trace);
        }
        return logic::Terms::func(symbol, subterms);
    }
    
    std::shared_ptr<const logic::Term> timepointForNonLoopStatement(const program::Statement* statement)
    {
        assert(statement != nullptr);
        assert(statement->type() != program::Statement::Type::WhileStatement);
        
        auto enclosingLoops = *statement->enclosingLoops;
        auto enclosingIteratorTerms = std::vector<std::shared_ptr<const logic::Term>>();
        for (const auto& enclosingLoop : enclosingLoops)
        {
            auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
            enclosingIteratorTerms.push_back(logic::Terms::var(enclosingIteratorSymbol));
        }

        return logic::Terms::func(locationSymbolForStatement(statement), enclosingIteratorTerms);
    }
    
    std::shared_ptr<const logic::Term> timepointForLoopStatement(const program::WhileStatement* whileStatement, std::shared_ptr<const logic::Term> innerIteration)
    {
        assert(whileStatement != nullptr);
        assert(innerIteration != nullptr);
        
        auto enclosingLoops = *whileStatement->enclosingLoops;
        auto enclosingIteratorTerms = std::vector<std::shared_ptr<const logic::Term>>();
        for (const auto& enclosingLoop : enclosingLoops)
        {
            auto enclosingIteratorSymbol = iteratorSymbol(enclosingLoop);
            enclosingIteratorTerms.push_back(logic::Terms::var(enclosingIteratorSymbol));
        }
        enclosingIteratorTerms.push_back(innerIteration);
        return logic::Terms::func(locationSymbolForStatement(whileStatement), enclosingIteratorTerms);
    }

    std::shared_ptr<const logic::Term> startTimepointForStatement(const program::Statement* statement)
    {
        if (statement->type() != program::Statement::Type::WhileStatement)
        {
            return timepointForNonLoopStatement(statement);
        }
        else
        {
            auto whileStatement = static_cast<const program::WhileStatement*>(statement);
            return timepointForLoopStatement(whileStatement, logic::Theory::natZero());
        }
    }
    
    std::vector<std::shared_ptr<const logic::Symbol>> enclosingIteratorsSymbols(const program::Statement* statement)
    {
        auto enclosingIteratorsSymbols = std::vector<std::shared_ptr<const logic::Symbol>>();
        for (const auto& enclosingLoop : *statement->enclosingLoops)
        {
            enclosingIteratorsSymbols.push_back(iteratorSymbol(enclosingLoop));
        }
        return enclosingIteratorsSymbols;
    }

    
# pragma mark - Methods for generating most used terms/predicates denoting program-expressions
    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::Expression> expr, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace, bool lhsOfAssignment)
    {
        assert(expr != nullptr);
        assert(timePoint != nullptr);
        
        switch (expr->type())
        {
            case program::Type::ArithmeticConstant:
            case program::Type::Addition:
            case program::Type::Subtraction:
            case program::Type::Modulo:
            case program::Type::Multiplication:
            case program::Type::IntOrNatVariableAccess:
            case program::Type::IntArrayApplication:
            case program::Type::Pointer2IntDeref:
            {
                auto castedExpr = std::static_pointer_cast<const program::IntExpression>(expr);
                return toTerm(castedExpr, timePoint, trace, lhsOfAssignment);
            }
            case program::Type::PointerVariableAccess:
            {
                auto castedExpr = std::static_pointer_cast<const program::PointerVariableAccess>(expr);
                return toTerm(castedExpr->var, timePoint, trace);                
            }                       
            case program::Type::Pointer2PointerDeref:
            {
                auto castedExpr = std::static_pointer_cast<const program::DerefP2PExpression>(expr);
                return toTerm(castedExpr, timePoint, trace);                
            } 
        }
        assert(false);
        //to silence compiler warnings, but we should never reach here
        return toTerm(expr, timePoint, trace);
    }

    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::IntArrayApplication> app, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace)
    {
        auto array = toTerm(app->array, timePoint, trace);
        auto index = toTerm(app->index, timePoint, trace);
        return logic::Terms::arraySelect(array, index);
    }

    //TODO code duplication with the next two functions. Look into changing to a 
    //diamond hierarchy. 
    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::DerefP2IExpression> e, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace)
    {
        std::shared_ptr<const logic::Term> exprToTerm;
        //the expression being dereferenced
        auto expr = e->expr;
        if(expr->type() == program::Type::PointerVariableAccess){
           exprToTerm = logic::Terms::locConstant(expr->toString());
        } else {
           assert(expr->type() == program::Type::Pointer2PointerDeref);
           auto castedExpr = std::static_pointer_cast<const program::DerefP2PExpression>(expr);
           exprToTerm = toTerm(castedExpr, timePoint, trace);
        }
        return logic::Theory::valueAtInt(timePoint, logic::Theory::deref(timePoint, exprToTerm));
    }

    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::DerefP2PExpression> e, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace)
    {
        std::shared_ptr<const logic::Term> exprToTerm;
        //the expression being dereferenced
        auto expr = e->expr;
        if(expr->type() == program::Type::PointerVariableAccess){
           exprToTerm = logic::Terms::locConstant(expr->toString());
        } else {
           assert(expr->type() == program::Type::Pointer2PointerDeref);
           auto castedExpr = std::static_pointer_cast<const program::DerefP2PExpression>(expr);
           exprToTerm = toTerm(castedExpr, timePoint, trace);
        }
        return logic::Theory::deref(timePoint, exprToTerm);
    }


    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::Variable> var, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace)
    {
        assert(var != nullptr);
        assert(trace != nullptr);
                
    //    if (!var->isConstant)
    //    {
        assert(timePoint != nullptr);
    //    arguments.push_back(timePoint);

        auto varAsConst = logic::Terms::func(logic::Signature::fetch(var->name),{});

        if(var->isPointer()){ 
            return logic::Theory::deref(timePoint, varAsConst);
        } else if(var->isArray()){
            if(var->isConstant){
                return logic::Theory::valueAtConstArray(varAsConst);
            } else {    
                return logic::Theory::valueAtArray(timePoint, varAsConst);
            }
        }
        if(var->isConstant){
            return logic::Theory::valueAtConstInt(varAsConst);
        } else {    
            return logic::Theory::valueAtInt(timePoint, varAsConst);
        }        
    }
    
    std::shared_ptr<const logic::Term> toTerm(std::shared_ptr<const program::IntExpression> expr, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace, bool lhsOfAssignment)
    {
        assert(expr != nullptr);
        assert(timePoint != nullptr);
        
        switch (expr->type())
        {
            case program::Type::ArithmeticConstant:
            {
                auto castedExpr = std::static_pointer_cast<const program::ArithmeticConstant>(expr);
                return logic::Theory::intConstant(castedExpr->value);
            }
            case program::Type::Addition:
            {
                auto castedExpr = std::static_pointer_cast<const program::Addition>(expr);
                return logic::Theory::intAddition(toTerm(castedExpr->summand1, timePoint, trace), toTerm(castedExpr->summand2, timePoint, trace));
            }
            case program::Type::Subtraction:
            {
                auto castedExpr = std::static_pointer_cast<const program::Subtraction>(expr);
                return logic::Theory::intSubtraction(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
            }
            case program::Type::Modulo:
            {
                auto castedExpr = std::static_pointer_cast<const program::Modulo>(expr);
                return logic::Theory::intModulo(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
            }
            case program::Type::Multiplication:
            {
                auto castedExpr = std::static_pointer_cast<const program::Multiplication>(expr);
                return logic::Theory::intMultiplication(toTerm(castedExpr->factor1, timePoint, trace), toTerm(castedExpr->factor2, timePoint, trace));
            }
            case program::Type::IntOrNatVariableAccess:
            {
                auto castedExpr = std::static_pointer_cast<const program::IntOrNatVariableAccess>(expr);
                return toTerm(castedExpr->var, timePoint, trace);
            }
            case program::Type::IntArrayApplication:
            {
                auto castedExpr = std::static_pointer_cast<const program::IntArrayApplication>(expr);
                if(lhsOfAssignment){
                    return toTerm(castedExpr->array, timePoint, trace);
                } else {
                    return toTerm(castedExpr, timePoint, trace);
                }
            } 
            case program::Type::Pointer2IntDeref:
            {
                auto castedExpr = std::static_pointer_cast<const program::DerefP2IExpression>(expr);
                return toTerm(castedExpr, timePoint, trace);                
            }                         
        }
        assert(false);
        //to silence compiler warnings, but we should never reach here
        return toTerm(expr, timePoint, trace);        
    }

    std::shared_ptr<const logic::Formula> toFormula(std::shared_ptr<const program::BoolExpression> expr, std::shared_ptr<const logic::Term> timePoint, std::shared_ptr<const logic::Term> trace)
    {
        assert(expr != nullptr);
        assert(timePoint != nullptr);
        
        switch (expr->type())
        {
            case program::BoolExpression::Type::BooleanConstant:
            {
                auto castedExpr = std::static_pointer_cast<const program::BooleanConstant>(expr);
                return castedExpr->value ? logic::Theory::boolTrue() : logic::Theory::boolFalse();
            }
            case program::BoolExpression::Type::BooleanAnd:
            {
                auto castedExpr = std::static_pointer_cast<const program::BooleanAnd>(expr);
                return logic::Formulas::conjunction({toFormula(castedExpr->child1, timePoint, trace), toFormula(castedExpr->child2, timePoint, trace)});
            }
            case program::BoolExpression::Type::BooleanOr:
            {
                auto castedExpr = std::static_pointer_cast<const program::BooleanOr>(expr);
                return logic::Formulas::disjunction({toFormula(castedExpr->child1, timePoint, trace), toFormula(castedExpr->child2, timePoint, trace)});
            }
            case program::BoolExpression::Type::BooleanNot:
            {
                auto castedExpr = std::static_pointer_cast<const program::BooleanNot>(expr);
                return logic::Formulas::negation(toFormula(castedExpr->child, timePoint, trace));
            }
            case program::BoolExpression::Type::ArithmeticComparison:
            {
                auto castedExpr = std::static_pointer_cast<const program::ArithmeticComparison>(expr);
                switch (castedExpr->kind)
                {
                    case program::ArithmeticComparison::Kind::GT:
                        return logic::Theory::intGreater(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
                    case program::ArithmeticComparison::Kind::GE:
                        return logic::Theory::intGreaterEqual(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
                    case program::ArithmeticComparison::Kind::LT:
                        return logic::Theory::intLess(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
                    case program::ArithmeticComparison::Kind::LE:
                        return logic::Theory::intLessEqual(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
                    case program::ArithmeticComparison::Kind::EQ:
                        return logic::Formulas::equality(toTerm(castedExpr->child1, timePoint, trace), toTerm(castedExpr->child2, timePoint, trace));
                }
            }
        }
        assert(false);
        //to silence compiler warnings, but we should never reach here
        return toFormula(expr, timePoint, trace);        
    }

    std::shared_ptr<const logic::Formula> varEqual(std::shared_ptr<const program::Variable> v, std::shared_ptr<const logic::Term> timePoint1, std::shared_ptr<const logic::Term> timePoint2, std::shared_ptr<const logic::Term> trace)
    {

        auto lhs = toTerm(v,timePoint1,trace);
        auto rhs = toTerm(v,timePoint2,trace);

        return logic::Formulas::equality(lhs, rhs); 
    }

    std::shared_ptr<const logic::Formula> allVarEqual(const std::vector<std::shared_ptr<const program::Variable>>& activeVars, std::shared_ptr<const logic::Term> timePoint1, std::shared_ptr<const logic::Term> timePoint2, std::shared_ptr<const logic::Term> trace, std::string label)
    {
        std::vector<std::shared_ptr<const logic::Formula>> conjuncts;
        for (const auto& var : activeVars)
        {
            if(!var->isConstant)
            {
                conjuncts.push_back(varEqual(var, timePoint1, timePoint2, trace));
            }
        }
        return logic::Formulas::conjunction(conjuncts, label);
    }
}
