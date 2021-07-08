#include "Semantics.hpp"

#include <algorithm>
#include <memory>
#include <vector>
#include <cassert>
#include <unordered_set>

#include "Sort.hpp"
#include "Term.hpp"
#include "Formula.hpp"
#include "Theory.hpp"
#include "Options.hpp"

#include "SymbolDeclarations.hpp"

namespace analysis {

    std::vector<std::shared_ptr<const program::Variable>> intersection(std::vector<std::shared_ptr<const program::Variable>> v1,
                                                                       std::vector<std::shared_ptr<const program::Variable>> v2)
    {
        std::vector<std::shared_ptr<const program::Variable>> v3;

        std::sort(v1.begin(), v1.end());
        std::sort(v2.begin(), v2.end());

        std::set_intersection(v1.begin(),v1.end(),
                              v2.begin(),v2.end(),
                              back_inserter(v3));
        return v3;
    }


    std::vector<std::shared_ptr<const program::Variable>> vecUnion(std::vector<std::shared_ptr<const program::Variable>> v1,
                                                                   std::vector<std::shared_ptr<const program::Variable>> v2)
    {
        std::vector<std::shared_ptr<const program::Variable>> v3;

        std::sort(v1.begin(), v1.end());
        std::sort(v2.begin(), v2.end());

        std::set_union(v1.begin(),v1.end(),
                              v2.begin(),v2.end(),
                              back_inserter(v3));
        return v3;
    }

    std::vector<std::shared_ptr<const logic::Axiom>> 
    Semantics::generateBounds()
    {
        std::vector<std::shared_ptr<const program::Variable>> allVars;

        for (auto it : locationToActiveVars)
        {
            allVars = vecUnion(it.second, allVars);
        } 

        std::vector<std::shared_ptr<const logic::Axiom>> axioms;

        auto locSymbol = locationSymbol("tp",0);
        auto lVar = locVar();
        auto z = logic::Theory::intConstant(0);
 
        for(const auto& var : allVars)
        {
            if(var->isNat()){
                for (const auto& trace : traceTerms(numberOfTraces))
                {

                    auto axiom = logic::Theory::intGreaterEqual(
                                    toTerm(var,lVar,trace),
                                    z
                                );
                    
                    if(!var->isConstant){
                        axiom =  logic::Formulas::universal({locSymbol}, axiom);
                    }

                    axioms.push_back(std::make_shared<logic::Axiom>(axiom));
                }
            }
        }

        return axioms;  
    }


    std::pair<std::vector<std::shared_ptr<const logic::Axiom>>, InlinedVariableValues> Semantics::generateSemantics()
    {           
        // generate semantics compositionally
        std::vector<std::shared_ptr<const logic::Axiom>> axioms;
        for(const auto& function : program.functions)
        {
            std::vector<std::shared_ptr<const logic::Formula>> conjunctsFunction;

            for (const auto& trace : traceTerms(numberOfTraces))
            {
                std::vector<std::shared_ptr<const logic::Formula>> conjunctsTrace;

                SemanticsInliner inliner(problemItems, trace);
                for (const auto& statement : function->statements)
                {
                    auto semantics = generateSemantics(statement.get(), inliner, trace);
                    conjunctsTrace.push_back(semantics);
                }
                if (util::Configuration::instance().inlineSemantics())
                {
                    // handle persistence of last statement of the function
                    auto lEnd = endTimePointMap.at(function->statements.back().get());
                    inliner.currTimepoint = lEnd;
                    auto f = inliner.handlePersistence(lEnd, locationToActiveVars.at(lEnd->symbol->name), "Define referenced terms denoting variable values at " + lEnd->symbol->name);
                    conjunctsTrace.push_back(f);
                }

                if (numberOfTraces > 1)
                {
                    conjunctsFunction.push_back(logic::Formulas::conjunctionSimp(conjunctsTrace, "Semantics of trace " + trace->symbol->name));
                }
                else
                {
                    // if there is only one trace, don't group semantics by trace but use semantics directly
                    conjunctsFunction = conjunctsTrace;
                }
            }

            auto axiomFormula = logic::Formulas::conjunctionSimp(conjunctsFunction);
            axioms.push_back(std::make_shared<logic::Axiom>(axiomFormula, "Semantics of function " + function->name, logic::ProblemItem::Visibility::Implicit));
        }

        std::vector<std::shared_ptr<const program::Variable>> allVars;
        for(auto vars : locationToActiveVars){
            //WARNING if there are multiple vars with the same name, but in different scope
            //this is dangerous!
            allVars = vecUnion(allVars, vars.second);
        }

        std::vector<std::shared_ptr<const logic::Formula>> uniqueVars;
        for(int i = 0; i < allVars.size(); i++){
            auto var = allVars[i];
            for(int j = i + 1; j < allVars.size(); j++){
                auto var2 = allVars[j];
                auto varAsTerm = logic::Terms::func(logic::Signature::fetch(var->name),{});
                auto var2AsTerm = logic::Terms::func(logic::Signature::fetch(var2->name),{});
                auto notEqual = logic::Formulas::disequality(varAsTerm, var2AsTerm);
                uniqueVars.push_back(notEqual);
            }
        }

        auto tp = locationSymbol("tp",0);
        auto memLocSymbol = locVarSymbol();
        auto tpVar = locVar();
        auto memLocVariable = memLocVar();

        auto deref = logic::Theory::deref(tpVar, memLocVariable);
        auto derefFormula = logic::Formulas::disequality(memLocVariable, deref);
        auto derefNotIdentity = logic::Formulas::universal({tp, memLocSymbol}, derefFormula);
        uniqueVars.push_back(derefNotIdentity);
    
        auto memSemantics = logic::Formulas::conjunctionSimp(uniqueVars);

        axioms.push_back(std::make_shared<logic::Axiom>(memSemantics, "Semantics of memory locations", logic::ProblemItem::Visibility::Implicit));
   

        return std::make_pair(axioms, inlinedVariableValues);
    }

    std::shared_ptr<const logic::Formula> Semantics::generateSemantics(const program::Statement* statement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace)
    {
        if (statement->type() == program::Statement::Type::Assignment)
        {
            auto castedStatement = static_cast<const program::Assignment*>(statement);
            return generateSemantics(castedStatement, inliner, trace);
        }
        else if (statement->type() == program::Statement::Type::IfElse)
        {
            auto castedStatement = static_cast<const program::IfElse*>(statement);
            return generateSemantics(castedStatement, inliner, trace);
        }
        else if (statement->type() == program::Statement::Type::WhileStatement)
        {
            auto castedStatement = static_cast<const program::WhileStatement*>(statement);
            return generateSemantics(castedStatement, inliner, trace);
        }
        else
        {
            assert(statement->type() == program::Statement::Type::SkipStatement);
            auto castedStatement = static_cast<const program::SkipStatement*>(statement);
            return generateSemantics(castedStatement, inliner, trace);
        }
    }

    std::shared_ptr<const logic::Formula> Semantics::generateSemantics(const program::Assignment*  assignment, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace)
    {
        std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

        auto l1 = startTimepointForStatement(assignment);
        auto l2 = endTimePointMap.at(assignment);
        auto l1Name = l1->symbol->name;
        auto l2Name = l2->symbol->name;
        auto activeVars = intersection(locationToActiveVars.at(l1Name), locationToActiveVars.at(l2Name));

        if (util::Configuration::instance().inlineSemantics())
        {
            //This is safe as we assume no pointers when using the inliner
            auto castedRhs = std::static_pointer_cast<const program::IntExpression>(assignment->rhs);

            if(assignment->lhs->type() == program::Type::IntOrNatVariableAccess){          
                auto castedLhs = std::static_pointer_cast<const program::IntOrNatVariableAccess>(assignment->lhs);


                inliner.currTimepoint = l1;
                auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
                conjuncts.push_back(f1);

                auto f2 = inliner.setIntVarValue(castedLhs->var, inliner.toCachedTerm(castedRhs));
                conjuncts.push_back(f2);

                return logic::Formulas::conjunctionSimp(conjuncts, "Update variable " + castedLhs->var->name + " at location " + assignment->location);

            } else {
                auto application = std::static_pointer_cast<const program::IntArrayApplication>(assignment->lhs);

                inliner.currTimepoint = l1;
                auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
                conjuncts.push_back(f1);

                // val_int a l2 = store (var_int a last_set) index cached(rhs)
                
                auto var = application->array;

                auto array_now = toTerm(var,l2,trace);
                auto array_before = inliner.toCachedTermFull(var);

                auto index = inliner.toCachedTerm(application->index);
                auto toStore = inliner.toCachedTerm(castedRhs);

                auto rhs = logic::Terms::arrayStore(array_before,index,toStore);

                auto eq1 = logic::Formulas::equality(array_now, rhs);
                conjuncts.push_back(eq1);

                // set last assignment of a to l2
                inliner.setArrayVarTimepoint(var, l2);

                return logic::Formulas::conjunctionSimp(conjuncts, "Update array variable " + application->array->name + " at location " + assignment->location);                    
            }
        }
        else
        {
            //Deal with array and non-array variables together.

            //assignment must be of the form:
            // x = t
            // x = #y
            // *...*x = t
            // *...*x = #y
            // x[expr] = expr

            auto lhs = assignment->lhs;
            auto rhs = assignment->rhs;

            auto isVar = [](std::shared_ptr<const program::Expression> e) {
                return (e->type() == program::Type::PointerVariableAccess ||
                        e->type() == program::Type::IntOrNatVariableAccess);
            };

            auto isDerefExpr = [](std::shared_ptr<const program::Expression> e) {
                return (e->type() == program::Type::Pointer2IntDeref ||
                        e->type() == program::Type::Pointer2PointerDeref);
            };

            auto isRefExpr = [](std::shared_ptr<const program::Expression> e) {
                return (e->type() == program::Type::VarReference);
            };

            auto isIntArrayApp = [](std::shared_ptr<const program::Expression> e) {
                return (e->type() == program::Type::IntArrayApplication);
            };


            auto isNonVarIntExpr = [](std::shared_ptr<const program::Expression> e) {
                return
                (e->type() != program::Type::IntOrNatVariableAccess) &&
                (!e->isPointerExpr());
            };
            
            std::shared_ptr<const logic::Term> lhsTerm; 
            std::shared_ptr<const logic::Term> rhsTerm;

            //[*...*]x = term
            if((isDerefExpr(lhs) || isVar(lhs)) && 
               (isDerefExpr(rhs) || isVar(rhs) || isNonVarIntExpr(rhs))){
                lhsTerm = toTerm(lhs, l2, trace);
                rhsTerm = toTerm(rhs, l1, trace);
            } 

            //[*...*]x = #y
            if(isRefExpr(rhs)){                   
                auto castedRhs = std::static_pointer_cast<const program::VarReference>(rhs);            
                rhsTerm = logic::Terms::locConstant(castedRhs->referent->name);
                lhsTerm = toTerm(lhs, l2, trace);
            }

            //a[expr1] = expr2
            if(isIntArrayApp(lhs)){
                auto asArrayApp = std::static_pointer_cast<const program::IntArrayApplication>(lhs);   
                auto index = toTerm(asArrayApp->index, l1, trace);
                auto toStore = toTerm(rhs, l1, trace);
                auto array = toTerm(asArrayApp->array, l1, trace);
                rhsTerm = logic::Terms::arrayStore(array, index, toStore);  
                lhsTerm = toTerm(lhs, l2, trace, true);
            }

            // lhs(l2) = rhs(l1);
            auto eq = logic::Formulas::equality(lhsTerm, rhsTerm);

            conjuncts.push_back(eq);
             
            auto lhsAsFunc = std::static_pointer_cast<const logic::FuncTerm>(lhsTerm);

            // forall positions pos. (pos!=e(l1) => a(l2,pos) = a(l1,pos))
            auto locSymbol = locVarSymbol();
            auto loc = memLocVar();
          
            bool activeVarsContainsArrayVars = false;
            bool activeVarsContainsPointerVars = false;

            for(auto var : activeVars){
                if(var->isArray()){
                    activeVarsContainsArrayVars =  true;
                } else if(var->isPointer()){
                    activeVarsContainsPointerVars = true;
                }
            }

            auto premise = logic::Formulas::disequality(loc, lhsAsFunc->subterms[1]);

            std::vector<std::shared_ptr<const logic::Formula>> forms;

            auto lhs3 = logic::Theory::valueAtInt(l2, loc);
            auto rhs3 = logic::Theory::valueAtInt(l1, loc);
            auto eq3 = logic::Formulas::equality(lhs3, rhs3);
            forms.push_back(lhsAsFunc->isValueAt()  ?
                            logic::Formulas::implication(premise, eq3) : eq3);

            if(activeVarsContainsPointerVars){
                auto lhs2 = logic::Theory::deref(l2, loc);
                auto rhs2 = logic::Theory::deref(l1, loc);
                auto eq2 = logic::Formulas::equality(lhs2, rhs2);
                forms.push_back(lhsAsFunc->isDerefAt() ?
                                logic::Formulas::implication(premise, eq2) : eq2);     
            }
            
            if(activeVarsContainsArrayVars){
                auto lhs4 = logic::Theory::valueAtArray(l2, loc);                    
                auto rhs4 = logic::Theory::valueAtArray(l1, loc);
                auto eq4 = logic::Formulas::equality(lhs4, rhs4); 
                forms.push_back(lhsAsFunc->isValueAt()  || lhsAsFunc->isDerefAt() ?
                                eq4 : logic::Formulas::implication(premise, eq4));     
            }
        
            auto conj = logic::Formulas::conjunctionSimp(forms);
            auto conjunct = logic::Formulas::universal({locSymbol}, conj);

            conjuncts.push_back(conjunct);

            return logic::Formulas::conjunction(conjuncts, "Update variable " + lhs->toString() + " at location " + assignment->location);
        
        }
        
    }

    std::shared_ptr<const logic::Formula> Semantics::generateSemantics(const program::IfElse* ifElse, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace)
    {
        std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

        auto lStart = startTimepointForStatement(ifElse);
        auto lEnd = endTimePointMap.at(ifElse);
        auto lLeftStart = startTimepointForStatement(ifElse->ifStatements.front().get());
        auto lRightStart = startTimepointForStatement(ifElse->elseStatements.front().get());

        if (util::Configuration::instance().inlineSemantics())
        {
            // Part 1: visit start-location
            inliner.currTimepoint = lStart;
            auto f1 = inliner.handlePersistence(lStart, locationToActiveVars.at(lStart->symbol->name), "Define referenced terms denoting variable values at " + ifElse->location);
            conjuncts.push_back(f1);

            // Part 2: go through branches: collect all formulas describing semantics of branches and assert them conditionally
            // note: we need to generate condition and negatedCondition here, since they depend on the state of the inliner.
            auto condition = inliner.toCachedFormula(ifElse->condition);
            auto negatedCondition = logic::Formulas::negation(condition);

            std::vector<std::shared_ptr<const logic::Formula>> conjunctsLeft;
            std::vector<std::shared_ptr<const logic::Formula>> conjunctsRight;
            SemanticsInliner inlinerLeft(inliner);
            SemanticsInliner inlinerRight(inliner);

            for (const auto& statement : ifElse->ifStatements)
            {   
                auto semanticsOfStatement = generateSemantics(statement.get(), inlinerLeft, trace);
                conjunctsLeft.push_back(semanticsOfStatement);
            }
            for (const auto& statement : ifElse->elseStatements)
            {            
                auto semanticsOfStatement = generateSemantics(statement.get(), inlinerRight, trace);
                conjunctsRight.push_back(semanticsOfStatement);
            }

            // Part 3: define variable values at the merge of branches
            auto cachedIntVarValues = inliner.getCachedIntVarValues();
            auto cachedArrayVarTimepoints = inliner.getCachedArrayVarTimepoints();
            auto cachedIntVarValuesLeft = inlinerLeft.getCachedIntVarValues();
            auto cachedArrayVarTimepointsLeft = inlinerLeft.getCachedArrayVarTimepoints();
            auto cachedIntVarValuesRight = inlinerRight.getCachedIntVarValues();
            auto cachedArrayVarTimepointsRight = inlinerRight.getCachedArrayVarTimepoints();

            std::unordered_set<std::shared_ptr<const program::Variable>> mergeVars;
            for (const auto& pair : cachedIntVarValuesLeft)
            {
                auto var = pair.first;
                if (cachedIntVarValues.find(var) == cachedIntVarValues.end() || *cachedIntVarValues[var] != *pair.second)
                {
                    if(!var->isConstant)
                    {
                        mergeVars.insert(var);
                    }
                }
            }
            for (const auto& pair : cachedIntVarValuesRight)
            {
                auto var = pair.first;
                if (cachedIntVarValues.find(var) == cachedIntVarValues.end() || *cachedIntVarValues[var] != *pair.second)
                {
                    if(!var->isConstant)
                    {
                        mergeVars.insert(var);
                    }
                }
            }
            for (const auto& pair : cachedArrayVarTimepointsLeft)
            {
                auto var = pair.first;
                if (cachedArrayVarTimepoints.find(var) == cachedArrayVarTimepoints.end() || *cachedArrayVarTimepoints[var] != *pair.second)
                {
                    if(!var->isConstant)
                    {
                        mergeVars.insert(var);
                    }
                }
            }
            for (const auto& pair : cachedArrayVarTimepointsRight)
            {
                auto var = pair.first;
                if (cachedArrayVarTimepoints.find(var) == cachedArrayVarTimepoints.end() || *cachedArrayVarTimepoints[var] != *pair.second)
                {
                    if(!var->isConstant)
                    {
                        mergeVars.insert(var);
                    }
                }
            }

            for (const auto& var : mergeVars)
            {
                auto varLEnd = toTerm(var,lEnd,trace);

                // define the value of var at lEnd as the merge of values at the end of the two branches
                conjunctsLeft.push_back(
                    logic::Formulas::equalitySimp(
                        varLEnd,
                        inlinerLeft.toCachedTermFull(var)
                    )
                );
                conjunctsRight.push_back(
                    logic::Formulas::equalitySimp(
                        varLEnd,
                        inlinerRight.toCachedTermFull(var)
                    )
                );

                // remember that lEnd is the last timepoint where var was set
                assert(!var->isConstant);
                if(var->isArray()){
                    inliner.setArrayVarTimepoint(var, lEnd);                    
                } else {
                    auto result = inliner.setIntVarValue(var, varLEnd);
                }
            }

            conjuncts.push_back(
                logic::Formulas::implicationSimp(
                    condition,
                    logic::Formulas::conjunctionSimp(conjunctsLeft),
                    "Semantics of left branch"
                )
            );
            conjuncts.push_back(
                logic::Formulas::implicationSimp(
                     negatedCondition,
                     logic::Formulas::conjunctionSimp(conjunctsRight),
                     "Semantics of right branch"
                )
            );

            return logic::Formulas::conjunctionSimp(conjuncts, "Semantics of IfElse at location " + ifElse->location);
        }
        else
        {
            auto condition = toFormula(ifElse->condition, lStart, trace);
            auto negatedCondition = logic::Formulas::negation(condition);

            // Part 1: values at the beginning of any branch are the same as at the beginning of the ifElse-statement
            // don't need to take the intersection with active vars at lLeftStart/lRightStart, since the active vars at lStart are always a subset of those at lLeftStart/lRightStart
            auto activeVars = locationToActiveVars.at(lStart->symbol->name);

            auto implicationIfBranch = logic::Formulas::implication(condition, allVarEqual(activeVars,lLeftStart,lStart, trace), "Jumping into the left branch doesn't change the variable values");
            auto implicationElseBranch = logic::Formulas::implication(negatedCondition, allVarEqual(activeVars,lRightStart,lStart, trace), "Jumping into the right branch doesn't change the variable values");

            conjuncts.push_back(implicationIfBranch);
            conjuncts.push_back(implicationElseBranch);

            // Part 2: collect all formulas describing semantics of branches and assert them conditionally
            for (const auto& statement : ifElse->ifStatements)
            {
                auto semanticsOfStatement = generateSemantics(statement.get(), inliner, trace);
                auto implication = logic::Formulas::implication(condition, semanticsOfStatement, "Semantics of left branch");
                conjuncts.push_back(implication);
            }
            for (const auto& statement : ifElse->elseStatements)
            {
                auto semanticsOfStatement = generateSemantics(statement.get(), inliner, trace);
                auto implication = logic::Formulas::implication(negatedCondition, semanticsOfStatement,  "Semantics of right branch");
                conjuncts.push_back(implication);
            }

            return logic::Formulas::conjunction(conjuncts, "Semantics of IfElse at location " + ifElse->location);
        }
    }

    std::shared_ptr<const logic::Formula> Semantics::generateSemantics(const program::WhileStatement* whileStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace)
    {
        std::vector<std::shared_ptr<const logic::Formula>> conjuncts;

        auto itSymbol = iteratorSymbol(whileStatement);
        auto it = logic::Terms::var(itSymbol);
        auto n = lastIterationTermForLoop(whileStatement, numberOfTraces, trace);

        auto lStart0 = timepointForLoopStatement(whileStatement, logic::Theory::natZero());
        auto lStartIt = timepointForLoopStatement(whileStatement, it);
        auto lStartSuccOfIt = timepointForLoopStatement(whileStatement, logic::Theory::natSucc(it));
        auto lStartN = timepointForLoopStatement(whileStatement, n);
        auto lBodyStartIt = startTimepointForStatement(whileStatement->bodyStatements.front().get());
        auto lEnd = endTimePointMap.at(whileStatement);

        auto posSymbol = posVarSymbol();
        auto pos = posVar();

        auto activeVars = locationToActiveVars.at(lStart0->symbol->name);

        if (util::Configuration::instance().inlineSemantics())
        {
            auto assignedVars = AnalysisPreComputation::computeAssignedVars(whileStatement);
            // Part 0: custom persistence handling: handle all vars which 1) are active, 2) keep the same value throughout the loop, 3) are non-const, and 4) are persistent at the loop condition check
            // note: condition 3) is a requirement since otherwise the defining formulas could be unsound. Condition 4) does not lead to incompleteness of the formalization, since the value of variables, which change their value in the loop, will be defined afterwards anyway.
            std::vector<std::shared_ptr<const program::Variable>> vars;
            for (const auto& var : activeVars)
            {
                if (assignedVars.find(var) == assignedVars.end() && !var->isConstant)
                {
                    vars.push_back(var);
                }
            }
            auto f1 = inliner.handlePersistenceOfLoop(lStart0, lStartIt, vars);
            conjuncts.push_back(
                logic::Formulas::universalSimp({itSymbol},
                    logic::Formulas::implicationSimp(
                        logic::Theory::natSubEq(it,n),
                        f1
                    ),
                    "Define referenced terms denoting variable values at " + whileStatement->location
                )
            );

            // Part 1: define values of assignedVars at iteration zero
            std::vector<std::shared_ptr<const logic::Formula>> conjPart1;

            inliner.currTimepoint = lStart0;
            for (const auto& var : assignedVars)
            {
                conjPart1.push_back(
                    logic::Formulas::equalitySimp(
                        toTerm(var, lStart0,trace),
                        inliner.toCachedTermFull(var)
                    )
                );
            }

            conjuncts.push_back(
                logic::Formulas::conjunctionSimp(
                    conjPart1,
                    "Define variable values at beginning of loop"
                )
            );

            // Part 2a: Loop condition holds at main-loop-location for all iterations before n
            inliner.currTimepoint = lStartIt;
            for (const auto& var : assignedVars)
            {
                if (!var->isArray())
                {
                    assert(!var->isConstant);
                    auto result = inliner.setIntVarValue(var,toTerm(var,lStartIt,trace));
                }
                else
                {
                    inliner.setArrayVarTimepoint(var,lStartIt);
                }
            }

            conjuncts.push_back(
                logic::Formulas::universal({itSymbol},
                    logic::Formulas::implication(
                        logic::Theory::natSub(it, n),
                        inliner.toCachedFormula(whileStatement->condition)
                    ),
                    "The loop-condition holds always before the last iteration"
                )
            );

            // Extra part: collect in inlinedVarValues the values of all variables, which occur in the loop condition but are not assigned to.
            inlinedVariableValues.initializeWhileStatement(whileStatement);
            std::unordered_set<std::shared_ptr<const program::Variable>> loopConditionVars;
            AnalysisPreComputation::computeVariablesContainedInLoopCondition(whileStatement->condition, loopConditionVars);

            for (const auto& var : loopConditionVars)
            {
                if (assignedVars.find(var) == assignedVars.end())
                {
                    if (var->isArray())
                    {
                        inlinedVariableValues.setArrayTimepoint(whileStatement, var, trace, inliner.getCachedArrayVarTimepoints().at(var));
                    }
                    else
                    {
                        inlinedVariableValues.setValue(whileStatement, var, trace, inliner.getCachedIntVarValues().at(var));
                    }
                }
            }

            // Part 3: collect all formulas describing semantics of the body, and define values of assignedVars at all iterations s(it)
            assert(*inliner.currTimepoint == *lStartIt);

            std::vector<std::shared_ptr<const logic::Formula>> conjunctsBody;
            for (const auto& statement : whileStatement->bodyStatements)
            {
                
                auto semanticsOfStatement = generateSemantics(statement.get(), inliner, trace);
                conjunctsBody.push_back(semanticsOfStatement);
            }

            inliner.currTimepoint = lStartSuccOfIt;
            for (const auto& var : assignedVars)
            {
                conjunctsBody.push_back(
                    logic::Formulas::equalitySimp(
                        toTerm(var,lStartSuccOfIt,trace),
                        inliner.toCachedTermFull(var),
                        "Define value of variable " + var->name + " at beginning of next iteration"
                    )
                );
            }

            conjuncts.push_back(
                logic::Formulas::universalSimp({itSymbol},
                    logic::Formulas::implicationSimp(
                        logic::Theory::natSub(it,n),
                        logic::Formulas::conjunctionSimp(conjunctsBody)
                    ),
                    "Semantics of the body"
                )
            );

            // Part 4: define values of assignedVars after the execution of the loop
            inliner.currTimepoint = lStartN;
            for (const auto& var : assignedVars)
            {
                if (!var->isArray())
                {
                    assert(!var->isConstant);
                    auto result = inliner.setIntVarValue(var, toTerm(var,lStartN,trace));
                }
                else
                {
                    inliner.setArrayVarTimepoint(var,lStartN);
                }
            }

            // Part 2b: loop condition doesn't hold at n
            assert(*inliner.currTimepoint == *lStartN);
            conjuncts.push_back(
                logic::Formulas::negation(
                    inliner.toCachedFormula(whileStatement->condition),
                    "The loop-condition doesn't hold in the last iteration"
                )
            );

            return logic::Formulas::conjunctionSimp(conjuncts, "Loop at location " + whileStatement->location);
        }
        else
        {
            // Part 1: values at the beginning of body are the same as at the beginning of the while-statement
            auto part1 =
                logic::Formulas::universal({itSymbol},
                    logic::Formulas::implication(
                        logic::Theory::natSub(it,n),
                        allVarEqual(activeVars,lBodyStartIt,lStartIt, trace)
                    ),
                    "Jumping into the loop body doesn't change the variable values"
                );
            conjuncts.push_back(part1);

            // Part 2: collect all formulas describing semantics of body
            std::vector<std::shared_ptr<const logic::Formula>> conjunctsBody;
            for (const auto& statement : whileStatement->bodyStatements)
            {
                
                auto conjunct = generateSemantics(statement.get(), inliner, trace);
                conjunctsBody.push_back(conjunct);
            }
            auto bodySemantics =
                logic::Formulas::universal({itSymbol},
                    logic::Formulas::implication(
                        logic::Theory::natSub(it,n),
                        logic::Formulas::conjunction(conjunctsBody)
                    ),
                    "Semantics of the body"
                );
            conjuncts.push_back(bodySemantics);

            // Part 3: Define last iteration
            // Loop condition holds at main-loop-location for all iterations before n
            auto universal =
                logic::Formulas::universal({itSymbol},
                    logic::Formulas::implication(
                        logic::Theory::natSub(it, n),
                        toFormula(whileStatement->condition, lStartIt, trace)),
                    "The loop-condition holds always before the last iteration"
                );
            conjuncts.push_back(universal);

            // loop condition doesn't hold at n
            auto negConditionAtN = logic::Formulas::negation(toFormula(whileStatement->condition, lStartN, trace), "The loop-condition doesn't hold in the last iteration");
            conjuncts.push_back(negConditionAtN);

            // Part 4: The values after the while-loop are the values from the timepoint with location lStart and iteration n
            auto part4 = allVarEqual(activeVars,lEnd,lStartN, trace, "The values after the while-loop are the values from the last iteration");
            conjuncts.push_back(part4);

            return logic::Formulas::conjunction(conjuncts, "Loop at location " + whileStatement->location);
        }
    }

    std::shared_ptr<const logic::Formula> Semantics::generateSemantics(const program::SkipStatement* skipStatement, SemanticsInliner& inliner, std::shared_ptr<const logic::Term> trace)
    {
        auto l1 = startTimepointForStatement(skipStatement);

        if (util::Configuration::instance().inlineSemantics())
        {
            inliner.currTimepoint = l1;
            return inliner.handlePersistence(l1, locationToActiveVars.at(l1->symbol->name));
        }
        else
        {
            auto l2 = endTimePointMap.at(skipStatement);

            // identify startTimePoint and endTimePoint
            auto eq = logic::Formulas::equality(l1, l2, "Ignore any skip statement");
            return eq;
        }
    }
}