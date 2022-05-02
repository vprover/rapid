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

namespace analysis {

std::vector<std::shared_ptr<program::Variable>> intersection(
    std::vector<std::shared_ptr<program::Variable>> v1,
    std::vector<std::shared_ptr<program::Variable>> v2) {
  std::vector<std::shared_ptr<program::Variable>> v3;

  std::sort(v1.begin(), v1.end());
  std::sort(v2.begin(), v2.end());

  std::set_intersection(v1.begin(), v1.end(), v2.begin(), v2.end(),
                        back_inserter(v3));
  return v3;
}

void Semantics::applyTransformations(
    std::vector<std::shared_ptr<program::Function>> &functions,
    std::unordered_map<std::string,
                       std::vector<std::shared_ptr<program::Variable>>>
        &locationToActiveVars,
    unsigned traces) {
  for (auto &function : functions) {
    program::Statement::transformBlock(function->statements,
                                       locationToActiveVars, traces);
  }
}

// collect negated loop conditions for invariant generation mode
std::vector<std::shared_ptr<const logic::LoopCondition>> Semantics::generateNegatedLoopConditions() {
  
  std::vector<std::shared_ptr<const logic::LoopCondition>> items; 

  for (const auto &function : program.functions) {
    for (const auto &trace : traceTerms(numberOfTraces)) {
      SemanticsInliner inliner(problemItems, trace);
      for (const auto &statement : function->statements) {
        if(typeid(*statement) == typeid(program::WhileStatement)){
          auto whileStatement = static_cast<program::WhileStatement *>(statement.get()); 
            auto itSymbol = iteratorSymbol(whileStatement);
            auto it = logic::Terms::var(itSymbol);
            auto lStartIt = timepointForLoopStatement(whileStatement, it);
            auto condition = toTerm(whileStatement->condition, lStartIt, trace);
            auto negatedCondition = logic::Formulas::negation(condition);
            auto negatedConditionDef = std::make_shared<logic::LoopCondition>(
              negatedCondition, "Negated Loop Condition for loop at " + whileStatement->location,
              logic::ProblemItem::Visibility::Implicit);
            items.push_back(negatedConditionDef); 
        }
      }
    }
  }
  return items; 
}

std::pair<std::vector<std::shared_ptr<const logic::Axiom>>,
          InlinedVariableValues>
Semantics::generateSemantics() {
  // generate semantics compositionally
  std::vector<std::shared_ptr<const logic::Axiom>> axioms;
  for (const auto &function : program.functions) {
    std::vector<std::shared_ptr<const logic::Term>> conjunctsFunction;

    for (const auto &trace : traceTerms(numberOfTraces)) {
      std::vector<std::shared_ptr<const logic::Term>> conjunctsTrace;

      SemanticsInliner inliner(problemItems, trace);
      for (const auto &statement : function->statements) {
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

      if (numberOfTraces > 1) {
        conjunctsFunction.push_back(logic::Formulas::conjunctionSimp(
            conjunctsTrace, "Semantics of trace " + trace->symbol->name));
      } else {
        // if there is only one trace, don't group semantics by trace but use
        // semantics directly
        conjunctsFunction = conjunctsTrace;
      }

      std::vector<std::shared_ptr<const logic::Term>> targetSymbolAxioms;

      // postcondition mode
      // TODO: handling for multiple traces
      if (util::Configuration::instance().invariantGeneration()) {
        for (auto i = coloredSymbols.begin(); i != coloredSymbols.end(); ++i) {
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

      auto targetFormula = std::make_shared<logic::Axiom>(
          logic::Formulas::conjunctionSimp(targetSymbolAxioms),
          "target symbol definitions for symbol elimination",
          logic::ProblemItem::Visibility::Implicit);
      axioms.push_back(targetFormula);
    }

    auto axiomFormula = logic::Formulas::conjunctionSimp(conjunctsFunction);
    axioms.push_back(std::make_shared<logic::Axiom>(
        axiomFormula, "Semantics of function " + function->name,
        logic::ProblemItem::Visibility::Implicit));
  }

  return std::make_pair(axioms, inlinedVariableValues);
}

std::shared_ptr<const logic::Term> Semantics::generateSemantics(
    program::Statement *statement, SemanticsInliner &inliner,
    std::shared_ptr<const logic::Term> trace) {
  if (typeid(*statement) == typeid(program::Assignment)) {
    auto castedStatement = static_cast<program::Assignment *>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else if (typeid(*statement) == typeid(program::IfElseStatement)) {
    auto castedStatement = static_cast<program::IfElseStatement *>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else if (typeid(*statement) == typeid(program::WhileStatement)) {
    auto castedStatement = static_cast<program::WhileStatement *>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  } else {
    assert(typeid(*statement) == typeid(program::SkipStatement));
    auto castedStatement = static_cast<program::SkipStatement *>(statement);
    return generateSemantics(castedStatement, inliner, trace);
  }
}

std::shared_ptr<const logic::Term> Semantics::generateSemantics(
    program::Assignment *assignment, SemanticsInliner &inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Term>> conjuncts;

  auto l1 = startTimepointForStatement(assignment);
  auto l2 = endTimePointMap.at(assignment);
  auto l1Name = l1->symbol->name;
  auto l2Name = l2->symbol->name;
  auto activeVars = intersection(locationToActiveVars.at(l1Name),
                                 locationToActiveVars.at(l2Name));

  // case 1: assignment to int var
  if (typeid(*assignment->lhs) == typeid(program::VariableAccess)) {
    auto castedLhs =
        std::static_pointer_cast<program::VariableAccess>(assignment->lhs);

    // add integer symbols for coloring
    coloredSymbols.insert_or_assign(assignment->lhs->toString(),
                                    castedLhs->var);

    if (util::Configuration::instance().inlineSemantics()) {
      inliner.currTimepoint = l1;
      auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
      conjuncts.push_back(f1);

      auto f2 = inliner.setVarValue(castedLhs->var,
                                    inliner.toCachedTerm(assignment->rhs));
      conjuncts.push_back(f2);

      return logic::Formulas::conjunctionSimp(
          conjuncts, "Update variable " + castedLhs->var->name +
                         " at location " + assignment->location);
    } else {
      // lhs(l2) = rhs(l1)
      auto eq = logic::Formulas::equality(toTerm(castedLhs, l2, trace),
                                          toTerm(assignment->rhs, l1, trace));
      conjuncts.push_back(eq);

      for (const auto &var : activeVars) {
        if (!var->isConstant) {
          if (!var->isArray) {
            // forall other active non-const int-variables: v(l2) = v(l1)
            if (*var != *castedLhs->var) {
              auto eq = logic::Formulas::equality(toTerm(var, l2, trace),
                                                  toTerm(var, l1, trace));
              conjuncts.push_back(eq);
            }
          } else {
            // forall active non-const int-array-variables: forall p. v(l2,p) =
            // v(l1,p)
            auto posSymbol = posVarSymbol();
            auto pos = posVar();
            auto conjunct = logic::Formulas::universal(
                {posSymbol},
                logic::Formulas::equality(toTerm(var, l2, pos, trace),
                                          toTerm(var, l1, pos, trace)));
            conjuncts.push_back(conjunct);
          }
        }
      }

      return logic::Formulas::conjunction(
          conjuncts, "Update variable " + castedLhs->var->name +
                         " at location " + assignment->location);
    }
  }
  // case 2: assignment to int-array var
  else {
    assert(typeid(*assignment->lhs) == typeid(program::ArrayApplication));
    auto application =
        std::static_pointer_cast<program::ArrayApplication>(assignment->lhs);

    // add array symbols for coloring
    coloredSymbols.insert_or_assign(application->array->name,
                                    application->array);

    if (util::Configuration::instance().inlineSemantics()) {
      inliner.currTimepoint = l1;
      auto f1 = inliner.handlePersistence(l1, locationToActiveVars.at(l1Name));
      conjuncts.push_back(f1);

      // a(l2, cached(e)) = cached(rhs)
      auto eq1Lhs = toTerm(application->array, l2,
                           inliner.toCachedTerm(application->index), trace);
      auto eq1Rhs = inliner.toCachedTerm(assignment->rhs);
      auto eq1 = logic::Formulas::equality(eq1Lhs, eq1Rhs);
      conjuncts.push_back(eq1);

      // forall positions pos. (pos!=cached(e) => a(l2,pos) = cached(a,pos))
      auto posSymbol = posVarSymbol();
      auto pos = posVar();

      auto premise = logic::Formulas::disequality(
          pos, inliner.toCachedTerm(application->index));
      auto eq2 = logic::Formulas::equality(
          toTerm(application->array, l2, pos, trace),
          inliner.toCachedTermFull(application->array, pos));
      auto conjunct = logic::Formulas::universal(
          {posSymbol}, logic::Formulas::implication(premise, eq2));
      conjuncts.push_back(conjunct);

      // set last assignment of a to l2
      inliner.setArrayVarTimepoint(application->array, l2);

      return logic::Formulas::conjunctionSimp(
          conjuncts, "Update array variable " + application->array->name +
                         " at location " + assignment->location);
    } else {
      // a(l2, e(l1)) = rhs(l1)
      auto eq1Lhs = toTerm(application->array, l2,
                           toTerm(application->index, l1, trace), trace);
      auto eq1Rhs = toTerm(assignment->rhs, l1, trace);
      auto eq1 = logic::Formulas::equality(eq1Lhs, eq1Rhs);
      conjuncts.push_back(eq1);

      // forall positions pos. (pos!=e(l1) => a(l2,pos) = a(l1,pos))
      auto posSymbol = posVarSymbol();
      auto pos = posVar();

      auto premise = logic::Formulas::disequality(
          pos, toTerm(application->index, l1, trace));
      auto eq2 =
          logic::Formulas::equality(toTerm(application->array, l2, pos, trace),
                                    toTerm(application->array, l1, pos, trace));
      auto conjunct = logic::Formulas::universal(
          {posSymbol}, logic::Formulas::implication(premise, eq2));
      conjuncts.push_back(conjunct);

      for (const auto &var : activeVars) {
        if (!var->isConstant) {
          if (!var->isArray) {
            // forall active non-const int-variables: v(l2) = v(l1)
            auto eq = logic::Formulas::equality(toTerm(var, l2, trace),
                                                toTerm(var, l1, trace));
            conjuncts.push_back(eq);
          } else {
            // forall other active non-const int-array-variables: forall pos.
            // v(l2,pos) = v(l1,pos)
            if (*var != *application->array) {
              auto posSymbol = posVarSymbol();
              auto pos = posVar();
              auto conjunct = logic::Formulas::universal(
                  {posSymbol},
                  logic::Formulas::equality(toTerm(var, l2, pos, trace),
                                            toTerm(var, l1, pos, trace)));
              conjuncts.push_back(conjunct);
            }
          }
        }
      }
      return logic::Formulas::conjunction(
          conjuncts, "Update array variable " + application->array->name +
                         " at location " + assignment->location);
    }
  }
}

std::shared_ptr<const logic::Term> Semantics::generateSemantics(
    program::IfElseStatement *ifElse, SemanticsInliner &inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Term>> conjuncts;

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
    auto condition = inliner.toCachedTerm(ifElse->condition);
    auto negatedCondition = logic::Formulas::negation(condition);

    std::vector<std::shared_ptr<const logic::Term>> conjunctsLeft;
    std::vector<std::shared_ptr<const logic::Term>> conjunctsRight;
    SemanticsInliner inlinerLeft(inliner);
    SemanticsInliner inlinerRight(inliner);

    for (const auto &statement : ifElse->ifStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inlinerLeft, trace);
      conjunctsLeft.push_back(semanticsOfStatement);
    }
    for (const auto &statement : ifElse->elseStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inlinerRight, trace);
      conjunctsRight.push_back(semanticsOfStatement);
    }

    // Part 3: define variable values at the merge of branches
    auto cachedIntVarValues = inliner.getCachedVarValues();
    auto cachedArrayVarTimepoints = inliner.getCachedArrayVarTimepoints();
    auto cachedIntVarValuesLeft = inlinerLeft.getCachedVarValues();
    auto cachedArrayVarTimepointsLeft =
        inlinerLeft.getCachedArrayVarTimepoints();
    auto cachedIntVarValuesRight = inlinerRight.getCachedVarValues();
    auto cachedArrayVarTimepointsRight =
        inlinerRight.getCachedArrayVarTimepoints();

    std::unordered_set<std::shared_ptr<program::Variable>> mergeVars;
    for (const auto &pair : cachedIntVarValuesLeft) {
      auto var = pair.first;
      if (cachedIntVarValues.find(var) == cachedIntVarValues.end() ||
          *cachedIntVarValues[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }
    for (const auto &pair : cachedIntVarValuesRight) {
      auto var = pair.first;
      if (cachedIntVarValues.find(var) == cachedIntVarValues.end() ||
          *cachedIntVarValues[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }
    
    for (const auto &pair : cachedArrayVarTimepointsLeft) {	
      auto var = pair.first;	
      if (cachedArrayVarTimepoints.find(var) ==	
              cachedArrayVarTimepoints.end() ||	
          *cachedArrayVarTimepoints[var] != *pair.second) {	
        if (!var->isConstant) {	
          mergeVars.insert(var);	
        }	
      }	
    }
      
    for (const auto &pair : cachedArrayVarTimepointsRight) {
      auto var = pair.first;
      if (cachedArrayVarTimepoints.find(var) ==
              cachedArrayVarTimepoints.end() ||
          *cachedArrayVarTimepoints[var] != *pair.second) {
        if (!var->isConstant) {
          mergeVars.insert(var);
        }
      }
    }

    for (const auto &var : mergeVars) {
      if (!var->isArray) {
        auto varLEnd = toTerm(var, lEnd, trace);

        // define the value of var at lEnd as the merge of values at the end of
        // the two branches
        conjunctsLeft.push_back(logic::Formulas::equalitySimp(
            varLEnd, inlinerLeft.toCachedTermFull(var)));
        conjunctsRight.push_back(logic::Formulas::equalitySimp(
            varLEnd, inlinerRight.toCachedTermFull(var)));

        // remember that lEnd is the last timepoint where var was set
        assert(!var->isConstant);
        auto result = inliner.setVarValue(var, varLEnd);
      } else {
        assert(cachedArrayVarTimepointsLeft.find(var) !=
               cachedArrayVarTimepointsLeft.end());
        assert(cachedArrayVarTimepointsRight.find(var) !=
               cachedArrayVarTimepointsRight.end());

        auto posSymbol = posVarSymbol();
        auto pos = posVar();
        auto varLEnd = toTerm(var, lEnd, pos, trace);

        // define the value of var at lEnd as the merge of values at the end of
        // the two branches
        conjunctsLeft.push_back(logic::Formulas::universalSimp(
            {posSymbol}, logic::Formulas::equalitySimp(
                             varLEnd, inlinerLeft.toCachedTermFull(var, pos))));
        conjunctsRight.push_back(logic::Formulas::universalSimp(
            {posSymbol},
            logic::Formulas::equalitySimp(
                varLEnd, inlinerRight.toCachedTermFull(var, pos))));

        // cache the fact that lEnd is the last timepoint where var was set
        assert(!var->isConstant);
        inliner.setArrayVarTimepoint(var, lEnd);
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
    auto condition = toTerm(ifElse->condition, lStart, trace);
    auto negatedCondition = logic::Formulas::negation(condition);

    // Part 1: values at the beginning of any branch are the same as at the
    // beginning of the ifElse-statement don't need to take the intersection
    // with active vars at lLeftStart/lRightStart, since the active vars at
    // lStart are always a subset of those at lLeftStart/lRightStart
    auto activeVars = locationToActiveVars.at(lStart->symbol->name);

    auto implicationIfBranch = logic::Formulas::implication(
        condition, allVarEqual(activeVars, lLeftStart, lStart, trace),
        "Jumping into the left branch doesn't change the variable values");
    auto implicationElseBranch = logic::Formulas::implication(
        negatedCondition, allVarEqual(activeVars, lRightStart, lStart, trace),
        "Jumping into the right branch doesn't change the variable values");

    conjuncts.push_back(implicationIfBranch);
    conjuncts.push_back(implicationElseBranch);

    // Part 2: collect all formulas describing semantics of branches and assert
    // them conditionally
    for (const auto &statement : ifElse->ifStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inliner, trace);
      auto implication = logic::Formulas::implication(
          condition, semanticsOfStatement, "Semantics of left branch");
      conjuncts.push_back(implication);
    }
    for (const auto &statement : ifElse->elseStatements) {
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

std::shared_ptr<const logic::Term> Semantics::generateSemantics(
    program::WhileStatement *whileStatement, SemanticsInliner &inliner,
    std::shared_ptr<const logic::Term> trace) {
  std::vector<std::shared_ptr<const logic::Term>> conjuncts;

  auto itSymbol = iteratorSymbol(whileStatement);
  auto it = logic::Terms::var(itSymbol);
  auto n = lastIterationTermForLoop(whileStatement, numberOfTraces, trace);

  auto lStart0 =
      timepointForLoopStatement(whileStatement, logic::Theory::zero());
  loopStartTimePoints.push_back(lStart0);
  auto lStartIt = timepointForLoopStatement(whileStatement, it);
  auto lStartSuccOfIt =
      timepointForLoopStatement(whileStatement, logic::Theory::succ(it));
  auto lStartN = timepointForLoopStatement(whileStatement, n);
  auto lBodyStartIt =
      startTimepointForStatement(whileStatement->bodyStatements.front().get());
  auto lEnd = endTimePointMap.at(whileStatement);
  loopEndTimePoints.push_back(lStartN);
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
    std::vector<std::shared_ptr<program::Variable>> vars;
    for (const auto &var : activeVars) {
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
    std::vector<std::shared_ptr<const logic::Term>> conjPart1;

    inliner.currTimepoint = lStart0;
    for (const auto &var : assignedVars) {
      if (!var->isArray) {
        conjPart1.push_back(logic::Formulas::equalitySimp(
            toTerm(var, lStart0, trace), inliner.toCachedTermFull(var)));
      } else {
        auto cachedArrayTerm = inliner.toCachedTermFull(var, pos);

        auto f = logic::Formulas::universalSimp(
            {posSymbol},
            logic::Formulas::equalitySimp(toTerm(var, lStart0, pos, trace),
                                          cachedArrayTerm));

        // Special inlining case: derefencering constant program variables when
        // defined as mutable. When a timepoint is used with a quantified
        // variable such as Itl9 instead of nl9 when dereferencing terms for
        // main_end, f needs to universally quantify over Itl9 as well. This
        // might occur when non-constant program variables are not changed
        // throughout a loop, hence they are not propagated throughout all
        // timepoints of the loop with inline semantics. This variable will only
        // have cached timepoints from where its values were used, but not from
        // the end of the loop. Essentially these values are equal for all
        // iterations Itl9 of the loop.
        auto tps = inliner.getCachedArrayVarTimepoints();
        auto cachedTimepoint = tps[var];
        if (cachedTimepoint.get()->prettyString(0).find("nl") ==
                std::string::npos &&
            cachedTimepoint.get()->prettyString(0).find("Itl") !=
                std::string::npos) {
          auto cachedTimepointTerm =
              std::static_pointer_cast<const logic::FuncTerm>(cachedTimepoint);
          auto quantifiedSym =
              cachedTimepointTerm->subterms.back().get()->symbol;
          f = logic::Formulas::universalSimp(
              {posSymbol, quantifiedSym},
              logic::Formulas::equalitySimp(
                  toTerm(var, lStart0, pos, trace),
                  toTerm(var, cachedTimepoint, pos, trace)));
        }

        conjPart1.push_back(f);
      }
    }

    conjuncts.push_back(logic::Formulas::conjunctionSimp(
        conjPart1, "Define variable values at beginning of loop"));

    // Part 2a: Loop condition holds at main-loop-location for all iterations
    // before n
    inliner.currTimepoint = lStartIt;
    for (const auto &var : assignedVars) {
      if (!var->isArray) {
        assert(!var->isConstant);
        auto result = inliner.setVarValue(var, toTerm(var, lStartIt, trace));
      } else {
        inliner.setArrayVarTimepoint(var, lStartIt);
      }
    }

    if (util::Configuration::instance().integerIterations()) {
      conjuncts.push_back(logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunction(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              inliner.toCachedTerm(whileStatement->condition)),
          "The loop-condition holds always before the last iteration"));
    } else {
      conjuncts.push_back(logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Theory::less(it, n),
              inliner.toCachedTerm(whileStatement->condition)),
          "The loop-condition holds always before the last iteration"));
    }

    // Extra part: collect in inlinedVarValues the values of all variables,
    // which occur in the loop condition but are not assigned to.
    inlinedVariableValues.initializeWhileStatement(whileStatement);
    std::unordered_set<std::shared_ptr<program::Variable>> loopConditionVars;
    AnalysisPreComputation::computeVariablesContainedInLoopCondition(
        whileStatement->condition, loopConditionVars);

    for (const auto &var : loopConditionVars) {
      if (assignedVars.find(var) == assignedVars.end()) {
        if (var->isArray) {
          inlinedVariableValues.setArrayTimepoint(
              whileStatement, var, trace,
              inliner.getCachedArrayVarTimepoints().at(var));
        } else {
          inlinedVariableValues.setValue(whileStatement, var, trace,
                                         inliner.getCachedVarValues().at(var));
        }
      }
    }

    // Part 3: collect all formulas describing semantics of the body, and define
    // values of assignedVars at all iterations s(it)
    assert(*inliner.currTimepoint == *lStartIt);

    std::vector<std::shared_ptr<const logic::Term>> conjunctsBody;
    for (const auto &statement : whileStatement->bodyStatements) {
      auto semanticsOfStatement =
          generateSemantics(statement.get(), inliner, trace);
      conjunctsBody.push_back(semanticsOfStatement);
    }

    inliner.currTimepoint = lStartSuccOfIt;
    for (const auto &var : assignedVars) {
      if (!var->isArray) {
        conjunctsBody.push_back(logic::Formulas::equalitySimp(
            toTerm(var, lStartSuccOfIt, trace), inliner.toCachedTermFull(var),
            "Define value of variable " + var->name +
                " at beginning of next iteration"));
      } else {
        conjunctsBody.push_back(logic::Formulas::universalSimp(
            {posSymbol},
            logic::Formulas::equalitySimp(
                toTerm(var, lStartSuccOfIt, pos, trace),
                inliner.toCachedTermFull(var, pos)),
            "Define value of array variable " + var->name +
                " at beginning of next iteration"));
      }
    }

    // Semantics of the body
    if (util::Configuration::instance().integerIterations()) {
      conjuncts.push_back(logic::Formulas::universalSimp(
          {itSymbol},
          logic::Formulas::implicationSimp(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              logic::Formulas::conjunctionSimp(conjunctsBody)),
          "Semantics of the body"));
    } else {
      conjuncts.push_back(logic::Formulas::universalSimp(
          {itSymbol},
          logic::Formulas::implicationSimp(
              logic::Theory::less(it, n),
              logic::Formulas::conjunctionSimp(conjunctsBody)),
          "Semantics of the body"));
    }

    // Part 4: define values of assignedVars after the execution of the loop
    inliner.currTimepoint = lStartN;
    for (const auto &var : assignedVars) {
      if (!var->isArray) {
        assert(!var->isConstant);
        auto result = inliner.setVarValue(var, toTerm(var, lStartN, trace));
      } else {
        inliner.setArrayVarTimepoint(var, lStartN);
      }
    }

    // Part 2b: loop condition doesn't hold at n
    assert(*inliner.currTimepoint == *lStartN);
    conjuncts.push_back(logic::Formulas::negation(
        inliner.toCachedTerm(whileStatement->condition),
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
    auto part1 = logic::Formulas::universal(
        {itSymbol},
        logic::Formulas::implication(
            logic::Theory::less(it, n),
            allVarEqual(activeVars, lBodyStartIt, lStartIt, trace)),
        "Jumping into the loop body doesn't change the variable values");
    if (util::Configuration::instance().integerIterations()) {
      part1 = logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              allVarEqual(activeVars, lBodyStartIt, lStartIt, trace)),
          "Jumping into the loop body doesn't change the variable values");
    }
    conjuncts.push_back(part1);

    // Part 2: collect all formulas describing semantics of body
    std::vector<std::shared_ptr<const logic::Term>> conjunctsBody;
    for (const auto &statement : whileStatement->bodyStatements) {
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
            toTerm(whileStatement->condition, lStartIt, trace)),
        "The loop-condition holds always before the last iteration");

    if (util::Configuration::instance().integerIterations()) {
      universal = logic::Formulas::universal(
          {itSymbol},
          logic::Formulas::implication(
              logic::Formulas::conjunctionSimp(
                  {logic::Theory::lessEq(logic::Theory::intZero(), it),
                   logic::Theory::less(it, n)}),
              toTerm(whileStatement->condition, lStartIt, trace)),
          "The loop-condition holds always before the last iteration");
    }
    conjuncts.push_back(universal);

    // loop condition doesn't hold at n
    auto negConditionAtN = logic::Formulas::negation(
        toTerm(whileStatement->condition, lStartN, trace),
        "The loop-condition doesn't hold in the last iteration");
    conjuncts.push_back(negConditionAtN);

    // Part 4: The values after the while-loop are the values from the timepoint
    // with location lStart and iteration n
    auto part4 = allVarEqual(activeVars, lEnd, lStartN, trace,
                             "The values after the while-loop are the values "
                             "from the last iteration");
    conjuncts.push_back(part4);

    return logic::Formulas::conjunction(
        conjuncts, "Loop at location " + whileStatement->location);
  }
}

std::shared_ptr<const logic::Term> Semantics::generateSemantics(
    program::SkipStatement *skipStatement, SemanticsInliner &inliner,
    std::shared_ptr<const logic::Term> trace) {
  auto l1 = startTimepointForStatement(skipStatement);

  if (util::Configuration::instance().inlineSemantics()) {
    inliner.currTimepoint = l1;
    return inliner.handlePersistence(l1,
                                     locationToActiveVars.at(l1->symbol->name));
  } else {
    auto l2 = endTimePointMap.at(skipStatement);

    // identify startTimePoint and endTimePoint
    auto eq = logic::Formulas::equality(l1, l2, "Ignore any skip statement");
    return eq;
  }
}
}  // namespace analysis