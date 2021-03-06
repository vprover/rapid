#ifndef __SemanticsHelper__
#define __SemanticsHelper__

#include <memory>
#include <string>
#include <vector>

#include "Formula.hpp"
#include "Statements.hpp"
#include "Term.hpp"
#include "Variable.hpp"

namespace analysis {

#pragma mark - Methods for generating most used variables
std::shared_ptr<const logic::LVariable> posVar();

#pragma mark - Methods for generating most used trace terms
std::shared_ptr<const logic::Term> traceTerm(unsigned traceNumber);
std::vector<std::shared_ptr<const logic::Term>> traceTerms(
    unsigned numberOfTraces);

#pragma mark - Methods for generating color and target symbols for symbol elimination
// adds initial target symbol to signature and returns the symbol to add
// assertion
std::shared_ptr<const logic::LVariable> initTargetSymbol(
    const program::Variable* var);
// adds final target symbol to signature and returns the symbol to add assertion
std::shared_ptr<const logic::LVariable> finalTargetSymbol(
    const program::Variable* var);
// adds color symbol left to signature
void colorSymbol(const program::Variable* var);
// generate equality assertion for target symbol and trace logic pendant
std::shared_ptr<const logic::Term> defineTargetSymbol(
    std::shared_ptr<const logic::LVariable> target,
    std::shared_ptr<program::Variable> origin,
    std::shared_ptr<const logic::Term> tp);

#pragma mark - Methods for generating most used timepoint terms and symbols
std::shared_ptr<const logic::LVariable> iteratorTermForLoop(
    program::WhileStatement* whileStatement);
std::shared_ptr<const logic::Term> lastIterationTermForLoop(
    program::WhileStatement* whileStatement, unsigned numberOfTraces,
    std::shared_ptr<const logic::Term> trace);

std::shared_ptr<const logic::Term> timepointForNonLoopStatement(
    program::Statement* statement);
std::shared_ptr<const logic::Term> timepointForLoopStatement(
    program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> innerIteration);

std::shared_ptr<const logic::Term> startTimepointForStatement(
    program::Statement* statement);

std::vector<std::shared_ptr<const logic::Symbol>> enclosingIteratorsSymbols(
    program::Statement* statement);

#pragma mark - Methods for generating most used timepoint terms and symbols in integer sort
std::shared_ptr<const logic::LVariable> intIteratorTermForLoop(
    program::WhileStatement* whileStatement);
std::shared_ptr<const logic::Term> intLastIterationTermForLoop(
    program::WhileStatement* whileStatement, unsigned numberOfTraces,
    std::shared_ptr<const logic::Term> trace);

std::shared_ptr<const logic::Term> intTimepointForNonLoopStatement(
    program::Statement* statement);
std::shared_ptr<const logic::Term> intTimepointForLoopStatement(
    program::WhileStatement* whileStatement,
    std::shared_ptr<const logic::Term> innerIteration);

std::shared_ptr<const logic::Term> intStartTimepointForStatement(
    program::Statement* statement);

std::vector<std::shared_ptr<const logic::Symbol>> intEnclosingIteratorsSymbols(
    const program::Statement* statement);

#pragma mark - Methods for generating most used formulas

std::shared_ptr<const logic::Term> getDensityFormula(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    std::string nameSuffix, bool increasing);

std::shared_ptr<const logic::Term> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<program::Expression> expr,
    std::string nameSuffix, std::shared_ptr<const logic::Symbol> itSymbol,
    std::shared_ptr<const logic::LVariable> it,
    std::shared_ptr<const logic::Term> lStartIt,
    std::shared_ptr<const logic::Term> lStartSuccOfIt,
    std::shared_ptr<const logic::Term> n,
    std::shared_ptr<const logic::Term> trace, bool increasing);

// TODO remove duplication
std::shared_ptr<const logic::Term> getDensityDefinition(
    std::vector<std::shared_ptr<const logic::Symbol>> freeVarSymbols,
    const std::shared_ptr<program::Variable> var, std::string nameSuffix,
    std::shared_ptr<const logic::Symbol> itSymbol,
    std::shared_ptr<const logic::LVariable> it,
    std::shared_ptr<const logic::Term> lStartIt,
    std::shared_ptr<const logic::Term> lStartSuccOfIt,
    std::shared_ptr<const logic::Term> n,
    std::shared_ptr<const logic::Term> trace, bool increasing);

#pragma mark - Methods for generating most used terms/predicates denoting program-expressions
/*
 * convert a program variable to a logical term referring to the value of
 * Variable var at the Timepoint timepoint in the Trace trace. The first version
 * must only be used for non-array variables, the second version must only be
 * used for array-variables (where position refers to the position in the
 * array).
 */
std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Variable> var,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace);
std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Variable> arrayVar,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> position,
    std::shared_ptr<const logic::Term> trace);

/*
 * convert the expression expr to a logical term referring to the value of the
 * Expression expr at the Timepoint timepoint. calls toTerm(var,...) internally.
 */
std::shared_ptr<const logic::Term> toTerm(
    std::shared_ptr<program::Expression> expr,
    std::shared_ptr<const logic::Term> timePoint,
    std::shared_ptr<const logic::Term> trace);

#pragma mark - Methods for generating most used formulas for describing changes of state
/*
 * generate a formula asserting that the values of variable v at timepoint1 and
 * timepoint2 are the same.
 */
std::shared_ptr<const logic::Term> varEqual(
    std::shared_ptr<program::Variable> v,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace);
/*
 * generate a formula asserting that for each variable v in activeVars, the
 * values of v at timepoint1 and timepoint2 are the same. ignores any v in
 * activeVars which is constant.
 */
std::shared_ptr<const logic::Term> allVarEqual(
    const std::vector<std::shared_ptr<program::Variable>>& activeVars,
    std::shared_ptr<const logic::Term> timePoint1,
    std::shared_ptr<const logic::Term> timePoint2,
    std::shared_ptr<const logic::Term> trace, std::string label = "");
}  // namespace analysis

#endif
