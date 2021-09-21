#ifndef __SymbolDeclarations__
#define __SymbolDeclarations__

#include "Program.hpp"
#include "Signature.hpp"
#include "Statements.hpp"

std::shared_ptr<const logic::Symbol> locationSymbolForStatement(
    program::Statement* statement);
std::shared_ptr<const logic::Symbol> locationSymbolEndLocation(
    const program::Function* function);

std::shared_ptr<const logic::Symbol> iteratorSymbol(
    program::WhileStatement* whileStatement);
std::shared_ptr<const logic::Symbol> lastIterationSymbol(
    program::WhileStatement* whileStatement, unsigned numberOfTraces);

std::shared_ptr<const logic::Symbol> intIteratorSymbol(
    program::WhileStatement* whileStatement);
std::shared_ptr<const logic::Symbol> intLastIterationSymbol(
    program::WhileStatement* whileStatement, unsigned numberOfTraces);

std::shared_ptr<const logic::Symbol> posVarSymbol();
std::shared_ptr<const logic::Symbol> declareInitTargetSymbol(
    const program::Variable* var);
std::shared_ptr<const logic::Symbol> declareFinalTargetSymbol(
    const program::Variable* var);
void declareColorSymbolLeft(const program::Variable* var);

std::shared_ptr<const logic::Symbol> traceSymbol(unsigned traceNumber);

/*
 * The parser needs to declare itself the symbols corresponding to variables,
 * locations, last-loop-iterations and (if enabled) traces, since later parts of
 * the parsing (i.e. the smtlib-formula-parsing) require those declarations to
 * exist already. program variables are declared on the fly during parsing (at
 * least for now), (if enabled) traces are declared immediately after parsing
 * (two-traces), and all other symbols are declared per function whenever the
 * function-parsing is finished.
 */
void declareSymbolForProgramVar(program::Variable* var);
void declareSymbolsForTraces(unsigned numberOfTraces);
void declareSymbolsForFunction(const program::Function* function,
                               unsigned numberOfTraces);
// helper method for declareSymbolsForFunction
void declareSymbolsForStatements(program::Statement* statement,
                                 unsigned numberOfTraces);

#endif
