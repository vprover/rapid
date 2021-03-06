%skeleton "lalr1.cc" /* -*- C++ -*- */
%require "3.0"
%defines
%define api.namespace {parser}
%define api.parser.class {WhileParser}
%define api.token.constructor
%define api.value.type variant
%define parse.assert
%code requires
{
#include <cstring>
#include <iostream>
#include <vector>
#include <memory>

#include "Term.hpp"
#include "Formula.hpp"
#include "Theory.hpp"
#include "Problem.hpp"


#include "Expression.hpp"
#include "Variable.hpp"
#include "Statements.hpp"
#include "Program.hpp"

#include "Location.hpp"
#include "SymbolDeclarations.hpp"

#define YY_NULLPTR nullptr


namespace parser {
  class WhileParsingContext;
}
}

// The parsing parsing_context.
%param { parser::WhileParsingContext &parsing_context }
%locations
%define api.location.type {Location}
%initial-action
{
  // Initialize the initial location.
  @$.begin.filename = @$.end.filename = &parsing_context.inputFile;
};
%define parse.trace
%define parse.error verbose
%code
{
#include "WhileParsingContext.hpp"

using namespace program;

// Tell Flex the lexer's prototype ...
# define YY_DECL parser::WhileParser::symbol_type yylex(parser::WhileParsingContext &parsing_context)
// ... and declare it for the parser's sake.
YY_DECL;

}
%define api.token.prefix {TOK_}
%token
  END 0         "EOF"
  TRUE          "true"
  FALSE         "false"
  ASSIGN        "="
  IF            "if"
  ELSE          "else"
  WHILE         "while"
  BREAK         "break"
  CONTINUE      "continue"
  RETURN        "return"
  SKIP          "skip"
  FUNC          "func"
  LPAR          "("
  RPAR          ")"
  LBRA          "["
  RBRA          "]"
  LCUR          "{"
  RCUR          "}"
  SCOL          ";"
  NOT           "!"
  MUL           "*"
  PLUS          "+"
  MINUS         "-"
  MOD           "mod"
  GT            ">"
  GE            ">="
  LT            "<"
  LE            "<="
  EQ            "=="
  NEQ           "!="
  OR            "||"
  AND           "&&"
  ANDSMTLIB     "and"
  ORSMTLIB      "or"
  NOTSMTLIB     "not"
  IMPSMTLIB     "=>"
  FORALLSMTLIB  "forall"
  EXISTSSMTLIB  "exists"
  AXIOM         "axiom"
  LEMMA         "lemma"
  CONJECTURE    "conjecture"
  CONST         "const"
  SETTRACES     "set-traces"
;
%token <std::string> PROGRAM_ID "program identifier"
%token <std::string> SMTLIB_ID "smtlib identifier"
%token <std::string> TYPE "type identifier"
%token <int> INTEGER "number"

%type < std::vector<std::shared_ptr<const logic::ProblemItem> > > smtlib_problemitem_list
%type < std::shared_ptr<const logic::ProblemItem> > smtlib_problemitem

%type < std::vector<std::shared_ptr<const logic::Symbol>> > smtlib_quantvar_list
%type < std::shared_ptr<const logic::Symbol> > smtlib_quantvar
%type < std::vector<std::shared_ptr<const logic::Term>> > smtlib_term_list
%type < std::shared_ptr<const logic::Term> > smtlib_term


%type < std::shared_ptr<program::Program> > program
%type < std::vector< std::shared_ptr<program::Function>> > function_list
%type < std::shared_ptr<program::Function> > function

%type < std::shared_ptr<program::Variable> > var_definition_head

%type < std::vector<std::shared_ptr<program::Statement>> > statement_list
%type < std::shared_ptr<program::Statement> > statement
%type < std::vector<std::shared_ptr<program::Variable>> > active_vars_dummy
%type < std::shared_ptr<program::Assignment> > assignment_statement
%type < std::shared_ptr<program::IfElseStatement> > if_else_statement
%type < std::shared_ptr<program::WhileStatement> > while_statement
%type < std::shared_ptr<program::BreakStatement> > break_statement
%type < std::shared_ptr<program::ContinueStatement> > continue_statement
%type < std::shared_ptr<program::ReturnStatement> > return_statement
%type < std::shared_ptr<program::SkipStatement> > skip_statement

%type < std::shared_ptr<program::Expression> > expr
%type < std::shared_ptr<program::Expression> > location

%printer { yyoutput << $$; } <*>;

%right ASSIGN
%left  AND
%left  OR
%left  EQ NEQ
%left  GT GE LT LE
%left  PLUS MINUS
%left  MUL DIV MOD
%right NOT UMINUS

%%

%start problem;

problem:
  {
    logic::Theory::declareTheories();
  }
  program smtlib_problemitem_list
  {
    parsing_context.problemItems = $3;
  }
|
  LPAR SETTRACES INTEGER RPAR
  {
    if ($3 < 1)
    {
      error(@3, "number of traces has to be greater than or equal to 1");
    }

    parsing_context.numberOfTraces = (unsigned) $3;
    logic::Theory::declareTheories();
    declareSymbolsForTraces(parsing_context.numberOfTraces);
  }
  program smtlib_problemitem_list
  {
        parsing_context.problemItems = $7;
  }
;

program:
  function_list 
  { 
    parsing_context.program = std::unique_ptr<program::Program>(new program::Program($1)); 
  }
;

smtlib_problemitem_list:
  %empty {$$ = std::vector<std::shared_ptr<const logic::ProblemItem>>();}
| smtlib_problemitem_list smtlib_problemitem {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_problemitem:
  LPAR AXIOM smtlib_term RPAR
  {
    $$ = std::shared_ptr<const logic::Axiom>(new logic::Axiom($3, "user-axiom-" + std::to_string(parsing_context.numberOfAxioms)));
    parsing_context.numberOfAxioms++;
  }
|
  LPAR LEMMA smtlib_term RPAR
  {
    $$ = std::shared_ptr<const logic::Lemma>(new logic::Lemma($3, "user-lemma-" + std::to_string(parsing_context.numberOfLemmas)));
    parsing_context.numberOfLemmas++;
  }
|
  LPAR CONJECTURE smtlib_term RPAR
  {
    $$ = std::shared_ptr<const logic::Conjecture>(new logic::Conjecture($3, "user-conjecture-" + std::to_string(parsing_context.numberOfConjectures)));
    parsing_context.numberOfConjectures++;
  }
;

smtlib_term_list:
  %empty {$$ = std::vector<std::shared_ptr<const logic::Term>>();}
|  smtlib_term {$$ = std::vector<std::shared_ptr<const logic::Term>>(); $$.push_back($1);}
| smtlib_term_list smtlib_term {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_term:
SMTLIB_ID
{
  if (!parsing_context.isDeclared($1))
  {
    error(@1, $1 + " has not been declared");
  }
  auto symbol = parsing_context.fetch($1);

  if (symbol->argSorts.size() > 0)
  {
      error(@1, "Not enough arguments for term " + symbol->name);
  }
  if (symbol->rngSort == logic::Sorts::boolSort())
  {
    $$ = logic::Formulas::predicate(symbol, std::vector<std::shared_ptr<const logic::Term>>());
  }
  else
  {
    $$ = logic::Terms::func(symbol, std::vector<std::shared_ptr<const logic::Term>>());
  }
}
| INTEGER
  {
    $$ = logic::Theory::intConstant($1);
  }
| LPAR SMTLIB_ID smtlib_term_list RPAR
{
  if (!parsing_context.isDeclared($2))
  {
    error(@2, $2 + " has not been declared");
  }
  auto symbol = parsing_context.fetch($2);

  if ($3.size() < symbol->argSorts.size())
  {
      error(@3, "Not enough arguments for term " + symbol->name);
  }
  if ($3.size() > symbol->argSorts.size())
  {
      error(@3, "Too many arguments for term " + symbol->name);
  }
  for (int i = 0; i < symbol->argSorts.size(); ++i)
  {
      if (symbol->argSorts[i] != $3[i]->symbol->rngSort)
      {
        error(@3, "Argument has type " + $3[i]->symbol->rngSort->name + " instead of " + symbol->argSorts[i]->name);
      }
  }
  if (symbol->rngSort == logic::Sorts::boolSort())
  {
    $$ = logic::Formulas::predicate(symbol, std::move($3));
  }
  else
  {
    $$ = logic::Terms::func(symbol, std::move($3));
  }
}
| LPAR PLUS smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intAddition(std::move($3), std::move($4));
}
| LPAR MINUS smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intSubtraction(std::move($3), std::move($4));
}
| LPAR MOD smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intModulo(std::move($3), std::move($4));
}
| LPAR MUL smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intMultiplication(std::move($3), std::move($4));
}
| TRUE                                       { $$ = logic::Theory::boolTrue();}
| FALSE                                      { $$ = logic::Theory::boolFalse();}
| LPAR ASSIGN smtlib_term smtlib_term RPAR
  {
    auto leftSort = $3->symbol->rngSort;
    auto rightSort = $4->symbol->rngSort;

    if (leftSort != rightSort)
    {
      error(@4, "Argument types " + leftSort->name + " and " + rightSort->name + " don't match!");
    }
    $$ = logic::Formulas::equality(std::move($3), std::move($4));
  }
| LPAR GT smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intGreater(std::move($3), std::move($4));
}
| LPAR GE smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intGreaterEqual(std::move($3), std::move($4));
}
| LPAR LT smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intLess(std::move($3), std::move($4));
}
| LPAR LE smtlib_term smtlib_term RPAR
{
  if ($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if ($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intLessEqual(std::move($3), std::move($4));
}
| LPAR ANDSMTLIB smtlib_term_list RPAR    { $$ = logic::Formulas::conjunction(std::move($3));}
| LPAR ORSMTLIB smtlib_term_list RPAR     { $$ = logic::Formulas::disjunction(std::move($3));}
| LPAR NOTSMTLIB smtlib_term RPAR         { $$ = logic::Formulas::negation(std::move($3));}
| LPAR IMPSMTLIB smtlib_term smtlib_term RPAR  { $$ = logic::Formulas::implication(std::move($3), std::move($4));}
| LPAR FORALLSMTLIB LPAR smtlib_quantvar_list RPAR
  {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars($4);
  } 
  smtlib_term RPAR 
  { 
    parsing_context.popQuantifiedVars();
    $$ = logic::Formulas::universal(std::move($4), std::move($7));
  }
| LPAR EXISTSSMTLIB LPAR smtlib_quantvar_list RPAR
  {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars($4);
  } 
  smtlib_term RPAR 
  { 
    parsing_context.popQuantifiedVars();
    $$ = logic::Formulas::existential(std::move($4), std::move($7));
  }
;

smtlib_quantvar_list:
  smtlib_quantvar {auto vec = std::vector<std::shared_ptr<const logic::Symbol>>(); vec.push_back(std::move($1)); $$ = std::move(vec);}
| smtlib_quantvar_list smtlib_quantvar {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_quantvar:
  LPAR SMTLIB_ID TYPE RPAR 
  { 
    if(parsing_context.isDeclared($2))
    {
      error(@2, $2 + " has already been declared");
    }
    if ($3 == "Int")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::intSort());
    }
    else if ($3 == "Bool")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::boolSort());
    }
    else if ($3 == "Nat")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::natSort());
    }
    else if ($3 == "Time")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::timeSort());
    }
    else
    {
      if ($3 != "Trace")
      {
        error(@3, "Only the sorts Int, Bool, Time and Trace are supported");
      }
      $$ = logic::Signature::varSymbol($2, logic::Sorts::traceSort());
    }
  }
;

function_list:
  function             	  {auto v = std::vector< std::shared_ptr<program::Function>>(); v.push_back(std::move($1)); $$ = std::move(v);}
| function_list function  {$1.push_back(std::move($2)); $$ = std::move($1);}
;

function:
  FUNC PROGRAM_ID LPAR RPAR LCUR
  {
    parsing_context.pushProgramVars();
  }
  statement_list RCUR
  {
    auto functionEndLocationName = $2 + "_end";
    parsing_context.locationToActiveVars[functionEndLocationName] = parsing_context.getActiveProgramVars();
    parsing_context.popProgramVars();

  	auto function = std::shared_ptr<program::Function>(new program::Function($2, std::move($7)));

    // compute enclosing loops
    parsing_context.addEnclosingLoops(*function);
    $$ = function;

    // declare symbols for loops (needs to be done here, since it depends on enclosingLoops)
    declareSymbolsForFunction(function.get(), parsing_context.numberOfTraces);
  }
;

statement_list:
  %empty {$$ = std::vector<std::shared_ptr<program::Statement>>();}
| statement_list active_vars_dummy statement
  {
    auto locationName = $3->location;
    parsing_context.locationToActiveVars[locationName] = $2;
    $1.push_back(std::move($3)); $$ = std::move($1);
  }
| statement_list active_vars_dummy var_definition_head SCOL
  {
    // dummy is not used here, but silences a shift-reduce conflict
    parsing_context.addProgramVar($3);
    declareSymbolForProgramVar($3.get());
    $$ = std::move($1);
  }
;

statement:
  assignment_statement {$$ = std::move($1);}
| if_else_statement {$$ = std::move($1);}
| while_statement {$$ = std::move($1);}
| break_statement {$$ = std::move($1);}
| continue_statement {$$ = std::move($1);}
| return_statement {$$ = std::move($1);}
| skip_statement {$$ = std::move($1);}
;

assignment_statement:
  location ASSIGN expr SCOL
  {
    if (typeid(*$1) == typeid(VariableAccess))
    {
      auto variableAccess = std::static_pointer_cast<program::VariableAccess>($1);
      if (variableAccess->var->isConstant)
      {
        error(@1, "Assignment to const var " + variableAccess->var->name);
      }
    }
    else
    {
      assert(typeid(*$1) == typeid(ArrayApplication));
      auto arrayApplication = std::static_pointer_cast<program::ArrayApplication>($1);
      if (arrayApplication->array->isConstant)
      {
        error(@1, "Assignment to const var " + arrayApplication->array->name);
      }
    }
    $$ = std::shared_ptr<program::Assignment>(new program::Assignment(@2.begin.line, std::move($1), std::move($3)));
  }
| var_definition_head ASSIGN expr SCOL
  {
    // declare var
    parsing_context.addProgramVar($1);
    declareSymbolForProgramVar($1.get());

    // construct location
    if ($1->isArray)
    {
      error(@1, "Combined declaration and assignment not allowed, since " + $1->name + " is array variable");
    }
    auto variableAccess = std::shared_ptr<program::VariableAccess>(new VariableAccess(std::move($1)));

    // build assignment
    $$ = std::shared_ptr<program::Assignment>(new program::Assignment(@2.begin.line, std::move(variableAccess), std::move($3)));
  }
;

if_else_statement:
  IF LPAR expr RPAR push_dummy LCUR
  statement_list active_vars_dummy RCUR
  pop_dummy
  {
    auto leftEndLocationName = "l" + std::to_string(@1.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(@1.begin.line) + "_rEnd";
    parsing_context.locationToActiveVars[leftEndLocationName] = $8;
    parsing_context.locationToActiveVars[rightEndLocationName] = parsing_context.getActiveProgramVars();
    std::vector<std::shared_ptr<program::Statement>> emptyElse;
    auto skipStatement = std::shared_ptr<program::SkipStatement>(new program::SkipStatement(0));
    parsing_context.locationToActiveVars[skipStatement->location] = parsing_context.getActiveProgramVars();
    emptyElse.push_back(std::move(skipStatement));
    $$ = std::shared_ptr<program::IfElseStatement>(new program::IfElseStatement(@1.begin.line, std::move($3), std::move($7), std::move(emptyElse)));
  }
| IF LPAR expr RPAR push_dummy LCUR
  statement_list active_vars_dummy RCUR
  pop_dummy ELSE push_dummy LCUR
  statement_list active_vars_dummy RCUR
  pop_dummy
  {
    auto leftEndLocationName = "l" + std::to_string(@1.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(@1.begin.line) + "_rEnd";
    parsing_context.locationToActiveVars[leftEndLocationName] = $8;
    parsing_context.locationToActiveVars[rightEndLocationName] = $15;
    $$ = std::shared_ptr<program::IfElseStatement>(new program::IfElseStatement(@1.begin.line, std::move($3), std::move($7), std::move($14)));
  }
;

while_statement:
  WHILE expr
  {
    parsing_context.pushProgramVars();
  }
  LCUR statement_list RCUR
  {
    parsing_context.popProgramVars();
    $$ = std::shared_ptr<program::WhileStatement>(new program::WhileStatement(@1.begin.line, std::move($2), std::move($5)));
  }
;

break_statement:
  BREAK SCOL
  {
    $$ = std::shared_ptr<program::BreakStatement>(new program::BreakStatement(@2.begin.line));
  }
;

continue_statement:
  CONTINUE SCOL {
    $$ = std::shared_ptr<program::ContinueStatement>(new program::ContinueStatement(@2.begin.line));
  }
;

return_statement:
  RETURN expr SCOL {
    $$ = std::shared_ptr<program::ReturnStatement>(new program::ReturnStatement(@2.begin.line, std::move($2)));
  }
;

skip_statement:
  SKIP SCOL {$$ = std::shared_ptr<program::SkipStatement>(new program::SkipStatement(@1.begin.line));}
;

active_vars_dummy:
  %empty
  {
    $$ = parsing_context.getActiveProgramVars();
  }
;

push_dummy:
  %empty
  {
    parsing_context.pushProgramVars();
  }
;

pop_dummy:
  %empty
  {
    parsing_context.popProgramVars();
  }
;

var_definition_head:
  TYPE PROGRAM_ID
  {
    if ($1 == "Bool")
    {
      $$ = std::shared_ptr<program::Variable>(new program::BoolVariable($2, false, false, parsing_context.numberOfTraces));
    }
    else if ($1 == "Nat" || $1 == "Time" || $1 == "Trace")
    {
      error(@1, "Program variables can't have type " + $1);
    }
    else
    {
      $$ = std::shared_ptr<program::Variable>(new program::IntVariable($2, false, false, parsing_context.numberOfTraces));
    }
  }
| CONST TYPE PROGRAM_ID
  {
    if ($2 == "Bool")
    {
      $$ = std::shared_ptr<program::Variable>(new program::BoolVariable($3, true, false, parsing_context.numberOfTraces));
    }
    else if ($2 == "Nat" || $2 == "Time" || $2 == "Trace")
    {
      error(@2, "Program variables can't have type " + $2);
    }
    else
    {
      $$ = std::shared_ptr<program::Variable>(new program::IntVariable($3, true, false, parsing_context.numberOfTraces));
    }
  }
| TYPE LBRA RBRA PROGRAM_ID
  {
    if ($1 == "Bool")
    {
      $$ = std::shared_ptr<program::Variable>(new program::BoolVariable($4, false, true, parsing_context.numberOfTraces));
    }
    else if ($1 == "Nat" || $1 == "Time" || $1 == "Trace")
    {
      error(@1, "Program variables can't have type " + $1);
    }
    else
    {
      $$ = std::shared_ptr<program::Variable>(new program::IntVariable($4, false, true, parsing_context.numberOfTraces));
    }
  }
| CONST TYPE LBRA RBRA PROGRAM_ID
  {
    if ($2 == "Bool")
    {
      $$ = std::shared_ptr<program::Variable>(new program::BoolVariable($5, true, true, parsing_context.numberOfTraces));
    }
    else if ($2 == "Nat" || $2 == "Time" || $2 == "Trace")
    {
      error(@2, "Program variables can't have type " + $2);
    }
    else
    {
      $$ = std::shared_ptr<program::Variable>(new program::IntVariable($5, true, true, parsing_context.numberOfTraces));
    }
  }
;

expr:
  LPAR expr RPAR           { $$ = std::move($2); }
| location                 { $$ = std::move($1); }
| TRUE                     { $$ = std::shared_ptr<program::BooleanConstant>(new program::BooleanConstant(true)); }
| FALSE                    { $$ = std::shared_ptr<program::BooleanConstant>(new program::BooleanConstant(false)); }
| INTEGER                  { $$ = std::shared_ptr<program::ArithmeticConstant>(new program::ArithmeticConstant(std::move($1)));}
| expr MUL expr            { $$ = std::shared_ptr<program::Multiplication>(new program::Multiplication(std::move($1), std::move($3)));}
| expr PLUS expr           { $$ = std::shared_ptr<program::Addition>(new program::Addition(std::move($1), std::move($3)));}
| expr MINUS expr          { $$ = std::shared_ptr<program::Subtraction>(new program::Subtraction(std::move($1), std::move($3)));}
| expr MOD expr            { $$ = std::shared_ptr<program::Modulo>(new program::Modulo(std::move($1), std::move($3)));}

| expr GT expr             { $$ = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GT, std::move($1), std::move($3)));}
| expr GE expr             { $$ = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GE, std::move($1), std::move($3)));}
| expr LT expr             { $$ = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LT, std::move($1), std::move($3)));}
| expr LE expr             { $$ = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LE, std::move($1), std::move($3)));}
| expr EQ expr             { $$ = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move($1), std::move($3)));}
| expr NEQ expr            { auto formula = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move($1), std::move($3)));
                             $$ = std::shared_ptr<program::BooleanNot>(new program::BooleanNot(std::move(formula)));}
| expr AND expr            { $$ = std::shared_ptr<program::BooleanAnd>(new program::BooleanAnd(std::move($1), std::move($3)));}
| expr OR expr             { $$ = std::shared_ptr<program::BooleanOr>(new program::BooleanOr(std::move($1), std::move($3)));}
| NOT expr                 { $$ = std::shared_ptr<program::BooleanNot>(new program::BooleanNot(std::move($2)));}

;

location:
  PROGRAM_ID                
  { 
  	auto var = parsing_context.getProgramVar($1);
    if(var->isArray)
    {
      error(@1, "Array variable " + var->name + " needs index for access");
    }
    $$ = std::shared_ptr<program::VariableAccess>(new VariableAccess(std::move(var)));
  }
| PROGRAM_ID LBRA expr RBRA
  {
	  auto var = parsing_context.getProgramVar($1);
    if(!var->isArray)
    {
      error(@1, "Variable " + var->name + " is not an array");
    }
    $$ = std::shared_ptr<program::ArrayApplication>(new ArrayApplication(std::move(var), std::move($3)));
  }
;

%%
void parser::WhileParser::error(const location_type& l,
                              const std::string& m)
{
  std::cout << "Error while parsing location " << l << ":\n" << m << std::endl;
  parsing_context.errorFlag = true;
  exit(1);
}
