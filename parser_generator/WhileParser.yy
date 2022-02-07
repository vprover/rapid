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
  REFERENCE     "#"
  ARROW         "->"
  MALLOC        "malloc()"
  NULL          "NULL"
  DOT           "."
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
  STRUCT        "struct"
  SETTRACES     "set-traces"
;
%token <std::string> PROGRAM_ID "program identifier"
%token <std::string> SMTLIB_ID "smtlib identifier"
%token <std::string> STRUCT_NAME "struct name"
%token <std::string> TYPE "type identifier"
%token <int> INTEGER "number"

%type < std::vector<std::shared_ptr<const logic::ProblemItem> > > smtlib_problemitem_list
%type < std::shared_ptr<const logic::ProblemItem> > smtlib_problemitem

%type < std::vector<std::shared_ptr<const logic::Formula>> > smtlib_formula_list
%type < std::shared_ptr<const logic::Formula> > smtlib_formula
%type < std::vector<std::shared_ptr<const logic::Symbol>> > smtlib_quantvar_list
%type < std::shared_ptr<const logic::Symbol> > smtlib_quantvar
%type < std::vector<std::shared_ptr<const logic::Term>> > smtlib_term_list
%type < std::shared_ptr<const logic::Term> > smtlib_term


%type < std::shared_ptr<const program::Program> > program
%type < std::vector< std::shared_ptr<const program::Function>> > function_list
%type < std::shared_ptr<const program::Function> > function
%type < std::vector< std::shared_ptr<const program::ExprType>> > struct_decl_list
%type < std::list< std::shared_ptr<const program::Variable>> > field_list
%type < std::shared_ptr<const program::Variable> > field

%type < std::shared_ptr<const program::Variable> > var_definition_head

%type < std::vector<std::shared_ptr<const program::Statement>> > statement_list
%type < std::shared_ptr<const program::Statement> > statement
%type < std::vector<std::shared_ptr<const program::Variable>> > active_vars_dummy
%type < std::shared_ptr<const program::VarDecl> > var_decl_statement
%type < std::shared_ptr<const program::Assignment> > assignment_statement
%type < std::shared_ptr<const program::IfElse> > if_else_statement
%type < std::shared_ptr<const program::WhileStatement> > while_statement
%type < std::shared_ptr<const program::SkipStatement> > skip_statement

%type < std::shared_ptr<const program::ExprType>> type_dec
%type < std::shared_ptr<const program::ExprType>> struct_dec

%type < std::shared_ptr<const program::BoolExpression> > formula
%type < std::shared_ptr<const program::Expression> > expr
%type < std::shared_ptr<const program::Expression> > location
%type < std::shared_ptr<const program::Expression> > malloc_or_null

%printer { yyoutput << $$; } <*>;

%right ASSIGN
%left  AND
%left  OR
%left  EQ NEQ
%left  GT GE LT LE
%left  PLUS MINUS
%left  ARROW DOT
%left  MUL DIV MOD
%right NOT UMINUS


%%

%start problem;

problem:
  {
    logic::Theory::declareTheories();
    logic::Theory::declareMemoryArrays();
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
    logic::Theory::declareMemoryArrays();    
    declareSymbolsForTraces(parsing_context.numberOfTraces);
  }
  program smtlib_problemitem_list 
  {
        parsing_context.problemItems = $7;
  }
;

program:
  struct_decl_list function_list 
  { 
    parsing_context.program = std::unique_ptr<const program::Program>(new program::Program($2)); 
  }
;

smtlib_problemitem_list:
  %empty {$$ = std::vector<std::shared_ptr<const logic::ProblemItem>>();}
| smtlib_problemitem_list smtlib_problemitem {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_problemitem:
  LPAR AXIOM smtlib_formula RPAR 
  {
    $$ = std::shared_ptr<const logic::Axiom>(new logic::Axiom($3, "user-axiom-" + std::to_string(parsing_context.numberOfAxioms)));
    parsing_context.numberOfAxioms++;
  }
|
  LPAR LEMMA smtlib_formula RPAR 
  {
    $$ = std::shared_ptr<const logic::Lemma>(new logic::Lemma($3, "user-lemma-" + std::to_string(parsing_context.numberOfLemmas)));
    parsing_context.numberOfLemmas++;
  }
|
  LPAR CONJECTURE smtlib_formula RPAR 
  {
    $$ = std::shared_ptr<const logic::Conjecture>(new logic::Conjecture($3, "user-conjecture-" + std::to_string(parsing_context.numberOfConjectures)));
    parsing_context.numberOfConjectures++;
  }

smtlib_formula_list:
  %empty {$$ = std::vector<std::shared_ptr<const logic::Formula>>();}
| smtlib_formula_list smtlib_formula {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_formula:
  TRUE                                       { $$ = logic::Theory::boolTrue();}
| FALSE                                      { $$ = logic::Theory::boolFalse();}
| LPAR ASSIGN smtlib_term smtlib_term RPAR   
  { 
    auto leftSort = $3->symbol->rngSort;
    auto rightSort = $4->symbol->rngSort;
    
    if(leftSort != rightSort)
    {
      error(@4, "Argument types " + leftSort->name + " and " + rightSort->name + " don't match!");
    }
    $$ = logic::Formulas::equality(std::move($3), std::move($4));
  }
| LPAR GT smtlib_term smtlib_term RPAR       
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  }
  $$ = logic::Theory::intGreater(std::move($3), std::move($4));
}
| LPAR GE smtlib_term smtlib_term RPAR       
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intGreaterEqual(std::move($3), std::move($4));
}
| LPAR LT smtlib_term smtlib_term RPAR      
{ 
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intLess(std::move($3), std::move($4));
}
| LPAR LE smtlib_term smtlib_term RPAR      
{ 
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intLessEqual(std::move($3), std::move($4));
}
| LPAR ANDSMTLIB smtlib_formula_list RPAR    { $$ = logic::Formulas::conjunction(std::move($3));}
| LPAR ORSMTLIB smtlib_formula_list RPAR     { $$ = logic::Formulas::disjunction(std::move($3));}
| LPAR NOTSMTLIB smtlib_formula RPAR         { $$ = logic::Formulas::negation(std::move($3));}
| LPAR IMPSMTLIB smtlib_formula smtlib_formula RPAR  { $$ = logic::Formulas::implication(std::move($3), std::move($4));}
| LPAR FORALLSMTLIB LPAR smtlib_quantvar_list RPAR 
  {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars($4);
  } 
  smtlib_formula RPAR 
  { 
    parsing_context.popQuantifiedVars();
    $$ = logic::Formulas::universal(std::move($4), std::move($7));
  }
| LPAR EXISTSSMTLIB LPAR smtlib_quantvar_list RPAR 
  {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars($4);
  } 
  smtlib_formula RPAR 
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
    if($3 == "Int")
    { 
      $$ = logic::Signature::varSymbol($2, logic::Sorts::intSort());
    }
    else if($3 == "Bool")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::boolSort());
    }
    else if($3 == "Nat")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::natSort());
    }
    else if($3 == "Time")
    {
      $$ = logic::Signature::varSymbol($2, logic::Sorts::timeSort());
    }
    else
    {
      if($3 != "Trace")
      {
        error(@3, "Only the sorts Int, Bool, Time and Trace are supported");
      }
      $$ = logic::Signature::varSymbol($2, logic::Sorts::traceSort());
    }
  }
;

smtlib_term_list:
  smtlib_term {$$ = std::vector<std::shared_ptr<const logic::Term>>(); $$.push_back($1);}
| smtlib_term_list smtlib_term {$1.push_back(std::move($2)); $$ = std::move($1);}
;

smtlib_term:
SMTLIB_ID                               
{
  if(!parsing_context.isDeclared($1))
  {
    error(@1, $1 + " has not been declared");
  }
  auto symbol = parsing_context.fetch($1); 

  if(symbol->argSorts.size() > 0)
  {
    error(@1, "Not enough arguments for term " + symbol->name);
  }
  $$ = logic::Terms::func(symbol, std::vector<std::shared_ptr<const logic::Term>>());
}
| INTEGER                                 
  {
    $$ = logic::Theory::intConstant($1);
  }
| LPAR SMTLIB_ID smtlib_term_list RPAR    
{
  if(!parsing_context.isDeclared($2))
  {
    error(@2, $2 + " has not been declared");
  }
  auto symbol = parsing_context.fetch($2); 

  if($3.size() < symbol->argSorts.size())
  {
      error(@3, "Not enough arguments for term " + symbol->name);
  }
  if($3.size() > symbol->argSorts.size())
  {
      error(@3, "Too many arguments for term " + symbol->name);
  }
  for (int i=0; i < symbol->argSorts.size(); ++i)
  {
      if(symbol->argSorts[i] != $3[i]->symbol->rngSort)
      {
        error(@3, "Argument has type " + $3[i]->symbol->rngSort->name + " instead of " + symbol->argSorts[i]->name);
      }
  }
  $$ = logic::Terms::func(symbol, std::move($3));
}
| LPAR PLUS smtlib_term smtlib_term RPAR 
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intAddition(std::move($3), std::move($4));
}
| LPAR MINUS smtlib_term smtlib_term RPAR 
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intSubtraction(std::move($3), std::move($4));
}
| LPAR MOD smtlib_term smtlib_term RPAR 
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intModulo(std::move($3), std::move($4));
}
| LPAR MUL smtlib_term smtlib_term RPAR 
{
  if($3->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@3, "Left argument type needs to be Int");
  }
  if($4->symbol->rngSort != logic::Sorts::intSort())
  {
    error(@4, "Right argument type needs to be Int");
  } 
  $$ = logic::Theory::intMultiplication(std::move($3), std::move($4));
}
;

struct_decl_list:
  struct_dec               
  {  
    auto v = std::vector< std::shared_ptr<const program::ExprType>>(); 
    v.push_back(std::move($1)); 
    $$ = std::move(v);
  }
| struct_decl_list struct_dec  {$1.push_back(std::move($2)); $$ = std::move($1);}
;

function_list:
  function             	  {auto v = std::vector< std::shared_ptr<const program::Function>>(); v.push_back(std::move($1)); $$ = std::move(v);}
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

  	auto function = std::shared_ptr<const program::Function>(new program::Function($2, std::move($7)));

    // compute enclosing loops
    parsing_context.addEnclosingLoops(*function);
    $$ = function;

    // declare symbols for loops (needs to be done here, since it depends on enclosingLoops)
    declareSymbolsForFunction(function.get(), parsing_context.numberOfTraces);
  }
;

statement_list:
  %empty {$$ = std::vector<std::shared_ptr<const program::Statement>>();}
| statement_list active_vars_dummy statement
  {
    auto locationName = $3->location;
    parsing_context.locationToActiveVars[locationName] = $2;
    $1.push_back(std::move($3)); $$ = std::move($1);
  }
;

statement:
  var_decl_statement {$$ = std::move($1);}
| assignment_statement {$$ = std::move($1);}
| if_else_statement {$$ = std::move($1);}
| while_statement {$$ = std::move($1);}
| skip_statement {$$ = std::move($1);}
;


var_decl_statement:
  var_definition_head SCOL
  {
    // declare var
    parsing_context.addProgramVar($1);
    declareSymbolsForProgramVar($1.get());

    $$ = std::shared_ptr<const program::VarDecl>(new program::VarDecl(@1.begin.line, std::move($1)));        
  }
;

malloc_or_null:
  MALLOC
  {
    $$ = std::shared_ptr<const program::MallocFunc>(new program::MallocFunc());
  }
| NULL
  {
    $$ = std::shared_ptr<const program::NullPtr>(new program::NullPtr());
  }
;

assignment_statement:
  location ASSIGN expr SCOL 
  {
    if($1->isConstVar())
    {
      error(@1, "Assignment to const var " + $1->toString());
    }

    if($1->containsReference()){
      error(@1, $1->toString() + " contains a reference and therefore is not a valid lvalue");      
    }
   
    if(*($1->exprType()) != *($3->exprType()) ){
      error(@1, "Invalid assignment. Type mismatch.");
    }

    $$ = std::shared_ptr<const program::Assignment>(new program::Assignment(@2.begin.line, std::move($1), std::move($3)));
  }
| location ASSIGN malloc_or_null SCOL
  {
    if($1->isConstVar())
    {
      error(@1, "Assignment to const var " + $1->toString());
    }

    if($1->containsReference()){
      error(@1, $1->toString() + " contains a reference and therefore is not a valid lvalue");      
    }

    //TODO Malloc returns a pointer, so we should also check that the lhs is not a pointer to a pointer
    if(!$1->exprType()->isPointerType()){
      error(@1, "Invalid assignment. Type mismatch.");
    }
    $$ = std::shared_ptr<const program::Assignment>(new program::Assignment(@2.begin.line, std::move($1), std::move($3) ));        
  }
| var_definition_head ASSIGN expr SCOL
  {
    // declare var
    parsing_context.addProgramVar($1);
    declareSymbolsForProgramVar($1.get());

    // construct location
    if($1->isArray())
    {
      error(@1, "Combined declaration and assignment not allowed, since " + $1->name + " is array variable");
    }

    auto variable = std::shared_ptr<const program::VariableAccess>(new VariableAccess(std::move($1)));

    if(*(variable->exprType()) != *($3->exprType()) ){
      error(@1, "Invalid assignments. Type mismatch.");
    }   
    // build assignment
    $$ = std::shared_ptr<const program::Assignment>(new program::Assignment(@2.begin.line, std::move(variable), std::move($3)));
  }
| var_definition_head ASSIGN malloc_or_null SCOL
  {
    // declare var
    parsing_context.addProgramVar($1);
    declareSymbolsForProgramVar($1.get());

    // construct location
    //TODO Malloc returns a pointer, so we should also check that the lhs is not a pointer to a pointer    
    if(!$1->isPointer())
    {
      error(@1, "Invalid assignment. Type mismatch.");
    }

    auto variable = std::shared_ptr<const program::VariableAccess>(new VariableAccess(std::move($1)));

    // build assignment
    $$ = std::shared_ptr<const program::Assignment>(new program::Assignment(@2.begin.line, std::move(variable), std::move($3)));
  }    
;

if_else_statement:
  IF LPAR formula RPAR 
  {
    parsing_context.pushProgramVars();
  }
  LCUR statement_list active_vars_dummy RCUR 
  {
    parsing_context.popProgramVars();
  }
  ELSE 
  {
    parsing_context.pushProgramVars();
  }  
  LCUR statement_list active_vars_dummy RCUR 
  {
    parsing_context.popProgramVars();

    auto leftEndLocationName = "l" + std::to_string(@1.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(@1.begin.line) + "_rEnd";
    parsing_context.locationToActiveVars[leftEndLocationName] = $8;
    parsing_context.locationToActiveVars[rightEndLocationName] = $15;
    $$ = std::shared_ptr<const program::IfElse>(new program::IfElse(@1.begin.line, std::move($3), std::move($7), std::move($14)));
  }
;

while_statement:
  WHILE formula 
  {
    parsing_context.pushProgramVars();
  }
  LCUR statement_list RCUR
  {
    parsing_context.popProgramVars();
    $$ = std::shared_ptr<const program::WhileStatement>(new program::WhileStatement(@1.begin.line, std::move($2), std::move($5)));
  }
;

skip_statement:
  SKIP SCOL {$$ = std::shared_ptr<const program::SkipStatement>(new program::SkipStatement(@1.begin.line));}
;


active_vars_dummy:
  %empty 
  {
    $$ = parsing_context.getActiveProgramVars(); 
  }
;

var_definition_head:
  type_dec PROGRAM_ID
  {
    $$ = std::shared_ptr<const program::Variable>(new program::Variable($2, false,  std::move($1), parsing_context.numberOfTraces));
  }
| CONST type_dec PROGRAM_ID
  {
    $$ = std::shared_ptr<const program::Variable>(new program::Variable($3, true, std::move($2), parsing_context.numberOfTraces));
  }
;

field:
  var_definition_head SCOL
  {
    $$ = std::move($1);        
  }
;

field_list:
  field            
  {
    auto v = std::list< std::shared_ptr<const program::Variable>>(); 
    v.push_back(std::move($1)); 
    $$ = std::move(v);
  }
| field_list field  {$1.push_back(std::move($2)); $$ = std::move($1);}
;


type_dec:
  STRUCT_NAME
  {
    if(!parsing_context.validTypeName($1)){
      error(@1, "Not a valid type identifier");
    }
    $$ = parsing_context.getExprType($1);
  }
| TYPE
  {
    if(!parsing_context.validTypeName($1)){
      error(@1, "Not a valid type identifier");
    }
    $$ = parsing_context.getExprType($1);
  }
| TYPE LBRA RBRA
  {
    if($1 != "Int"){
      error(@1, "Only integer arrays are currently supported");
    }
    $$ = std::shared_ptr<const program::ExprType>(new program::ExprType(program::BasicType::ARRAY));
  }
| type_dec MUL {
    $$ = std::shared_ptr<const program::ExprType>(new program::ExprType(std::move($1)));
  }
;

struct_dec:
  STRUCT STRUCT_NAME LCUR
  {
    parsing_context.addTypeName($2);
  }
  field_list RCUR SCOL
  {
    auto structType = std::shared_ptr<const program::ExprType>(new program::StructType($2, std::move($5))); 
    parsing_context.addStructType($2, structType);
    declareSymbolsForStructType(structType);
    $$ = structType;    
  }
;

formula:
  LPAR formula RPAR        { $$ = std::move($2); }
| TRUE                     { $$ = std::shared_ptr<const program::BooleanConstant>(new program::BooleanConstant(true)); }
| FALSE                    { $$ = std::shared_ptr<const program::BooleanConstant>(new program::BooleanConstant(false)); }
| expr GT expr             
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }    
    $$ = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GT, std::move($1), std::move($3)));
  }
| expr GE expr             
  {     
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    } 
    $$ = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GE, std::move($1), std::move($3)));
  }
| expr LT expr             
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    } 
    $$ = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LT, std::move($1), std::move($3)));
  }
| expr LE expr             
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    } 
    $$ = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LE, std::move($1), std::move($3)));
  }
| expr EQ expr             
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    $$ = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move($1), std::move($3)));
  }
| expr NEQ expr            
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    auto formula = std::shared_ptr<const program::ArithmeticComparison>
         (new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move($1), std::move($3)));
    $$ = std::shared_ptr<const program::BooleanNot>(new program::BooleanNot(std::move(formula)));
  }
| formula AND formula      
  {
    $$ = std::shared_ptr<const program::BooleanAnd>(new program::BooleanAnd(std::move($1), std::move($3)));
  }
| formula OR formula       
  { 
    $$ = std::shared_ptr<const program::BooleanOr>(new program::BooleanOr(std::move($1), std::move($3)));
  }
| NOT formula              
  { 
    $$ = std::shared_ptr<const program::BooleanNot>(new program::BooleanNot(std::move($2)));
  }
;


expr:
  LPAR expr RPAR           { $$ = std::move($2); }
| location                 { $$ = std::move(std::static_pointer_cast<const program::Expression>($1)); }
| INTEGER                  { $$ = std::shared_ptr<const program::ArithmeticConstant>(new program::ArithmeticConstant(std::move($1)));}
| expr MUL expr    
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    $$ = std::shared_ptr<const program::Multiplication>(new program::Multiplication(std::move($1),std::move($3)));
  }
| expr PLUS expr   
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    $$ = std::shared_ptr<const program::Addition>(new program::Addition(std::move($1),std::move($3)));
  }
| expr MINUS expr  
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }      
    $$ = std::shared_ptr<const program::Subtraction>(new program::Subtraction(std::move($1),std::move($3)));
  }
| expr MOD expr    
  { 
    if(!$1->isArithmeticExpr()){
      error(@1, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot carry out arithmetic operation on non-arithmetic expression");
    }
    $$ = std::shared_ptr<const program::Modulo>(new program::Modulo(std::move($1),std::move($3)));
  }
;


location:
  PROGRAM_ID                
  { 
  	auto var = parsing_context.getProgramVar($1);
    if(var->isArray())
    {
      error(@1, "Array variable " + var->name + " needs index for access");
    }
    $$ = std::shared_ptr<const program::VariableAccess>(new VariableAccess(std::move(var)));      
  }
| location ARROW PROGRAM_ID
  {
    if(!$1->isPointerExpr()){
      error(@1, $1->toString() + " is not of pointer type. Did you mean to use . ?");
    }
    if($1->exprType()->getChild()->type() != program::BasicType::STRUCT)
    {
      error(@1, $1->toString() + " is not a pointer to a struct. Cannot access members with ->");        
    }
    auto type = $1->exprType()->getChild();
    auto asStructType = std::static_pointer_cast<const program::StructType>(type);
    auto field = asStructType->getField($3);
    if(!field){
      error(@1, "Struct " + asStructType->toString() + " contains no field named " + $3);      
    }  
    $$ = std::shared_ptr<const program::StructFieldAccess>(new StructFieldAccess(std::move(field), std::move($1)));      
  }
| location DOT PROGRAM_ID
  {
    if($1->isPointerExpr()){
      error(@1, "Is of pointer type. Did you mean to use -> ?" + $1->toString());
    }
    if($1->exprType()->type() != program::BasicType::STRUCT)
    {
      error(@1, $1->toString() + " is not of type struct. Cannot access members with .");        
    }
    auto type = $1->exprType();
    auto asStructType = std::static_pointer_cast<const program::StructType>(type);
    auto field = asStructType->getField($3);
    if(!field){
      error(@1, "Struct " + asStructType->toString() + " contains no field named " + $3);      
    }  
    $$ = std::shared_ptr<const program::StructFieldAccess>(new StructFieldAccess(std::move(field), std::move($1)));      
  }
| PROGRAM_ID LBRA expr RBRA 
  {
	  auto var = parsing_context.getProgramVar($1);
    if(!var->isArray())
    {
      error(@1, "Variable " + var->name + " is not an array");
    }
    if(!$3->isArithmeticExpr()){
      error(@3, "Cannot use a non-arithmetic expression as an array reference " + $3->toString());      
    }
	  $$ = std::shared_ptr<const program::IntArrayApplication>(new IntArrayApplication(std::move(var), std::move($3)));
  }
| REFERENCE PROGRAM_ID
  {
    auto var = parsing_context.getProgramVar($2);
    if(var->isArray())
    {
      error(@1, "Cannot currently reference an array variable " + var->name);
    }  
    if(var->isConstant){
      error(@2, "Cannot take the reference of constant variable " +  var->name);      
    }
    $$ = std::shared_ptr<const program::VarReference>(new VarReference(std::move(var)));    
  }  
| MUL location
  {
    if(!$2->isPointerExpr()){
      error(@2, "cannot derefence non-pointer expression " + $2->toString());
    }
    $$ = std::shared_ptr<const program::DerefExpression>(new DerefExpression(std::move($2)));
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

