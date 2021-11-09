// A Bison parser, made by GNU Bison 3.5.1.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015, 2018-2020 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.

// Undocumented macros, especially those whose name start with YY_,
// are private implementation details.  Do not rely on them.





#include "WhileParser.hpp"


// Unqualified %code blocks.
#line 50 "WhileParser.yy"

#include "WhileParsingContext.hpp"

using namespace program;

// Tell Flex the lexer's prototype ...
# define YY_DECL parser::WhileParser::symbol_type yylex(parser::WhileParsingContext &context)
// ... and declare it for the parser's sake.
YY_DECL;


#line 57 "../src/parser/WhileParser.cpp"


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

// Whether we are compiled with exception support.
#ifndef YY_EXCEPTIONS
# if defined __GNUC__ && !defined __EXCEPTIONS
#  define YY_EXCEPTIONS 0
# else
#  define YY_EXCEPTIONS 1
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (false)
# endif


// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << '\n';                       \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yystack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YYUSE (Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void> (0)
# define YY_STACK_PRINT()                static_cast<void> (0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 4 "WhileParser.yy"
namespace parser {
#line 149 "../src/parser/WhileParser.cpp"


  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  WhileParser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr;
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              else
                goto append;

            append:
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
  WhileParser::WhileParser (parser::WhileParsingContext &context_yyarg)
#if YYDEBUG
    : yydebug_ (false),
      yycdebug_ (&std::cerr),
#else
    :
#endif
      context (context_yyarg)
  {}

  WhileParser::~WhileParser ()
  {}

  WhileParser::syntax_error::~syntax_error () YY_NOEXCEPT YY_NOTHROW
  {}

  /*---------------.
  | Symbol types.  |
  `---------------*/



  // by_state.
  WhileParser::by_state::by_state () YY_NOEXCEPT
    : state (empty_state)
  {}

  WhileParser::by_state::by_state (const by_state& that) YY_NOEXCEPT
    : state (that.state)
  {}

  void
  WhileParser::by_state::clear () YY_NOEXCEPT
  {
    state = empty_state;
  }

  void
  WhileParser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  WhileParser::by_state::by_state (state_type s) YY_NOEXCEPT
    : state (s)
  {}

  WhileParser::symbol_number_type
  WhileParser::by_state::type_get () const YY_NOEXCEPT
  {
    if (state == empty_state)
      return empty_symbol;
    else
      return yystos_[+state];
  }

  WhileParser::stack_symbol_type::stack_symbol_type ()
  {}

  WhileParser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.location))
  {
    switch (that.type_get ())
    {
      case 56: // smtlib_formula
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::Formula>  > (YY_MOVE (that.value));
        break;

      case 54: // smtlib_problemitem
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (that.value));
        break;

      case 60: // smtlib_quantvar
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (that.value));
        break;

      case 62: // smtlib_term
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::Term>  > (YY_MOVE (that.value));
        break;

      case 78: // formula
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::BoolExpression>  > (YY_MOVE (that.value));
        break;

      case 64: // function
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::Function>  > (YY_MOVE (that.value));
        break;

      case 69: // if_else_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::IfElse>  > (YY_MOVE (that.value));
        break;

      case 68: // assignment_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::IntAssignment>  > (YY_MOVE (that.value));
        break;

      case 79: // expr
      case 80: // location
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::IntExpression>  > (YY_MOVE (that.value));
        break;

      case 52: // program
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::Program>  > (YY_MOVE (that.value));
        break;

      case 75: // skip_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::SkipStatement>  > (YY_MOVE (that.value));
        break;

      case 67: // statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::Statement>  > (YY_MOVE (that.value));
        break;

      case 77: // var_definition_head
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::Variable>  > (YY_MOVE (that.value));
        break;

      case 73: // while_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const program::WhileStatement>  > (YY_MOVE (that.value));
        break;

      case 63: // function_list
        value.YY_MOVE_OR_COPY<  std::vector< std::shared_ptr<const program::Function>>  > (YY_MOVE (that.value));
        break;

      case 55: // smtlib_formula_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::Formula>>  > (YY_MOVE (that.value));
        break;

      case 53: // smtlib_problemitem_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (that.value));
        break;

      case 59: // smtlib_quantvar_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (that.value));
        break;

      case 61: // smtlib_term_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (that.value));
        break;

      case 66: // statement_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const program::Statement>>  > (YY_MOVE (that.value));
        break;

      case 76: // active_vars_dummy
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const program::Variable>>  > (YY_MOVE (that.value));
        break;

      case 45: // "number"
        value.YY_MOVE_OR_COPY< int > (YY_MOVE (that.value));
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.YY_MOVE_OR_COPY< std::string > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  WhileParser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.location))
  {
    switch (that.type_get ())
    {
      case 56: // smtlib_formula
        value.move<  std::shared_ptr<const logic::Formula>  > (YY_MOVE (that.value));
        break;

      case 54: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (that.value));
        break;

      case 60: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (that.value));
        break;

      case 62: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (YY_MOVE (that.value));
        break;

      case 78: // formula
        value.move<  std::shared_ptr<const program::BoolExpression>  > (YY_MOVE (that.value));
        break;

      case 64: // function
        value.move<  std::shared_ptr<const program::Function>  > (YY_MOVE (that.value));
        break;

      case 69: // if_else_statement
        value.move<  std::shared_ptr<const program::IfElse>  > (YY_MOVE (that.value));
        break;

      case 68: // assignment_statement
        value.move<  std::shared_ptr<const program::IntAssignment>  > (YY_MOVE (that.value));
        break;

      case 79: // expr
      case 80: // location
        value.move<  std::shared_ptr<const program::IntExpression>  > (YY_MOVE (that.value));
        break;

      case 52: // program
        value.move<  std::shared_ptr<const program::Program>  > (YY_MOVE (that.value));
        break;

      case 75: // skip_statement
        value.move<  std::shared_ptr<const program::SkipStatement>  > (YY_MOVE (that.value));
        break;

      case 67: // statement
        value.move<  std::shared_ptr<const program::Statement>  > (YY_MOVE (that.value));
        break;

      case 77: // var_definition_head
        value.move<  std::shared_ptr<const program::Variable>  > (YY_MOVE (that.value));
        break;

      case 73: // while_statement
        value.move<  std::shared_ptr<const program::WhileStatement>  > (YY_MOVE (that.value));
        break;

      case 63: // function_list
        value.move<  std::vector< std::shared_ptr<const program::Function>>  > (YY_MOVE (that.value));
        break;

      case 55: // smtlib_formula_list
        value.move<  std::vector<std::shared_ptr<const logic::Formula>>  > (YY_MOVE (that.value));
        break;

      case 53: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (that.value));
        break;

      case 59: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (that.value));
        break;

      case 61: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (that.value));
        break;

      case 66: // statement_list
        value.move<  std::vector<std::shared_ptr<const program::Statement>>  > (YY_MOVE (that.value));
        break;

      case 76: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<const program::Variable>>  > (YY_MOVE (that.value));
        break;

      case 45: // "number"
        value.move< int > (YY_MOVE (that.value));
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.move< std::string > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

    // that is emptied.
    that.type = empty_symbol;
  }

#if YY_CPLUSPLUS < 201103L
  WhileParser::stack_symbol_type&
  WhileParser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    switch (that.type_get ())
    {
      case 56: // smtlib_formula
        value.copy<  std::shared_ptr<const logic::Formula>  > (that.value);
        break;

      case 54: // smtlib_problemitem
        value.copy<  std::shared_ptr<const logic::ProblemItem>  > (that.value);
        break;

      case 60: // smtlib_quantvar
        value.copy<  std::shared_ptr<const logic::Symbol>  > (that.value);
        break;

      case 62: // smtlib_term
        value.copy<  std::shared_ptr<const logic::Term>  > (that.value);
        break;

      case 78: // formula
        value.copy<  std::shared_ptr<const program::BoolExpression>  > (that.value);
        break;

      case 64: // function
        value.copy<  std::shared_ptr<const program::Function>  > (that.value);
        break;

      case 69: // if_else_statement
        value.copy<  std::shared_ptr<const program::IfElse>  > (that.value);
        break;

      case 68: // assignment_statement
        value.copy<  std::shared_ptr<const program::IntAssignment>  > (that.value);
        break;

      case 79: // expr
      case 80: // location
        value.copy<  std::shared_ptr<const program::IntExpression>  > (that.value);
        break;

      case 52: // program
        value.copy<  std::shared_ptr<const program::Program>  > (that.value);
        break;

      case 75: // skip_statement
        value.copy<  std::shared_ptr<const program::SkipStatement>  > (that.value);
        break;

      case 67: // statement
        value.copy<  std::shared_ptr<const program::Statement>  > (that.value);
        break;

      case 77: // var_definition_head
        value.copy<  std::shared_ptr<const program::Variable>  > (that.value);
        break;

      case 73: // while_statement
        value.copy<  std::shared_ptr<const program::WhileStatement>  > (that.value);
        break;

      case 63: // function_list
        value.copy<  std::vector< std::shared_ptr<const program::Function>>  > (that.value);
        break;

      case 55: // smtlib_formula_list
        value.copy<  std::vector<std::shared_ptr<const logic::Formula>>  > (that.value);
        break;

      case 53: // smtlib_problemitem_list
        value.copy<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (that.value);
        break;

      case 59: // smtlib_quantvar_list
        value.copy<  std::vector<std::shared_ptr<const logic::Symbol>>  > (that.value);
        break;

      case 61: // smtlib_term_list
        value.copy<  std::vector<std::shared_ptr<const logic::Term>>  > (that.value);
        break;

      case 66: // statement_list
        value.copy<  std::vector<std::shared_ptr<const program::Statement>>  > (that.value);
        break;

      case 76: // active_vars_dummy
        value.copy<  std::vector<std::shared_ptr<const program::Variable>>  > (that.value);
        break;

      case 45: // "number"
        value.copy< int > (that.value);
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.copy< std::string > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    return *this;
  }

  WhileParser::stack_symbol_type&
  WhileParser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    switch (that.type_get ())
    {
      case 56: // smtlib_formula
        value.move<  std::shared_ptr<const logic::Formula>  > (that.value);
        break;

      case 54: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (that.value);
        break;

      case 60: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (that.value);
        break;

      case 62: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (that.value);
        break;

      case 78: // formula
        value.move<  std::shared_ptr<const program::BoolExpression>  > (that.value);
        break;

      case 64: // function
        value.move<  std::shared_ptr<const program::Function>  > (that.value);
        break;

      case 69: // if_else_statement
        value.move<  std::shared_ptr<const program::IfElse>  > (that.value);
        break;

      case 68: // assignment_statement
        value.move<  std::shared_ptr<const program::IntAssignment>  > (that.value);
        break;

      case 79: // expr
      case 80: // location
        value.move<  std::shared_ptr<const program::IntExpression>  > (that.value);
        break;

      case 52: // program
        value.move<  std::shared_ptr<const program::Program>  > (that.value);
        break;

      case 75: // skip_statement
        value.move<  std::shared_ptr<const program::SkipStatement>  > (that.value);
        break;

      case 67: // statement
        value.move<  std::shared_ptr<const program::Statement>  > (that.value);
        break;

      case 77: // var_definition_head
        value.move<  std::shared_ptr<const program::Variable>  > (that.value);
        break;

      case 73: // while_statement
        value.move<  std::shared_ptr<const program::WhileStatement>  > (that.value);
        break;

      case 63: // function_list
        value.move<  std::vector< std::shared_ptr<const program::Function>>  > (that.value);
        break;

      case 55: // smtlib_formula_list
        value.move<  std::vector<std::shared_ptr<const logic::Formula>>  > (that.value);
        break;

      case 53: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (that.value);
        break;

      case 59: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (that.value);
        break;

      case 61: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (that.value);
        break;

      case 66: // statement_list
        value.move<  std::vector<std::shared_ptr<const program::Statement>>  > (that.value);
        break;

      case 76: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<const program::Variable>>  > (that.value);
        break;

      case 45: // "number"
        value.move< int > (that.value);
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.move< std::string > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    // that is emptied.
    that.state = empty_state;
    return *this;
  }
#endif

  template <typename Base>
  void
  WhileParser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);
  }

#if YYDEBUG
  template <typename Base>
  void
  WhileParser::yy_print_ (std::ostream& yyo,
                                     const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YYUSE (yyoutput);
    symbol_number_type yytype = yysym.type_get ();
#if defined __GNUC__ && ! defined __clang__ && ! defined __ICC && __GNUC__ * 100 + __GNUC_MINOR__ <= 408
    // Avoid a (spurious) G++ 4.8 warning about "array subscript is
    // below array bounds".
    if (yysym.empty ())
      std::abort ();
#endif
    yyo << (yytype < yyntokens_ ? "token" : "nterm")
        << ' ' << yytname_[yytype] << " ("
        << yysym.location << ": ";
    switch (yytype)
    {
      case 42: // "program identifier"
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as < std::string > (); }
#line 725 "../src/parser/WhileParser.cpp"
        break;

      case 43: // "smtlib identifier"
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as < std::string > (); }
#line 731 "../src/parser/WhileParser.cpp"
        break;

      case 44: // "type identifier"
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as < std::string > (); }
#line 737 "../src/parser/WhileParser.cpp"
        break;

      case 45: // "number"
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as < int > (); }
#line 743 "../src/parser/WhileParser.cpp"
        break;

      case 52: // program
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::Program>  > (); }
#line 749 "../src/parser/WhileParser.cpp"
        break;

      case 53: // smtlib_problemitem_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (); }
#line 755 "../src/parser/WhileParser.cpp"
        break;

      case 54: // smtlib_problemitem
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::ProblemItem>  > (); }
#line 761 "../src/parser/WhileParser.cpp"
        break;

      case 55: // smtlib_formula_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::Formula>>  > (); }
#line 767 "../src/parser/WhileParser.cpp"
        break;

      case 56: // smtlib_formula
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::Formula>  > (); }
#line 773 "../src/parser/WhileParser.cpp"
        break;

      case 59: // smtlib_quantvar_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::Symbol>>  > (); }
#line 779 "../src/parser/WhileParser.cpp"
        break;

      case 60: // smtlib_quantvar
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::Symbol>  > (); }
#line 785 "../src/parser/WhileParser.cpp"
        break;

      case 61: // smtlib_term_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::Term>>  > (); }
#line 791 "../src/parser/WhileParser.cpp"
        break;

      case 62: // smtlib_term
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::Term>  > (); }
#line 797 "../src/parser/WhileParser.cpp"
        break;

      case 63: // function_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector< std::shared_ptr<const program::Function>>  > (); }
#line 803 "../src/parser/WhileParser.cpp"
        break;

      case 64: // function
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::Function>  > (); }
#line 809 "../src/parser/WhileParser.cpp"
        break;

      case 66: // statement_list
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const program::Statement>>  > (); }
#line 815 "../src/parser/WhileParser.cpp"
        break;

      case 67: // statement
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::Statement>  > (); }
#line 821 "../src/parser/WhileParser.cpp"
        break;

      case 68: // assignment_statement
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::IntAssignment>  > (); }
#line 827 "../src/parser/WhileParser.cpp"
        break;

      case 69: // if_else_statement
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::IfElse>  > (); }
#line 833 "../src/parser/WhileParser.cpp"
        break;

      case 73: // while_statement
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::WhileStatement>  > (); }
#line 839 "../src/parser/WhileParser.cpp"
        break;

      case 75: // skip_statement
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::SkipStatement>  > (); }
#line 845 "../src/parser/WhileParser.cpp"
        break;

      case 76: // active_vars_dummy
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const program::Variable>>  > (); }
#line 851 "../src/parser/WhileParser.cpp"
        break;

      case 77: // var_definition_head
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::Variable>  > (); }
#line 857 "../src/parser/WhileParser.cpp"
        break;

      case 78: // formula
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::BoolExpression>  > (); }
#line 863 "../src/parser/WhileParser.cpp"
        break;

      case 79: // expr
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::IntExpression>  > (); }
#line 869 "../src/parser/WhileParser.cpp"
        break;

      case 80: // location
#line 138 "WhileParser.yy"
                 { yyoutput << yysym.value.template as <  std::shared_ptr<const program::IntExpression>  > (); }
#line 875 "../src/parser/WhileParser.cpp"
        break;

      default:
        break;
    }
    yyo << ')';
  }
#endif

  void
  WhileParser::yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym)
  {
    if (m)
      YY_SYMBOL_PRINT (m, sym);
    yystack_.push (YY_MOVE (sym));
  }

  void
  WhileParser::yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym)
  {
#if 201103L <= YY_CPLUSPLUS
    yypush_ (m, stack_symbol_type (s, std::move (sym)));
#else
    stack_symbol_type ss (s, sym);
    yypush_ (m, ss);
#endif
  }

  void
  WhileParser::yypop_ (int n)
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  WhileParser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  WhileParser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  WhileParser::debug_level_type
  WhileParser::debug_level () const
  {
    return yydebug_;
  }

  void
  WhileParser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  WhileParser::state_type
  WhileParser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - yyntokens_] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - yyntokens_];
  }

  bool
  WhileParser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  bool
  WhileParser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  WhileParser::operator() ()
  {
    return parse ();
  }

  int
  WhileParser::parse ()
  {
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

#if YY_EXCEPTIONS
    try
#endif // YY_EXCEPTIONS
      {
    YYCDEBUG << "Starting parse\n";


    // User initialization code.
#line 43 "WhileParser.yy"
{
  // Initialize the initial location.
  yyla.location.begin.filename = yyla.location.end.filename = &context.inputFile;
}

#line 999 "../src/parser/WhileParser.cpp"


    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, YY_MOVE (yyla));

  /*-----------------------------------------------.
  | yynewstate -- push a new symbol on the stack.  |
  `-----------------------------------------------*/
  yynewstate:
    YYCDEBUG << "Entering state " << int (yystack_[0].state) << '\n';

    // Accept?
    if (yystack_[0].state == yyfinal_)
      YYACCEPT;

    goto yybackup;


  /*-----------.
  | yybackup.  |
  `-----------*/
  yybackup:
    // Try to take a decision without lookahead.
    yyn = yypact_[+yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token: ";
#if YY_EXCEPTIONS
        try
#endif // YY_EXCEPTIONS
          {
            symbol_type yylookahead (yylex (context));
            yyla.move (yylookahead);
          }
#if YY_EXCEPTIONS
        catch (const syntax_error& yyexc)
          {
            YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
            error (yyexc);
            goto yyerrlab1;
          }
#endif // YY_EXCEPTIONS
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.type_get ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.type_get ())
      {
        goto yydefault;
      }

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", state_type (yyn), YY_MOVE (yyla));
    goto yynewstate;


  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[+yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;


  /*-----------------------------.
  | yyreduce -- do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_ (yystack_[yylen].state, yyr1_[yyn]);
      /* Variants are always initialized to an empty instance of the
         correct type. The default '$$ = $1' action is NOT applied
         when using variants.  */
      switch (yyr1_[yyn])
    {
      case 56: // smtlib_formula
        yylhs.value.emplace<  std::shared_ptr<const logic::Formula>  > ();
        break;

      case 54: // smtlib_problemitem
        yylhs.value.emplace<  std::shared_ptr<const logic::ProblemItem>  > ();
        break;

      case 60: // smtlib_quantvar
        yylhs.value.emplace<  std::shared_ptr<const logic::Symbol>  > ();
        break;

      case 62: // smtlib_term
        yylhs.value.emplace<  std::shared_ptr<const logic::Term>  > ();
        break;

      case 78: // formula
        yylhs.value.emplace<  std::shared_ptr<const program::BoolExpression>  > ();
        break;

      case 64: // function
        yylhs.value.emplace<  std::shared_ptr<const program::Function>  > ();
        break;

      case 69: // if_else_statement
        yylhs.value.emplace<  std::shared_ptr<const program::IfElse>  > ();
        break;

      case 68: // assignment_statement
        yylhs.value.emplace<  std::shared_ptr<const program::IntAssignment>  > ();
        break;

      case 79: // expr
      case 80: // location
        yylhs.value.emplace<  std::shared_ptr<const program::IntExpression>  > ();
        break;

      case 52: // program
        yylhs.value.emplace<  std::shared_ptr<const program::Program>  > ();
        break;

      case 75: // skip_statement
        yylhs.value.emplace<  std::shared_ptr<const program::SkipStatement>  > ();
        break;

      case 67: // statement
        yylhs.value.emplace<  std::shared_ptr<const program::Statement>  > ();
        break;

      case 77: // var_definition_head
        yylhs.value.emplace<  std::shared_ptr<const program::Variable>  > ();
        break;

      case 73: // while_statement
        yylhs.value.emplace<  std::shared_ptr<const program::WhileStatement>  > ();
        break;

      case 63: // function_list
        yylhs.value.emplace<  std::vector< std::shared_ptr<const program::Function>>  > ();
        break;

      case 55: // smtlib_formula_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::Formula>>  > ();
        break;

      case 53: // smtlib_problemitem_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
        break;

      case 59: // smtlib_quantvar_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::Symbol>>  > ();
        break;

      case 61: // smtlib_term_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::Term>>  > ();
        break;

      case 66: // statement_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const program::Statement>>  > ();
        break;

      case 76: // active_vars_dummy
        yylhs.value.emplace<  std::vector<std::shared_ptr<const program::Variable>>  > ();
        break;

      case 45: // "number"
        yylhs.value.emplace< int > ();
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        yylhs.value.emplace< std::string > ();
        break;

      default:
        break;
    }


      // Default location.
      {
        stack_type::slice range (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, range, yylen);
        yyerror_range[1].location = yylhs.location;
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
#if YY_EXCEPTIONS
      try
#endif // YY_EXCEPTIONS
        {
          switch (yyn)
            {
  case 2:
#line 154 "WhileParser.yy"
  {
    logic::Theory::declareTheories();
  }
#line 1223 "../src/parser/WhileParser.cpp"
    break;

  case 3:
#line 158 "WhileParser.yy"
  {
    context.problemItems = yystack_[0].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
  }
#line 1231 "../src/parser/WhileParser.cpp"
    break;

  case 4:
#line 163 "WhileParser.yy"
  {
    if (yystack_[1].value.as < int > () < 1)
    {
      error(yystack_[1].location, "number of traces has to be greater than or equal to 1");
    }

    context.numberOfTraces = (unsigned) yystack_[1].value.as < int > ();
    logic::Theory::declareTheories();
    declareSymbolsForTraces(context.numberOfTraces);
  }
#line 1246 "../src/parser/WhileParser.cpp"
    break;

  case 5:
#line 174 "WhileParser.yy"
  {
        context.problemItems = yystack_[0].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
  }
#line 1254 "../src/parser/WhileParser.cpp"
    break;

  case 6:
#line 181 "WhileParser.yy"
  { 
    context.program = std::unique_ptr<const program::Program>(new program::Program(yystack_[0].value.as <  std::vector< std::shared_ptr<const program::Function>>  > ())); 
  }
#line 1262 "../src/parser/WhileParser.cpp"
    break;

  case 7:
#line 187 "WhileParser.yy"
         {yylhs.value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > () = std::vector<std::shared_ptr<const logic::ProblemItem>>();}
#line 1268 "../src/parser/WhileParser.cpp"
    break;

  case 8:
#line 188 "WhileParser.yy"
                                             {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::ProblemItem>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ());}
#line 1274 "../src/parser/WhileParser.cpp"
    break;

  case 9:
#line 193 "WhileParser.yy"
  {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Axiom>(new logic::Axiom(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > (), "user-axiom-" + std::to_string(context.numberOfAxioms)));
    context.numberOfAxioms++;
  }
#line 1283 "../src/parser/WhileParser.cpp"
    break;

  case 10:
#line 199 "WhileParser.yy"
  {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Lemma>(new logic::Lemma(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > (), "user-lemma-" + std::to_string(context.numberOfLemmas)));
    context.numberOfLemmas++;
  }
#line 1292 "../src/parser/WhileParser.cpp"
    break;

  case 11:
#line 205 "WhileParser.yy"
  {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Conjecture>(new logic::Conjecture(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > (), "user-conjecture-" + std::to_string(context.numberOfConjectures)));
    context.numberOfConjectures++;
  }
#line 1301 "../src/parser/WhileParser.cpp"
    break;

  case 12:
#line 211 "WhileParser.yy"
         {yylhs.value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > () = std::vector<std::shared_ptr<const logic::Formula>>();}
#line 1307 "../src/parser/WhileParser.cpp"
    break;

  case 13:
#line 212 "WhileParser.yy"
                                     {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Formula>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > ());}
#line 1313 "../src/parser/WhileParser.cpp"
    break;

  case 14:
#line 216 "WhileParser.yy"
                                             { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::boolTrue();}
#line 1319 "../src/parser/WhileParser.cpp"
    break;

  case 15:
#line 217 "WhileParser.yy"
                                             { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::boolFalse();}
#line 1325 "../src/parser/WhileParser.cpp"
    break;

  case 16:
#line 219 "WhileParser.yy"
  { 
    auto leftSort = yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort;
    auto rightSort = yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort;
    
    if(leftSort != rightSort)
    {
      error(yystack_[1].location, "Argument types " + leftSort->name + " and " + rightSort->name + " don't match!");
    }
    yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::equality(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
  }
#line 1340 "../src/parser/WhileParser.cpp"
    break;

  case 17:
#line 230 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::intGreater(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1356 "../src/parser/WhileParser.cpp"
    break;

  case 18:
#line 242 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::intGreaterEqual(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1372 "../src/parser/WhileParser.cpp"
    break;

  case 19:
#line 254 "WhileParser.yy"
{ 
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::intLess(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1388 "../src/parser/WhileParser.cpp"
    break;

  case 20:
#line 266 "WhileParser.yy"
{ 
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Theory::intLessEqual(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1404 "../src/parser/WhileParser.cpp"
    break;

  case 21:
#line 277 "WhileParser.yy"
                                             { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::conjunction(std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > ()));}
#line 1410 "../src/parser/WhileParser.cpp"
    break;

  case 22:
#line 278 "WhileParser.yy"
                                             { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::disjunction(std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Formula>>  > ()));}
#line 1416 "../src/parser/WhileParser.cpp"
    break;

  case 23:
#line 279 "WhileParser.yy"
                                             { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::negation(std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > ()));}
#line 1422 "../src/parser/WhileParser.cpp"
    break;

  case 24:
#line 280 "WhileParser.yy"
                                                     { yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::implication(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Formula>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > ()));}
#line 1428 "../src/parser/WhileParser.cpp"
    break;

  case 25:
#line 282 "WhileParser.yy"
  {
    // TODO: propagate existing-var-error to parser and raise error
    context.pushQuantifiedVars(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());
  }
#line 1437 "../src/parser/WhileParser.cpp"
    break;

  case 26:
#line 287 "WhileParser.yy"
  { 
    context.popQuantifiedVars();
    yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::universal(std::move(yystack_[4].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > ()));
  }
#line 1446 "../src/parser/WhileParser.cpp"
    break;

  case 27:
#line 292 "WhileParser.yy"
  {
    // TODO: propagate existing-var-error to parser and raise error
    context.pushQuantifiedVars(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());
  }
#line 1455 "../src/parser/WhileParser.cpp"
    break;

  case 28:
#line 297 "WhileParser.yy"
  { 
    context.popQuantifiedVars();
    yylhs.value.as <  std::shared_ptr<const logic::Formula>  > () = logic::Formulas::existential(std::move(yystack_[4].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Formula>  > ()));
  }
#line 1464 "../src/parser/WhileParser.cpp"
    break;

  case 29:
#line 304 "WhileParser.yy"
                  {auto vec = std::vector<std::shared_ptr<const logic::Symbol>>(); vec.push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Symbol>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > () = std::move(vec);}
#line 1470 "../src/parser/WhileParser.cpp"
    break;

  case 30:
#line 305 "WhileParser.yy"
                                       {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Symbol>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());}
#line 1476 "../src/parser/WhileParser.cpp"
    break;

  case 31:
#line 310 "WhileParser.yy"
  { 
    if(context.isDeclared(yystack_[2].value.as < std::string > ()))
    {
      error(yystack_[2].location, yystack_[2].value.as < std::string > () + " has already been declared");
    }
    if(yystack_[1].value.as < std::string > () == "Int")
    { 
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::intSort());
    }
    else if(yystack_[1].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::boolSort());
    }
    else if(yystack_[1].value.as < std::string > () == "Nat")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::natSort());
    }
    else if(yystack_[1].value.as < std::string > () == "Time")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::timeSort());
    }
    else
    {
      if(yystack_[1].value.as < std::string > () != "Trace")
      {
        error(yystack_[1].location, "Only the sorts Int, Bool, Time and Trace are supported");
      }
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::traceSort());
    }
  }
#line 1511 "../src/parser/WhileParser.cpp"
    break;

  case 32:
#line 343 "WhileParser.yy"
              {yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > () = std::vector<std::shared_ptr<const logic::Term>>(); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().push_back(yystack_[0].value.as <  std::shared_ptr<const logic::Term>  > ());}
#line 1517 "../src/parser/WhileParser.cpp"
    break;

  case 33:
#line 344 "WhileParser.yy"
                               {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Term>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ());}
#line 1523 "../src/parser/WhileParser.cpp"
    break;

  case 34:
#line 349 "WhileParser.yy"
{
  if(!context.isDeclared(yystack_[0].value.as < std::string > ()))
  {
    error(yystack_[0].location, yystack_[0].value.as < std::string > () + " has not been declared");
  }
  auto symbol = context.fetch(yystack_[0].value.as < std::string > ()); 

  if(symbol->argSorts.size() > 0)
  {
      error(yystack_[0].location, "Not enough arguments for term " + symbol->name);
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Terms::func(symbol, std::vector<std::shared_ptr<const logic::Term>>());
}
#line 1541 "../src/parser/WhileParser.cpp"
    break;

  case 35:
#line 363 "WhileParser.yy"
  {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intConstant(yystack_[0].value.as < int > ());
  }
#line 1549 "../src/parser/WhileParser.cpp"
    break;

  case 36:
#line 367 "WhileParser.yy"
{
  if(!context.isDeclared(yystack_[2].value.as < std::string > ()))
  {
    error(yystack_[2].location, yystack_[2].value.as < std::string > () + " has not been declared");
  }
  auto symbol = context.fetch(yystack_[2].value.as < std::string > ()); 

  if(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().size() < symbol->argSorts.size())
  {
      error(yystack_[1].location, "Not enough arguments for term " + symbol->name);
  }
  if(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().size() > symbol->argSorts.size())
  {
      error(yystack_[1].location, "Too many arguments for term " + symbol->name);
  }
  for (int i=0; i < symbol->argSorts.size(); ++i)
  {
      if(symbol->argSorts[i] != yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()[i]->symbol->rngSort)
      {
        error(yystack_[1].location, "Argument has type " + yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()[i]->symbol->rngSort->name + " instead of " + symbol->argSorts[i]->name);
      }
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Terms::func(symbol, std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()));
}
#line 1578 "../src/parser/WhileParser.cpp"
    break;

  case 37:
#line 392 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intAddition(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1594 "../src/parser/WhileParser.cpp"
    break;

  case 38:
#line 404 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intSubtraction(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1610 "../src/parser/WhileParser.cpp"
    break;

  case 39:
#line 416 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intModulo(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1626 "../src/parser/WhileParser.cpp"
    break;

  case 40:
#line 428 "WhileParser.yy"
{
  if(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  } 
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intMultiplication(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1642 "../src/parser/WhileParser.cpp"
    break;

  case 41:
#line 442 "WhileParser.yy"
                          {auto v = std::vector< std::shared_ptr<const program::Function>>(); v.push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const program::Function>  > ())); yylhs.value.as <  std::vector< std::shared_ptr<const program::Function>>  > () = std::move(v);}
#line 1648 "../src/parser/WhileParser.cpp"
    break;

  case 42:
#line 443 "WhileParser.yy"
                          {yystack_[1].value.as <  std::vector< std::shared_ptr<const program::Function>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const program::Function>  > ())); yylhs.value.as <  std::vector< std::shared_ptr<const program::Function>>  > () = std::move(yystack_[1].value.as <  std::vector< std::shared_ptr<const program::Function>>  > ());}
#line 1654 "../src/parser/WhileParser.cpp"
    break;

  case 43:
#line 448 "WhileParser.yy"
  {
    context.pushProgramVars();
  }
#line 1662 "../src/parser/WhileParser.cpp"
    break;

  case 44:
#line 452 "WhileParser.yy"
  {
    auto functionEndLocationName = yystack_[6].value.as < std::string > () + "_end";
    context.locationToActiveVars[functionEndLocationName] = context.getActiveProgramVars();
    context.popProgramVars();

  	auto function = std::shared_ptr<const program::Function>(new program::Function(yystack_[6].value.as < std::string > (), std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ())));

    // compute enclosing loops
    context.addEnclosingLoops(*function);
    yylhs.value.as <  std::shared_ptr<const program::Function>  > () = function;

    // declare symbols for loops (needs to be done here, since it depends on enclosingLoops)
    declareSymbolsForFunction(function.get(), context.numberOfTraces);
  }
#line 1681 "../src/parser/WhileParser.cpp"
    break;

  case 45:
#line 469 "WhileParser.yy"
         {yylhs.value.as <  std::vector<std::shared_ptr<const program::Statement>>  > () = std::vector<std::shared_ptr<const program::Statement>>();}
#line 1687 "../src/parser/WhileParser.cpp"
    break;

  case 46:
#line 471 "WhileParser.yy"
  {
    auto locationName = yystack_[0].value.as <  std::shared_ptr<const program::Statement>  > ()->location;
    context.locationToActiveVars[locationName] = yystack_[1].value.as <  std::vector<std::shared_ptr<const program::Variable>>  > ();
    yystack_[2].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const program::Statement>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const program::Statement>>  > () = std::move(yystack_[2].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ());
  }
#line 1697 "../src/parser/WhileParser.cpp"
    break;

  case 47:
#line 477 "WhileParser.yy"
  {
    // dummy is not used here, but silences a shift-reduce conflict
    context.addProgramVar(yystack_[1].value.as <  std::shared_ptr<const program::Variable>  > ());
    declareSymbolForProgramVar(yystack_[1].value.as <  std::shared_ptr<const program::Variable>  > ().get());
    yylhs.value.as <  std::vector<std::shared_ptr<const program::Statement>>  > () = std::move(yystack_[3].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ());
  }
#line 1708 "../src/parser/WhileParser.cpp"
    break;

  case 48:
#line 486 "WhileParser.yy"
                       {yylhs.value.as <  std::shared_ptr<const program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntAssignment>  > ());}
#line 1714 "../src/parser/WhileParser.cpp"
    break;

  case 49:
#line 487 "WhileParser.yy"
                    {yylhs.value.as <  std::shared_ptr<const program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<const program::IfElse>  > ());}
#line 1720 "../src/parser/WhileParser.cpp"
    break;

  case 50:
#line 488 "WhileParser.yy"
                  {yylhs.value.as <  std::shared_ptr<const program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<const program::WhileStatement>  > ());}
#line 1726 "../src/parser/WhileParser.cpp"
    break;

  case 51:
#line 489 "WhileParser.yy"
                 {yylhs.value.as <  std::shared_ptr<const program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<const program::SkipStatement>  > ());}
#line 1732 "../src/parser/WhileParser.cpp"
    break;

  case 52:
#line 494 "WhileParser.yy"
  {
    if(yystack_[3].value.as <  std::shared_ptr<const program::IntExpression>  > ()->type() == IntExpression::Type::IntVariableAccess)
    {
      auto intVariableAccess = std::static_pointer_cast<const program::IntVariableAccess>(yystack_[3].value.as <  std::shared_ptr<const program::IntExpression>  > ());
      if(intVariableAccess->var->isConstant)
      {
        error(yystack_[3].location, "Assignment to const var " + intVariableAccess->var->name);
      }
    }
    else
    {
      assert(yystack_[3].value.as <  std::shared_ptr<const program::IntExpression>  > ()->type() == IntExpression::Type::IntArrayApplication);
      auto intArrayApplication = std::static_pointer_cast<const program::IntArrayApplication>(yystack_[3].value.as <  std::shared_ptr<const program::IntExpression>  > ());
      if(intArrayApplication->array->isConstant)
      {
        error(yystack_[3].location, "Assignment to const var " + intArrayApplication->array->name);
      }
    }
    yylhs.value.as <  std::shared_ptr<const program::IntAssignment>  > () = std::shared_ptr<const program::IntAssignment>(new program::IntAssignment(yystack_[2].location.begin.line, std::move(yystack_[3].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const program::IntExpression>  > ())));
  }
#line 1757 "../src/parser/WhileParser.cpp"
    break;

  case 53:
#line 515 "WhileParser.yy"
  {
    // declare var
    context.addProgramVar(yystack_[3].value.as <  std::shared_ptr<const program::Variable>  > ());
    declareSymbolForProgramVar(yystack_[3].value.as <  std::shared_ptr<const program::Variable>  > ().get());

    // construct location
    if(yystack_[3].value.as <  std::shared_ptr<const program::Variable>  > ()->isArray)
    {
      error(yystack_[3].location, "Combined declaration and assignment not allowed, since " + yystack_[3].value.as <  std::shared_ptr<const program::Variable>  > ()->name + " is array variable");
    }
    auto intVariableAccess = std::shared_ptr<const program::IntVariableAccess>(new IntVariableAccess(std::move(yystack_[3].value.as <  std::shared_ptr<const program::Variable>  > ())));
   
    // build assignment
    yylhs.value.as <  std::shared_ptr<const program::IntAssignment>  > () = std::shared_ptr<const program::IntAssignment>(new program::IntAssignment(yystack_[2].location.begin.line, std::move(intVariableAccess), std::move(yystack_[1].value.as <  std::shared_ptr<const program::IntExpression>  > ())));
  }
#line 1777 "../src/parser/WhileParser.cpp"
    break;

  case 54:
#line 534 "WhileParser.yy"
  {
    context.pushProgramVars();
  }
#line 1785 "../src/parser/WhileParser.cpp"
    break;

  case 55:
#line 538 "WhileParser.yy"
  {
    context.popProgramVars();
  }
#line 1793 "../src/parser/WhileParser.cpp"
    break;

  case 56:
#line 542 "WhileParser.yy"
  {
    context.pushProgramVars();
  }
#line 1801 "../src/parser/WhileParser.cpp"
    break;

  case 57:
#line 546 "WhileParser.yy"
  {
    context.popProgramVars();

    auto leftEndLocationName = "l" + std::to_string(yystack_[15].location.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(yystack_[15].location.begin.line) + "_rEnd";
    context.locationToActiveVars[leftEndLocationName] = yystack_[8].value.as <  std::vector<std::shared_ptr<const program::Variable>>  > ();
    context.locationToActiveVars[rightEndLocationName] = yystack_[1].value.as <  std::vector<std::shared_ptr<const program::Variable>>  > ();
    yylhs.value.as <  std::shared_ptr<const program::IfElse>  > () = std::shared_ptr<const program::IfElse>(new program::IfElse(yystack_[15].location.begin.line, std::move(yystack_[13].value.as <  std::shared_ptr<const program::BoolExpression>  > ()), std::move(yystack_[9].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ()), std::move(yystack_[2].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ())));
  }
#line 1815 "../src/parser/WhileParser.cpp"
    break;

  case 58:
#line 559 "WhileParser.yy"
  {
    context.pushProgramVars();
  }
#line 1823 "../src/parser/WhileParser.cpp"
    break;

  case 59:
#line 563 "WhileParser.yy"
  {
    context.popProgramVars();
    yylhs.value.as <  std::shared_ptr<const program::WhileStatement>  > () = std::shared_ptr<const program::WhileStatement>(new program::WhileStatement(yystack_[5].location.begin.line, std::move(yystack_[4].value.as <  std::shared_ptr<const program::BoolExpression>  > ()), std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const program::Statement>>  > ())));
  }
#line 1832 "../src/parser/WhileParser.cpp"
    break;

  case 60:
#line 570 "WhileParser.yy"
            {yylhs.value.as <  std::shared_ptr<const program::SkipStatement>  > () = std::shared_ptr<const program::SkipStatement>(new program::SkipStatement(yystack_[1].location.begin.line));}
#line 1838 "../src/parser/WhileParser.cpp"
    break;

  case 61:
#line 575 "WhileParser.yy"
  {
    yylhs.value.as <  std::vector<std::shared_ptr<const program::Variable>>  > () = context.getActiveProgramVars(); 
  }
#line 1846 "../src/parser/WhileParser.cpp"
    break;

  case 62:
#line 582 "WhileParser.yy"
  {
    if(yystack_[1].value.as < std::string > () == "Bool")
    {
      error(yystack_[1].location, "Program variables of type Bool are not supported");
    }
    if(yystack_[1].value.as < std::string > () == "Nat" || yystack_[1].value.as < std::string > () == "Time" || yystack_[1].value.as < std::string > () == "Trace")
    {
      error(yystack_[1].location, "Program variables can't have type " + yystack_[1].value.as < std::string > ());
    }
    yylhs.value.as <  std::shared_ptr<const program::Variable>  > () = std::shared_ptr<const program::Variable>(new program::Variable(yystack_[0].value.as < std::string > (), false, false, context.numberOfTraces));
  }
#line 1862 "../src/parser/WhileParser.cpp"
    break;

  case 63:
#line 594 "WhileParser.yy"
  {
    if(yystack_[1].value.as < std::string > () == "Bool")
    {
      error(yystack_[2].location, "Program variables of type Bool are not supported");
    }
    if(yystack_[1].value.as < std::string > () == "Nat" || yystack_[1].value.as < std::string > () == "Time" || yystack_[1].value.as < std::string > () == "Trace")
    {
      error(yystack_[1].location, "Program variables can't have type " + yystack_[1].value.as < std::string > ());
    }
    yylhs.value.as <  std::shared_ptr<const program::Variable>  > () = std::shared_ptr<const program::Variable>(new program::Variable(yystack_[0].value.as < std::string > (), true, false, context.numberOfTraces));
  }
#line 1878 "../src/parser/WhileParser.cpp"
    break;

  case 64:
#line 606 "WhileParser.yy"
  {
    if(yystack_[3].value.as < std::string > () == "Bool")
    {
      error(yystack_[3].location, "Program variables of type Bool are not supported");
    }
    if(yystack_[3].value.as < std::string > () == "Nat" || yystack_[3].value.as < std::string > () == "Time" || yystack_[3].value.as < std::string > () == "Trace")
    {
      error(yystack_[3].location, "Program variables can't have type " + yystack_[3].value.as < std::string > ());
    }
    yylhs.value.as <  std::shared_ptr<const program::Variable>  > () = std::shared_ptr<const program::Variable>(new program::Variable(yystack_[0].value.as < std::string > (), false, true, context.numberOfTraces));
  }
#line 1894 "../src/parser/WhileParser.cpp"
    break;

  case 65:
#line 618 "WhileParser.yy"
  {
    if(yystack_[3].value.as < std::string > () == "Bool")
    {
      error(yystack_[4].location, "Program variables of type Bool are not supported");
    }
    if(yystack_[3].value.as < std::string > () == "Nat" || yystack_[3].value.as < std::string > () == "Time" || yystack_[3].value.as < std::string > () == "Trace")
    {
      error(yystack_[3].location, "Program variables can't have type " + yystack_[3].value.as < std::string > ());
    }
    yylhs.value.as <  std::shared_ptr<const program::Variable>  > () = std::shared_ptr<const program::Variable>(new program::Variable(yystack_[0].value.as < std::string > (), true, true, context.numberOfTraces));
  }
#line 1910 "../src/parser/WhileParser.cpp"
    break;

  case 66:
#line 632 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::move(yystack_[1].value.as <  std::shared_ptr<const program::BoolExpression>  > ()); }
#line 1916 "../src/parser/WhileParser.cpp"
    break;

  case 67:
#line 633 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanConstant>(new program::BooleanConstant(true)); }
#line 1922 "../src/parser/WhileParser.cpp"
    break;

  case 68:
#line 634 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanConstant>(new program::BooleanConstant(false)); }
#line 1928 "../src/parser/WhileParser.cpp"
    break;

  case 69:
#line 635 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GT, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 1934 "../src/parser/WhileParser.cpp"
    break;

  case 70:
#line 636 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GE, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 1940 "../src/parser/WhileParser.cpp"
    break;

  case 71:
#line 637 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LT, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 1946 "../src/parser/WhileParser.cpp"
    break;

  case 72:
#line 638 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LE, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 1952 "../src/parser/WhileParser.cpp"
    break;

  case 73:
#line 639 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 1958 "../src/parser/WhileParser.cpp"
    break;

  case 74:
#line 640 "WhileParser.yy"
                           { auto formula = std::shared_ptr<const program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));
                             yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanNot>(new program::BooleanNot(std::move(formula)));}
#line 1965 "../src/parser/WhileParser.cpp"
    break;

  case 75:
#line 642 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanAnd>(new program::BooleanAnd(std::move(yystack_[2].value.as <  std::shared_ptr<const program::BoolExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::BoolExpression>  > ())));}
#line 1971 "../src/parser/WhileParser.cpp"
    break;

  case 76:
#line 643 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanOr>(new program::BooleanOr(std::move(yystack_[2].value.as <  std::shared_ptr<const program::BoolExpression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<const program::BoolExpression>  > ())));}
#line 1977 "../src/parser/WhileParser.cpp"
    break;

  case 77:
#line 644 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::BoolExpression>  > () = std::shared_ptr<const program::BooleanNot>(new program::BooleanNot(std::move(yystack_[0].value.as <  std::shared_ptr<const program::BoolExpression>  > ())));}
#line 1983 "../src/parser/WhileParser.cpp"
    break;

  case 78:
#line 648 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::move(yystack_[1].value.as <  std::shared_ptr<const program::IntExpression>  > ()); }
#line 1989 "../src/parser/WhileParser.cpp"
    break;

  case 79:
#line 649 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ()); }
#line 1995 "../src/parser/WhileParser.cpp"
    break;

  case 80:
#line 650 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::ArithmeticConstant>(new program::ArithmeticConstant(std::move(yystack_[0].value.as < int > ())));}
#line 2001 "../src/parser/WhileParser.cpp"
    break;

  case 81:
#line 651 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::Multiplication>(new program::Multiplication(std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()),std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 2007 "../src/parser/WhileParser.cpp"
    break;

  case 82:
#line 652 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::Addition>(new program::Addition(std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()),std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 2013 "../src/parser/WhileParser.cpp"
    break;

  case 83:
#line 653 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::Subtraction>(new program::Subtraction(std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()),std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 2019 "../src/parser/WhileParser.cpp"
    break;

  case 84:
#line 654 "WhileParser.yy"
                           { yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::Modulo>(new program::Modulo(std::move(yystack_[2].value.as <  std::shared_ptr<const program::IntExpression>  > ()),std::move(yystack_[0].value.as <  std::shared_ptr<const program::IntExpression>  > ())));}
#line 2025 "../src/parser/WhileParser.cpp"
    break;

  case 85:
#line 659 "WhileParser.yy"
  { 
  	auto var = context.getProgramVar(yystack_[0].value.as < std::string > ());
    if(var->isArray)
    {
      error(yystack_[0].location, "Array variable " + var->name + " needs index for access");
    }
    yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::IntVariableAccess>(new IntVariableAccess(std::move(var)));
  }
#line 2038 "../src/parser/WhileParser.cpp"
    break;

  case 86:
#line 668 "WhileParser.yy"
  {
	  auto var = context.getProgramVar(yystack_[3].value.as < std::string > ());
    if(!var->isArray)
    {
      error(yystack_[3].location, "Variable " + var->name + " is not an array");
    }
	  yylhs.value.as <  std::shared_ptr<const program::IntExpression>  > () = std::shared_ptr<const program::IntArrayApplication>(new IntArrayApplication(std::move(var), std::move(yystack_[1].value.as <  std::shared_ptr<const program::IntExpression>  > ())));
  }
#line 2051 "../src/parser/WhileParser.cpp"
    break;


#line 2055 "../src/parser/WhileParser.cpp"

            default:
              break;
            }
        }
#if YY_EXCEPTIONS
      catch (const syntax_error& yyexc)
        {
          YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
          error (yyexc);
          YYERROR;
        }
#endif // YY_EXCEPTIONS
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;
      YY_STACK_PRINT ();

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, YY_MOVE (yylhs));
    }
    goto yynewstate;


  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        error (yyla.location, yysyntax_error_ (yystack_[0].state, yyla));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.type_get () == yyeof_)
          YYABORT;
        else if (!yyla.empty ())
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyla.clear ();
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:
    /* Pacify compilers when the user code never invokes YYERROR and
       the label yyerrorlab therefore never appears in user code.  */
    if (false)
      YYERROR;

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    goto yyerrlab1;


  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    {
      stack_symbol_type error_token;
      for (;;)
        {
          yyn = yypact_[+yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yy_error_token_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yy_error_token_)
                {
                  yyn = yytable_[yyn];
                  if (0 < yyn)
                    break;
                }
            }

          // Pop the current state because it cannot handle the error token.
          if (yystack_.size () == 1)
            YYABORT;

          yyerror_range[1].location = yystack_[0].location;
          yy_destroy_ ("Error: popping", yystack_[0]);
          yypop_ ();
          YY_STACK_PRINT ();
        }

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      error_token.state = state_type (yyn);
      yypush_ ("Shifting", YY_MOVE (error_token));
    }
    goto yynewstate;


  /*-------------------------------------.
  | yyacceptlab -- YYACCEPT comes here.  |
  `-------------------------------------*/
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;


  /*-----------------------------------.
  | yyabortlab -- YYABORT comes here.  |
  `-----------------------------------*/
  yyabortlab:
    yyresult = 1;
    goto yyreturn;


  /*-----------------------------------------------------.
  | yyreturn -- parsing is finished, return the result.  |
  `-----------------------------------------------------*/
  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
#if YY_EXCEPTIONS
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack\n";
        // Do not try to display the values of the reclaimed symbols,
        // as their printers might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
#endif // YY_EXCEPTIONS
  }

  void
  WhileParser::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what ());
  }

  // Generate an error message.
  std::string
  WhileParser::yysyntax_error_ (state_type yystate, const symbol_type& yyla) const
  {
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    std::ptrdiff_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yyla) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state merging
         (from LALR or IELR) and default reductions corrupt the expected
         token list.  However, the list is correct for canonical LR with
         one exception: it will still contain any token that will not be
         accepted due to an error action in a later state.
    */
    if (!yyla.empty ())
      {
        symbol_number_type yytoken = yyla.type_get ();
        yyarg[yycount++] = yytname_[yytoken];

        int yyn = yypact_[+yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            // Stay within bounds of both yycheck and yytname.
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yy_error_token_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
      default: // Avoid compiler warnings.
        YYCASE_ (0, YY_("syntax error"));
        YYCASE_ (1, YY_("syntax error, unexpected %s"));
        YYCASE_ (2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_ (3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_ (4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_ (5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    std::string yyres;
    // Argument number.
    std::ptrdiff_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const short WhileParser::yypact_ninf_ = -179;

  const signed char WhileParser::yytable_ninf_ = -1;

  const short
  WhileParser::yypact_[] =
  {
      -1,   -17,    46,    55,    27,  -179,    59,  -179,    55,  -179,
      67,    92,    94,  -179,  -179,    98,   147,  -179,    55,   105,
     111,   111,   111,  -179,  -179,  -179,  -179,   106,   100,   116,
     123,    94,  -179,    37,    37,    37,    37,    37,  -179,  -179,
     111,   111,   135,   152,  -179,  -179,  -179,   188,    70,  -179,
    -179,    37,    37,    37,    37,    37,    96,   179,   193,   111,
     195,   195,  -179,     9,    37,    37,    37,    37,    37,   196,
     197,   198,   199,   200,  -179,  -179,  -179,  -179,   201,   164,
     189,  -179,   191,   203,     5,   202,   171,   204,    39,  -179,
    -179,  -179,  -179,  -179,     2,   211,    37,    37,    37,    37,
      -6,  -179,  -179,  -179,  -179,  -179,  -179,  -179,   174,  -179,
    -179,  -179,     5,  -179,  -179,     5,     5,  -179,   159,   153,
    -179,  -179,    41,    24,   206,  -179,    24,  -179,    24,   209,
     210,   212,   213,  -179,  -179,   214,   111,   111,    97,   104,
     132,  -179,     5,     5,   208,    24,    24,    24,    24,    24,
      24,    24,    24,    24,    24,   215,  -179,    24,   173,   185,
     128,   145,  -179,  -179,  -179,  -179,  -179,   216,   218,  -179,
    -179,  -179,  -179,   205,  -179,  -179,    74,    74,  -179,   177,
     177,   177,   177,   177,   177,   190,   149,  -179,  -179,  -179,
    -179,  -179,  -179,   220,   217,  -179,  -179,  -179,  -179,    62,
    -179,   224,  -179,   221,  -179,  -179,    79,  -179
  };

  const signed char
  WhileParser::yydefact_[] =
  {
       2,     0,     0,     0,     0,     1,     0,     7,     6,    41,
       0,     0,     3,    42,     4,     0,     0,     8,     0,     0,
       0,     0,     0,     7,    43,    14,    15,     0,     0,     0,
       0,     5,    45,     0,     0,     0,     0,     0,    12,    12,
       0,     0,     0,     0,     9,    10,    11,    61,     0,    34,
      35,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    44,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    21,    13,    22,    23,     0,     0,
       0,    29,     0,     0,     0,     0,     0,    85,     0,    46,
      48,    49,    50,    51,     0,     0,     0,     0,     0,     0,
       0,    32,    16,    17,    18,    19,    20,    24,     0,    25,
      30,    27,     0,    67,    68,     0,     0,    80,    58,     0,
      79,    60,     0,     0,     0,    62,     0,    47,     0,     0,
       0,     0,     0,    36,    33,     0,     0,     0,     0,     0,
       0,    77,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    63,     0,     0,     0,
       0,     0,    40,    37,    38,    39,    31,     0,     0,    54,
      66,    78,    76,    75,    45,    81,    82,    83,    84,    69,
      70,    71,    72,    73,    74,     0,     0,    86,    64,    53,
      52,    26,    28,     0,    61,    65,    45,    59,    61,     0,
      55,     0,    56,     0,    45,    61,     0,    57
  };

  const short
  WhileParser::yypgoto_[] =
  {
    -179,  -179,  -179,  -179,   219,   222,  -179,   207,   -19,  -179,
    -179,   178,     4,  -179,   -23,  -179,   230,  -179,  -170,  -179,
    -179,  -179,  -179,  -179,  -179,  -179,  -179,  -179,  -178,  -179,
     -18,   -90,   -63
  };

  const short
  WhileParser::yydefgoto_[] =
  {
      -1,     2,     3,    18,     7,    12,    17,    56,    75,   136,
     137,    80,    81,   100,    51,     8,     9,    32,    47,    89,
      90,    91,   193,   201,   203,    92,   144,    93,    63,    94,
     118,   119,   120
  };

  const unsigned char
  WhileParser::yytable_[] =
  {
      95,    28,    29,    30,   194,    48,   133,   126,   113,   114,
       1,    52,    53,    54,    55,    83,   115,    84,    85,   127,
     199,    58,    59,   116,     4,   140,   198,   206,    69,    70,
      71,    72,    73,   158,   205,   157,   160,    49,   161,    50,
      78,    96,    97,    98,    99,   101,     5,    87,    48,    86,
     117,    87,   124,    88,   155,   175,   176,   177,   178,   179,
     180,   181,   182,   183,   184,     6,    87,   186,    83,   117,
      84,    85,    10,   129,   130,   131,   132,   134,   200,    14,
      49,   125,    50,   156,   110,    83,   110,    84,    85,    64,
      65,    66,    67,   145,   138,   207,   148,   139,   141,    25,
      26,    11,    86,    15,    87,    16,    88,    27,    74,   169,
      19,    33,    44,    68,    25,    26,   170,   167,   168,    86,
      24,    87,    27,    88,   172,   173,   142,   143,    45,    34,
      35,    36,    37,   142,   143,    46,    95,    38,    39,    40,
      41,    42,    43,    95,   171,   189,    60,   145,   146,   147,
     148,   145,   146,   147,   148,   149,   150,   151,   152,   153,
     154,   171,   190,    61,   145,   146,   147,   148,   145,   146,
     147,   148,   145,   146,   147,   148,   149,   150,   151,   152,
     153,   154,    25,    26,    20,    21,    22,   187,   142,   143,
      27,    76,   145,   146,   147,   148,   145,   146,   147,   148,
      79,   109,    79,   111,    62,    77,    79,   108,   102,   103,
     104,   105,   106,   107,   112,   122,   128,   123,   135,   121,
     159,   162,   163,   174,   164,   165,   166,   188,   191,   185,
     192,   202,   195,   197,   142,   196,   204,    23,    13,    82,
       0,     0,     0,     0,     0,    31,    57
  };

  const short
  WhileParser::yycheck_[] =
  {
      63,    20,    21,    22,   174,    11,    12,     5,     3,     4,
      11,    34,    35,    36,    37,     6,    11,     8,     9,    17,
     198,    40,    41,    18,    41,   115,   196,   205,    51,    52,
      53,    54,    55,   123,   204,    11,   126,    43,   128,    45,
      59,    64,    65,    66,    67,    68,     0,    42,    11,    40,
      45,    42,    13,    44,    13,   145,   146,   147,   148,   149,
     150,   151,   152,   153,   154,    10,    42,   157,     6,    45,
       8,     9,    45,    96,    97,    98,    99,   100,    16,    12,
      43,    42,    45,    42,    80,     6,    82,     8,     9,    19,
      20,    21,    22,    19,   112,    16,    22,   115,   116,     3,
       4,    42,    40,    11,    42,    11,    44,    11,    12,    12,
      12,     5,    12,    43,     3,     4,    12,   136,   137,    40,
      15,    42,    11,    44,   142,   143,    29,    30,    12,    23,
      24,    25,    26,    29,    30,    12,   199,    31,    32,    33,
      34,    35,    36,   206,    12,    17,    11,    19,    20,    21,
      22,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    12,    17,    11,    19,    20,    21,    22,    19,    20,
      21,    22,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,     3,     4,    37,    38,    39,    14,    29,    30,
      11,    12,    19,    20,    21,    22,    19,    20,    21,    22,
      11,    12,    11,    12,    16,    12,    11,    43,    12,    12,
      12,    12,    12,    12,    11,    44,     5,    13,    44,    17,
      14,    12,    12,    15,    12,    12,    12,    42,    12,    14,
      12,     7,    42,    16,    29,    15,    15,    18,     8,    61,
      -1,    -1,    -1,    -1,    -1,    23,    39
  };

  const signed char
  WhileParser::yystos_[] =
  {
       0,    11,    49,    50,    41,     0,    10,    52,    63,    64,
      45,    42,    53,    64,    12,    11,    11,    54,    51,    12,
      37,    38,    39,    52,    15,     3,     4,    11,    56,    56,
      56,    53,    65,     5,    23,    24,    25,    26,    31,    32,
      33,    34,    35,    36,    12,    12,    12,    66,    11,    43,
      45,    62,    62,    62,    62,    62,    55,    55,    56,    56,
      11,    11,    16,    76,    19,    20,    21,    22,    43,    62,
      62,    62,    62,    62,    12,    56,    12,    12,    56,    11,
      59,    60,    59,     6,     8,     9,    40,    42,    44,    67,
      68,    69,    73,    75,    77,    80,    62,    62,    62,    62,
      61,    62,    12,    12,    12,    12,    12,    12,    43,    12,
      60,    12,    11,     3,     4,    11,    18,    45,    78,    79,
      80,    17,    44,    13,    13,    42,     5,    17,     5,    62,
      62,    62,    62,    12,    62,    44,    57,    58,    78,    78,
      79,    78,    29,    30,    74,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    13,    42,    11,    79,    14,
      79,    79,    12,    12,    12,    12,    12,    56,    56,    12,
      12,    12,    78,    78,    15,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    79,    14,    79,    14,    42,    17,
      17,    12,    12,    70,    66,    42,    15,    16,    66,    76,
      16,    71,     7,    72,    15,    66,    76,    16
  };

  const signed char
  WhileParser::yyr1_[] =
  {
       0,    48,    50,    49,    51,    49,    52,    53,    53,    54,
      54,    54,    55,    55,    56,    56,    56,    56,    56,    56,
      56,    56,    56,    56,    56,    57,    56,    58,    56,    59,
      59,    60,    61,    61,    62,    62,    62,    62,    62,    62,
      62,    63,    63,    65,    64,    66,    66,    66,    67,    67,
      67,    67,    68,    68,    70,    71,    72,    69,    74,    73,
      75,    76,    77,    77,    77,    77,    78,    78,    78,    78,
      78,    78,    78,    78,    78,    78,    78,    78,    79,    79,
      79,    79,    79,    79,    79,    80,    80
  };

  const signed char
  WhileParser::yyr2_[] =
  {
       0,     2,     0,     3,     0,     7,     1,     0,     2,     4,
       4,     4,     0,     2,     1,     1,     5,     5,     5,     5,
       5,     4,     4,     4,     5,     0,     8,     0,     8,     1,
       2,     4,     1,     2,     1,     1,     4,     5,     5,     5,
       5,     1,     2,     0,     8,     0,     3,     4,     1,     1,
       1,     1,     4,     4,     0,     0,     0,    16,     0,     6,
       2,     0,     2,     3,     4,     5,     3,     1,     1,     3,
       3,     3,     3,     3,     3,     3,     3,     2,     3,     1,
       1,     3,     3,     3,     3,     1,     4
  };



  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const WhileParser::yytname_[] =
  {
  "\"EOF\"", "error", "$undefined", "\"true\"", "\"false\"", "\"=\"",
  "\"if\"", "\"else\"", "\"while\"", "\"skip\"", "\"func\"", "\"(\"",
  "\")\"", "\"[\"", "\"]\"", "\"{\"", "\"}\"", "\";\"", "\"!\"", "\"*\"",
  "\"+\"", "\"-\"", "\"mod\"", "\">\"", "\">=\"", "\"<\"", "\"<=\"",
  "\"==\"", "\"!=\"", "\"||\"", "\"&&\"", "\"and\"", "\"or\"", "\"not\"",
  "\"=>\"", "\"forall\"", "\"exists\"", "\"axiom\"", "\"lemma\"",
  "\"conjecture\"", "\"const\"", "\"set-traces\"",
  "\"program identifier\"", "\"smtlib identifier\"", "\"type identifier\"",
  "\"number\"", "DIV", "UMINUS", "$accept", "problem", "$@1", "$@2",
  "program", "smtlib_problemitem_list", "smtlib_problemitem",
  "smtlib_formula_list", "smtlib_formula", "$@3", "$@4",
  "smtlib_quantvar_list", "smtlib_quantvar", "smtlib_term_list",
  "smtlib_term", "function_list", "function", "$@5", "statement_list",
  "statement", "assignment_statement", "if_else_statement", "$@6", "$@7",
  "$@8", "while_statement", "$@9", "skip_statement", "active_vars_dummy",
  "var_definition_head", "formula", "expr", "location", YY_NULLPTR
  };

#if YYDEBUG
  const short
  WhileParser::yyrline_[] =
  {
       0,   154,   154,   154,   163,   162,   180,   187,   188,   192,
     198,   204,   211,   212,   216,   217,   218,   229,   241,   253,
     265,   277,   278,   279,   280,   282,   281,   292,   291,   304,
     305,   309,   343,   344,   348,   362,   366,   391,   403,   415,
     427,   442,   443,   448,   447,   469,   470,   476,   486,   487,
     488,   489,   493,   514,   534,   538,   542,   533,   559,   558,
     570,   574,   581,   593,   605,   617,   632,   633,   634,   635,
     636,   637,   638,   639,   640,   642,   643,   644,   648,   649,
     650,   651,   652,   653,   654,   658,   667
  };

  // Print the state stack on the debug stream.
  void
  WhileParser::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << int (i->state);
    *yycdebug_ << '\n';
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  WhileParser::yy_reduce_print_ (int yyrule)
  {
    int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):\n";
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG


#line 4 "WhileParser.yy"
} // parser
#line 2586 "../src/parser/WhileParser.cpp"

#line 678 "WhileParser.yy"

void parser::WhileParser::error(const location_type& l,
                              const std::string& m)
{
  std::cout << "Error while parsing location " << l << ":\n" << m << std::endl;
  context.errorFlag = true;
  exit(1);
}

