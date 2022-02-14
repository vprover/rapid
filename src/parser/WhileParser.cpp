// A Bison parser, made by GNU Bison 3.4.2.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015, 2018-2019 Free Software Foundation, Inc.

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
# define YY_DECL parser::WhileParser::symbol_type yylex(parser::WhileParsingContext &parsing_context)
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
  WhileParser::WhileParser (parser::WhileParsingContext &parsing_context_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      parsing_context (parsing_context_yyarg)
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
      return yystos_[state];
  }

  WhileParser::stack_symbol_type::stack_symbol_type ()
  {}

  WhileParser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.location))
  {
    switch (that.type_get ())
    {
      case 57: // smtlib_problemitem
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (that.value));
        break;

      case 63: // smtlib_quantvar
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (that.value));
        break;

      case 59: // smtlib_term
        value.YY_MOVE_OR_COPY<  std::shared_ptr<const logic::Term>  > (YY_MOVE (that.value));
        break;

      case 69: // assignment_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Assignment>  > (YY_MOVE (that.value));
        break;

      case 73: // break_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::BreakStatement>  > (YY_MOVE (that.value));
        break;

      case 74: // continue_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::ContinueStatement>  > (YY_MOVE (that.value));
        break;

      case 81: // expr
      case 82: // location
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Expression>  > (YY_MOVE (that.value));
        break;

      case 65: // function
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Function>  > (YY_MOVE (that.value));
        break;

      case 70: // if_else_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::IfElseStatement>  > (YY_MOVE (that.value));
        break;

      case 55: // program
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Program>  > (YY_MOVE (that.value));
        break;

      case 75: // return_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::ReturnStatement>  > (YY_MOVE (that.value));
        break;

      case 76: // skip_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::SkipStatement>  > (YY_MOVE (that.value));
        break;

      case 68: // statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Statement>  > (YY_MOVE (that.value));
        break;

      case 80: // var_definition_head
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::Variable>  > (YY_MOVE (that.value));
        break;

      case 71: // while_statement
        value.YY_MOVE_OR_COPY<  std::shared_ptr<program::WhileStatement>  > (YY_MOVE (that.value));
        break;

      case 64: // function_list
        value.YY_MOVE_OR_COPY<  std::vector< std::shared_ptr<program::Function>>  > (YY_MOVE (that.value));
        break;

      case 56: // smtlib_problemitem_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (that.value));
        break;

      case 62: // smtlib_quantvar_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (that.value));
        break;

      case 58: // smtlib_term_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (that.value));
        break;

      case 67: // statement_list
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<program::Statement>>  > (YY_MOVE (that.value));
        break;

      case 77: // active_vars_dummy
        value.YY_MOVE_OR_COPY<  std::vector<std::shared_ptr<program::Variable>>  > (YY_MOVE (that.value));
        break;

      case 48: // "number"
        value.YY_MOVE_OR_COPY< int > (YY_MOVE (that.value));
        break;

      case 45: // "program identifier"
      case 46: // "smtlib identifier"
      case 47: // "type identifier"
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
      case 57: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (that.value));
        break;

      case 63: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (that.value));
        break;

      case 59: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (YY_MOVE (that.value));
        break;

      case 69: // assignment_statement
        value.move<  std::shared_ptr<program::Assignment>  > (YY_MOVE (that.value));
        break;

      case 73: // break_statement
        value.move<  std::shared_ptr<program::BreakStatement>  > (YY_MOVE (that.value));
        break;

      case 74: // continue_statement
        value.move<  std::shared_ptr<program::ContinueStatement>  > (YY_MOVE (that.value));
        break;

      case 81: // expr
      case 82: // location
        value.move<  std::shared_ptr<program::Expression>  > (YY_MOVE (that.value));
        break;

      case 65: // function
        value.move<  std::shared_ptr<program::Function>  > (YY_MOVE (that.value));
        break;

      case 70: // if_else_statement
        value.move<  std::shared_ptr<program::IfElseStatement>  > (YY_MOVE (that.value));
        break;

      case 55: // program
        value.move<  std::shared_ptr<program::Program>  > (YY_MOVE (that.value));
        break;

      case 75: // return_statement
        value.move<  std::shared_ptr<program::ReturnStatement>  > (YY_MOVE (that.value));
        break;

      case 76: // skip_statement
        value.move<  std::shared_ptr<program::SkipStatement>  > (YY_MOVE (that.value));
        break;

      case 68: // statement
        value.move<  std::shared_ptr<program::Statement>  > (YY_MOVE (that.value));
        break;

      case 80: // var_definition_head
        value.move<  std::shared_ptr<program::Variable>  > (YY_MOVE (that.value));
        break;

      case 71: // while_statement
        value.move<  std::shared_ptr<program::WhileStatement>  > (YY_MOVE (that.value));
        break;

      case 64: // function_list
        value.move<  std::vector< std::shared_ptr<program::Function>>  > (YY_MOVE (that.value));
        break;

      case 56: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (that.value));
        break;

      case 62: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (that.value));
        break;

      case 58: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (that.value));
        break;

      case 67: // statement_list
        value.move<  std::vector<std::shared_ptr<program::Statement>>  > (YY_MOVE (that.value));
        break;

      case 77: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<program::Variable>>  > (YY_MOVE (that.value));
        break;

      case 48: // "number"
        value.move< int > (YY_MOVE (that.value));
        break;

      case 45: // "program identifier"
      case 46: // "smtlib identifier"
      case 47: // "type identifier"
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
  WhileParser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    switch (that.type_get ())
    {
      case 57: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (that.value);
        break;

      case 63: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (that.value);
        break;

      case 59: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (that.value);
        break;

      case 69: // assignment_statement
        value.move<  std::shared_ptr<program::Assignment>  > (that.value);
        break;

      case 73: // break_statement
        value.move<  std::shared_ptr<program::BreakStatement>  > (that.value);
        break;

      case 74: // continue_statement
        value.move<  std::shared_ptr<program::ContinueStatement>  > (that.value);
        break;

      case 81: // expr
      case 82: // location
        value.move<  std::shared_ptr<program::Expression>  > (that.value);
        break;

      case 65: // function
        value.move<  std::shared_ptr<program::Function>  > (that.value);
        break;

      case 70: // if_else_statement
        value.move<  std::shared_ptr<program::IfElseStatement>  > (that.value);
        break;

      case 55: // program
        value.move<  std::shared_ptr<program::Program>  > (that.value);
        break;

      case 75: // return_statement
        value.move<  std::shared_ptr<program::ReturnStatement>  > (that.value);
        break;

      case 76: // skip_statement
        value.move<  std::shared_ptr<program::SkipStatement>  > (that.value);
        break;

      case 68: // statement
        value.move<  std::shared_ptr<program::Statement>  > (that.value);
        break;

      case 80: // var_definition_head
        value.move<  std::shared_ptr<program::Variable>  > (that.value);
        break;

      case 71: // while_statement
        value.move<  std::shared_ptr<program::WhileStatement>  > (that.value);
        break;

      case 64: // function_list
        value.move<  std::vector< std::shared_ptr<program::Function>>  > (that.value);
        break;

      case 56: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (that.value);
        break;

      case 62: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (that.value);
        break;

      case 58: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (that.value);
        break;

      case 67: // statement_list
        value.move<  std::vector<std::shared_ptr<program::Statement>>  > (that.value);
        break;

      case 77: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<program::Variable>>  > (that.value);
        break;

      case 48: // "number"
        value.move< int > (that.value);
        break;

      case 45: // "program identifier"
      case 46: // "smtlib identifier"
      case 47: // "type identifier"
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
      case 45: // "program identifier"
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as < std::string > (); }
#line 615 "../src/parser/WhileParser.cpp"
        break;

      case 46: // "smtlib identifier"
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as < std::string > (); }
#line 621 "../src/parser/WhileParser.cpp"
        break;

      case 47: // "type identifier"
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as < std::string > (); }
#line 627 "../src/parser/WhileParser.cpp"
        break;

      case 48: // "number"
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as < int > (); }
#line 633 "../src/parser/WhileParser.cpp"
        break;

      case 55: // program
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Program>  > (); }
#line 639 "../src/parser/WhileParser.cpp"
        break;

      case 56: // smtlib_problemitem_list
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (); }
#line 645 "../src/parser/WhileParser.cpp"
        break;

      case 57: // smtlib_problemitem
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::ProblemItem>  > (); }
#line 651 "../src/parser/WhileParser.cpp"
        break;

      case 58: // smtlib_term_list
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::Term>>  > (); }
#line 657 "../src/parser/WhileParser.cpp"
        break;

      case 59: // smtlib_term
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::Term>  > (); }
#line 663 "../src/parser/WhileParser.cpp"
        break;

      case 62: // smtlib_quantvar_list
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<const logic::Symbol>>  > (); }
#line 669 "../src/parser/WhileParser.cpp"
        break;

      case 63: // smtlib_quantvar
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<const logic::Symbol>  > (); }
#line 675 "../src/parser/WhileParser.cpp"
        break;

      case 64: // function_list
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector< std::shared_ptr<program::Function>>  > (); }
#line 681 "../src/parser/WhileParser.cpp"
        break;

      case 65: // function
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Function>  > (); }
#line 687 "../src/parser/WhileParser.cpp"
        break;

      case 67: // statement_list
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<program::Statement>>  > (); }
#line 693 "../src/parser/WhileParser.cpp"
        break;

      case 68: // statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Statement>  > (); }
#line 699 "../src/parser/WhileParser.cpp"
        break;

      case 69: // assignment_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Assignment>  > (); }
#line 705 "../src/parser/WhileParser.cpp"
        break;

      case 70: // if_else_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::IfElseStatement>  > (); }
#line 711 "../src/parser/WhileParser.cpp"
        break;

      case 71: // while_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::WhileStatement>  > (); }
#line 717 "../src/parser/WhileParser.cpp"
        break;

      case 73: // break_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::BreakStatement>  > (); }
#line 723 "../src/parser/WhileParser.cpp"
        break;

      case 74: // continue_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::ContinueStatement>  > (); }
#line 729 "../src/parser/WhileParser.cpp"
        break;

      case 75: // return_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::ReturnStatement>  > (); }
#line 735 "../src/parser/WhileParser.cpp"
        break;

      case 76: // skip_statement
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::SkipStatement>  > (); }
#line 741 "../src/parser/WhileParser.cpp"
        break;

      case 77: // active_vars_dummy
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::vector<std::shared_ptr<program::Variable>>  > (); }
#line 747 "../src/parser/WhileParser.cpp"
        break;

      case 80: // var_definition_head
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Variable>  > (); }
#line 753 "../src/parser/WhileParser.cpp"
        break;

      case 81: // expr
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Expression>  > (); }
#line 759 "../src/parser/WhileParser.cpp"
        break;

      case 82: // location
#line 141 "WhileParser.yy"
        { yyoutput << yysym.value.template as <  std::shared_ptr<program::Expression>  > (); }
#line 765 "../src/parser/WhileParser.cpp"
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
    // State.
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
  yyla.location.begin.filename = yyla.location.end.filename = &parsing_context.inputFile;
}

#line 890 "../src/parser/WhileParser.cpp"


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
    YYCDEBUG << "Entering state " << yystack_[0].state << '\n';

    // Accept?
    if (yystack_[0].state == yyfinal_)
      YYACCEPT;

    goto yybackup;


  /*-----------.
  | yybackup.  |
  `-----------*/
  yybackup:
    // Try to take a decision without lookahead.
    yyn = yypact_[yystack_[0].state];
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
            symbol_type yylookahead (yylex (parsing_context));
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
      goto yydefault;

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
    yypush_ ("Shifting", yyn, YY_MOVE (yyla));
    goto yynewstate;


  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystack_[0].state];
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
      case 57: // smtlib_problemitem
        yylhs.value.emplace<  std::shared_ptr<const logic::ProblemItem>  > ();
        break;

      case 63: // smtlib_quantvar
        yylhs.value.emplace<  std::shared_ptr<const logic::Symbol>  > ();
        break;

      case 59: // smtlib_term
        yylhs.value.emplace<  std::shared_ptr<const logic::Term>  > ();
        break;

      case 69: // assignment_statement
        yylhs.value.emplace<  std::shared_ptr<program::Assignment>  > ();
        break;

      case 73: // break_statement
        yylhs.value.emplace<  std::shared_ptr<program::BreakStatement>  > ();
        break;

      case 74: // continue_statement
        yylhs.value.emplace<  std::shared_ptr<program::ContinueStatement>  > ();
        break;

      case 81: // expr
      case 82: // location
        yylhs.value.emplace<  std::shared_ptr<program::Expression>  > ();
        break;

      case 65: // function
        yylhs.value.emplace<  std::shared_ptr<program::Function>  > ();
        break;

      case 70: // if_else_statement
        yylhs.value.emplace<  std::shared_ptr<program::IfElseStatement>  > ();
        break;

      case 55: // program
        yylhs.value.emplace<  std::shared_ptr<program::Program>  > ();
        break;

      case 75: // return_statement
        yylhs.value.emplace<  std::shared_ptr<program::ReturnStatement>  > ();
        break;

      case 76: // skip_statement
        yylhs.value.emplace<  std::shared_ptr<program::SkipStatement>  > ();
        break;

      case 68: // statement
        yylhs.value.emplace<  std::shared_ptr<program::Statement>  > ();
        break;

      case 80: // var_definition_head
        yylhs.value.emplace<  std::shared_ptr<program::Variable>  > ();
        break;

      case 71: // while_statement
        yylhs.value.emplace<  std::shared_ptr<program::WhileStatement>  > ();
        break;

      case 64: // function_list
        yylhs.value.emplace<  std::vector< std::shared_ptr<program::Function>>  > ();
        break;

      case 56: // smtlib_problemitem_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
        break;

      case 62: // smtlib_quantvar_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::Symbol>>  > ();
        break;

      case 58: // smtlib_term_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<const logic::Term>>  > ();
        break;

      case 67: // statement_list
        yylhs.value.emplace<  std::vector<std::shared_ptr<program::Statement>>  > ();
        break;

      case 77: // active_vars_dummy
        yylhs.value.emplace<  std::vector<std::shared_ptr<program::Variable>>  > ();
        break;

      case 48: // "number"
        yylhs.value.emplace< int > ();
        break;

      case 45: // "program identifier"
      case 46: // "smtlib identifier"
      case 47: // "type identifier"
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
#line 157 "WhileParser.yy"
    {
    logic::Theory::declareTheories();
  }
#line 1112 "../src/parser/WhileParser.cpp"
    break;

  case 3:
#line 161 "WhileParser.yy"
    {
    parsing_context.problemItems = yystack_[0].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
  }
#line 1120 "../src/parser/WhileParser.cpp"
    break;

  case 4:
#line 166 "WhileParser.yy"
    {
    if (yystack_[1].value.as < int > () < 1)
    {
      error(yystack_[1].location, "number of traces has to be greater than or equal to 1");
    }

    parsing_context.numberOfTraces = (unsigned) yystack_[1].value.as < int > ();
    logic::Theory::declareTheories();
    declareSymbolsForTraces(parsing_context.numberOfTraces);
  }
#line 1135 "../src/parser/WhileParser.cpp"
    break;

  case 5:
#line 177 "WhileParser.yy"
    {
        parsing_context.problemItems = yystack_[0].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
  }
#line 1143 "../src/parser/WhileParser.cpp"
    break;

  case 6:
#line 184 "WhileParser.yy"
    { 
    parsing_context.program = std::unique_ptr<program::Program>(new program::Program(yystack_[0].value.as <  std::vector< std::shared_ptr<program::Function>>  > ())); 
  }
#line 1151 "../src/parser/WhileParser.cpp"
    break;

  case 7:
#line 190 "WhileParser.yy"
    {yylhs.value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > () = std::vector<std::shared_ptr<const logic::ProblemItem>>();}
#line 1157 "../src/parser/WhileParser.cpp"
    break;

  case 8:
#line 191 "WhileParser.yy"
    {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::ProblemItem>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ());}
#line 1163 "../src/parser/WhileParser.cpp"
    break;

  case 9:
#line 196 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Axiom>(new logic::Axiom(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > (), "user-axiom-" + std::to_string(parsing_context.numberOfAxioms)));
    parsing_context.numberOfAxioms++;
  }
#line 1172 "../src/parser/WhileParser.cpp"
    break;

  case 10:
#line 202 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Lemma>(new logic::Lemma(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > (), "user-lemma-" + std::to_string(parsing_context.numberOfLemmas)));
    parsing_context.numberOfLemmas++;
  }
#line 1181 "../src/parser/WhileParser.cpp"
    break;

  case 11:
#line 208 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<const logic::ProblemItem>  > () = std::shared_ptr<const logic::Conjecture>(new logic::Conjecture(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > (), "user-conjecture-" + std::to_string(parsing_context.numberOfConjectures)));
    parsing_context.numberOfConjectures++;
  }
#line 1190 "../src/parser/WhileParser.cpp"
    break;

  case 12:
#line 215 "WhileParser.yy"
    {yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > () = std::vector<std::shared_ptr<const logic::Term>>();}
#line 1196 "../src/parser/WhileParser.cpp"
    break;

  case 13:
#line 216 "WhileParser.yy"
    {yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > () = std::vector<std::shared_ptr<const logic::Term>>(); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().push_back(yystack_[0].value.as <  std::shared_ptr<const logic::Term>  > ());}
#line 1202 "../src/parser/WhileParser.cpp"
    break;

  case 14:
#line 217 "WhileParser.yy"
    {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Term>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Term>>  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ());}
#line 1208 "../src/parser/WhileParser.cpp"
    break;

  case 15:
#line 222 "WhileParser.yy"
    {
  if (!parsing_context.isDeclared(yystack_[0].value.as < std::string > ()))
  {
    error(yystack_[0].location, yystack_[0].value.as < std::string > () + " has not been declared");
  }
  auto symbol = parsing_context.fetch(yystack_[0].value.as < std::string > ());

  if (symbol->argSorts.size() > 0)
  {
      error(yystack_[0].location, "Not enough arguments for term " + symbol->name);
  }
  if (symbol->rngSort == logic::Sorts::boolSort())
  {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::predicate(symbol, std::vector<std::shared_ptr<const logic::Term>>());
  }
  else
  {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Terms::func(symbol, std::vector<std::shared_ptr<const logic::Term>>());
  }
}
#line 1233 "../src/parser/WhileParser.cpp"
    break;

  case 16:
#line 243 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intConstant(yystack_[0].value.as < int > ());
  }
#line 1241 "../src/parser/WhileParser.cpp"
    break;

  case 17:
#line 247 "WhileParser.yy"
    {
  if (!parsing_context.isDeclared(yystack_[2].value.as < std::string > ()))
  {
    error(yystack_[2].location, yystack_[2].value.as < std::string > () + " has not been declared");
  }
  auto symbol = parsing_context.fetch(yystack_[2].value.as < std::string > ());

  if (yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().size() < symbol->argSorts.size())
  {
      error(yystack_[1].location, "Not enough arguments for term " + symbol->name);
  }
  if (yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ().size() > symbol->argSorts.size())
  {
      error(yystack_[1].location, "Too many arguments for term " + symbol->name);
  }
  for (int i = 0; i < symbol->argSorts.size(); ++i)
  {
      if (symbol->argSorts[i] != yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()[i]->symbol->rngSort)
      {
        error(yystack_[1].location, "Argument has type " + yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()[i]->symbol->rngSort->name + " instead of " + symbol->argSorts[i]->name);
      }
  }
  if (symbol->rngSort == logic::Sorts::boolSort())
  {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::predicate(symbol, std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()));
  }
  else
  {
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Terms::func(symbol, std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()));
  }
}
#line 1277 "../src/parser/WhileParser.cpp"
    break;

  case 18:
#line 279 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intAddition(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1293 "../src/parser/WhileParser.cpp"
    break;

  case 19:
#line 291 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intSubtraction(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1309 "../src/parser/WhileParser.cpp"
    break;

  case 20:
#line 303 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intModulo(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1325 "../src/parser/WhileParser.cpp"
    break;

  case 21:
#line 315 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intMultiplication(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1341 "../src/parser/WhileParser.cpp"
    break;

  case 22:
#line 326 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::boolTrue();}
#line 1347 "../src/parser/WhileParser.cpp"
    break;

  case 23:
#line 327 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::boolFalse();}
#line 1353 "../src/parser/WhileParser.cpp"
    break;

  case 24:
#line 329 "WhileParser.yy"
    {
    auto leftSort = yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort;
    auto rightSort = yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort;

    if (leftSort != rightSort)
    {
      error(yystack_[1].location, "Argument types " + leftSort->name + " and " + rightSort->name + " don't match!");
    }
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::equality(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
  }
#line 1368 "../src/parser/WhileParser.cpp"
    break;

  case 25:
#line 340 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intGreater(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1384 "../src/parser/WhileParser.cpp"
    break;

  case 26:
#line 352 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intGreaterEqual(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1400 "../src/parser/WhileParser.cpp"
    break;

  case 27:
#line 364 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intLess(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1416 "../src/parser/WhileParser.cpp"
    break;

  case 28:
#line 376 "WhileParser.yy"
    {
  if (yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[2].location, "Left argument type needs to be Int");
  }
  if (yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()->symbol->rngSort != logic::Sorts::intSort())
  {
    error(yystack_[1].location, "Right argument type needs to be Int");
  }
  yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Theory::intLessEqual(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
}
#line 1432 "../src/parser/WhileParser.cpp"
    break;

  case 29:
#line 387 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::conjunction(std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()));}
#line 1438 "../src/parser/WhileParser.cpp"
    break;

  case 30:
#line 388 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::disjunction(std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Term>>  > ()));}
#line 1444 "../src/parser/WhileParser.cpp"
    break;

  case 31:
#line 389 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::negation(std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));}
#line 1450 "../src/parser/WhileParser.cpp"
    break;

  case 32:
#line 390 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::implication(std::move(yystack_[2].value.as <  std::shared_ptr<const logic::Term>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));}
#line 1456 "../src/parser/WhileParser.cpp"
    break;

  case 33:
#line 392 "WhileParser.yy"
    {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());
  }
#line 1465 "../src/parser/WhileParser.cpp"
    break;

  case 34:
#line 397 "WhileParser.yy"
    { 
    parsing_context.popQuantifiedVars();
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::universal(std::move(yystack_[4].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
  }
#line 1474 "../src/parser/WhileParser.cpp"
    break;

  case 35:
#line 402 "WhileParser.yy"
    {
    // TODO: propagate existing-var-error to parser and raise error
    parsing_context.pushQuantifiedVars(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());
  }
#line 1483 "../src/parser/WhileParser.cpp"
    break;

  case 36:
#line 407 "WhileParser.yy"
    { 
    parsing_context.popQuantifiedVars();
    yylhs.value.as <  std::shared_ptr<const logic::Term>  > () = logic::Formulas::existential(std::move(yystack_[4].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<const logic::Term>  > ()));
  }
#line 1492 "../src/parser/WhileParser.cpp"
    break;

  case 37:
#line 414 "WhileParser.yy"
    {auto vec = std::vector<std::shared_ptr<const logic::Symbol>>(); vec.push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Symbol>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > () = std::move(vec);}
#line 1498 "../src/parser/WhileParser.cpp"
    break;

  case 38:
#line 415 "WhileParser.yy"
    {yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<const logic::Symbol>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > () = std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<const logic::Symbol>>  > ());}
#line 1504 "../src/parser/WhileParser.cpp"
    break;

  case 39:
#line 420 "WhileParser.yy"
    { 
    if(parsing_context.isDeclared(yystack_[2].value.as < std::string > ()))
    {
      error(yystack_[2].location, yystack_[2].value.as < std::string > () + " has already been declared");
    }
    if (yystack_[1].value.as < std::string > () == "Int")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::intSort());
    }
    else if (yystack_[1].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::boolSort());
    }
    else if (yystack_[1].value.as < std::string > () == "Nat")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::natSort());
    }
    else if (yystack_[1].value.as < std::string > () == "Time")
    {
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::timeSort());
    }
    else
    {
      if (yystack_[1].value.as < std::string > () != "Trace")
      {
        error(yystack_[1].location, "Only the sorts Int, Bool, Time and Trace are supported");
      }
      yylhs.value.as <  std::shared_ptr<const logic::Symbol>  > () = logic::Signature::varSymbol(yystack_[2].value.as < std::string > (), logic::Sorts::traceSort());
    }
  }
#line 1539 "../src/parser/WhileParser.cpp"
    break;

  case 40:
#line 453 "WhileParser.yy"
    {auto v = std::vector< std::shared_ptr<program::Function>>(); v.push_back(std::move(yystack_[0].value.as <  std::shared_ptr<program::Function>  > ())); yylhs.value.as <  std::vector< std::shared_ptr<program::Function>>  > () = std::move(v);}
#line 1545 "../src/parser/WhileParser.cpp"
    break;

  case 41:
#line 454 "WhileParser.yy"
    {yystack_[1].value.as <  std::vector< std::shared_ptr<program::Function>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<program::Function>  > ())); yylhs.value.as <  std::vector< std::shared_ptr<program::Function>>  > () = std::move(yystack_[1].value.as <  std::vector< std::shared_ptr<program::Function>>  > ());}
#line 1551 "../src/parser/WhileParser.cpp"
    break;

  case 42:
#line 459 "WhileParser.yy"
    {
    parsing_context.pushProgramVars();
  }
#line 1559 "../src/parser/WhileParser.cpp"
    break;

  case 43:
#line 463 "WhileParser.yy"
    {
    auto functionEndLocationName = yystack_[6].value.as < std::string > () + "_end";
    parsing_context.locationToActiveVars[functionEndLocationName] = parsing_context.getActiveProgramVars();
    parsing_context.popProgramVars();

  	auto function = std::shared_ptr<program::Function>(new program::Function(yystack_[6].value.as < std::string > (), std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ())));

    // compute enclosing loops
    parsing_context.addEnclosingLoops(*function);
    yylhs.value.as <  std::shared_ptr<program::Function>  > () = function;

    // declare symbols for loops (needs to be done here, since it depends on enclosingLoops)
    declareSymbolsForFunction(function.get(), parsing_context.numberOfTraces);
  }
#line 1578 "../src/parser/WhileParser.cpp"
    break;

  case 44:
#line 480 "WhileParser.yy"
    {yylhs.value.as <  std::vector<std::shared_ptr<program::Statement>>  > () = std::vector<std::shared_ptr<program::Statement>>();}
#line 1584 "../src/parser/WhileParser.cpp"
    break;

  case 45:
#line 482 "WhileParser.yy"
    {
    auto locationName = yystack_[0].value.as <  std::shared_ptr<program::Statement>  > ()->location;
    parsing_context.locationToActiveVars[locationName] = yystack_[1].value.as <  std::vector<std::shared_ptr<program::Variable>>  > ();
    yystack_[2].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ().push_back(std::move(yystack_[0].value.as <  std::shared_ptr<program::Statement>  > ())); yylhs.value.as <  std::vector<std::shared_ptr<program::Statement>>  > () = std::move(yystack_[2].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ());
  }
#line 1594 "../src/parser/WhileParser.cpp"
    break;

  case 46:
#line 488 "WhileParser.yy"
    {
    // dummy is not used here, but silences a shift-reduce conflict
    parsing_context.addProgramVar(yystack_[1].value.as <  std::shared_ptr<program::Variable>  > ());
    declareSymbolForProgramVar(yystack_[1].value.as <  std::shared_ptr<program::Variable>  > ().get());
    yylhs.value.as <  std::vector<std::shared_ptr<program::Statement>>  > () = std::move(yystack_[3].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ());
  }
#line 1605 "../src/parser/WhileParser.cpp"
    break;

  case 47:
#line 497 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::Assignment>  > ());}
#line 1611 "../src/parser/WhileParser.cpp"
    break;

  case 48:
#line 498 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::IfElseStatement>  > ());}
#line 1617 "../src/parser/WhileParser.cpp"
    break;

  case 49:
#line 499 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::WhileStatement>  > ());}
#line 1623 "../src/parser/WhileParser.cpp"
    break;

  case 50:
#line 500 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::BreakStatement>  > ());}
#line 1629 "../src/parser/WhileParser.cpp"
    break;

  case 51:
#line 501 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::ContinueStatement>  > ());}
#line 1635 "../src/parser/WhileParser.cpp"
    break;

  case 52:
#line 502 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::ReturnStatement>  > ());}
#line 1641 "../src/parser/WhileParser.cpp"
    break;

  case 53:
#line 503 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::Statement>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::SkipStatement>  > ());}
#line 1647 "../src/parser/WhileParser.cpp"
    break;

  case 54:
#line 508 "WhileParser.yy"
    {
    if (typeid(*yystack_[3].value.as <  std::shared_ptr<program::Expression>  > ()) == typeid(VariableAccess))
    {
      auto variableAccess = std::static_pointer_cast<program::VariableAccess>(yystack_[3].value.as <  std::shared_ptr<program::Expression>  > ());
      if (variableAccess->var->isConstant)
      {
        error(yystack_[3].location, "Assignment to const var " + variableAccess->var->name);
      }
    }
    else
    {
      assert(typeid(*yystack_[3].value.as <  std::shared_ptr<program::Expression>  > ()) == typeid(ArrayApplication));
      auto arrayApplication = std::static_pointer_cast<program::ArrayApplication>(yystack_[3].value.as <  std::shared_ptr<program::Expression>  > ());
      if (arrayApplication->array->isConstant)
      {
        error(yystack_[3].location, "Assignment to const var " + arrayApplication->array->name);
      }
    }
    yylhs.value.as <  std::shared_ptr<program::Assignment>  > () = std::shared_ptr<program::Assignment>(new program::Assignment(yystack_[2].location.begin.line, std::move(yystack_[3].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[1].value.as <  std::shared_ptr<program::Expression>  > ())));
  }
#line 1672 "../src/parser/WhileParser.cpp"
    break;

  case 55:
#line 529 "WhileParser.yy"
    {
    // declare var
    parsing_context.addProgramVar(yystack_[3].value.as <  std::shared_ptr<program::Variable>  > ());
    declareSymbolForProgramVar(yystack_[3].value.as <  std::shared_ptr<program::Variable>  > ().get());

    // construct location
    if (yystack_[3].value.as <  std::shared_ptr<program::Variable>  > ()->isArray)
    {
      error(yystack_[3].location, "Combined declaration and assignment not allowed, since " + yystack_[3].value.as <  std::shared_ptr<program::Variable>  > ()->name + " is array variable");
    }
    auto variableAccess = std::shared_ptr<program::VariableAccess>(new VariableAccess(std::move(yystack_[3].value.as <  std::shared_ptr<program::Variable>  > ())));

    // build assignment
    yylhs.value.as <  std::shared_ptr<program::Assignment>  > () = std::shared_ptr<program::Assignment>(new program::Assignment(yystack_[2].location.begin.line, std::move(variableAccess), std::move(yystack_[1].value.as <  std::shared_ptr<program::Expression>  > ())));
  }
#line 1692 "../src/parser/WhileParser.cpp"
    break;

  case 56:
#line 550 "WhileParser.yy"
    {
    auto leftEndLocationName = "l" + std::to_string(yystack_[9].location.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(yystack_[9].location.begin.line) + "_rEnd";
    parsing_context.locationToActiveVars[leftEndLocationName] = yystack_[2].value.as <  std::vector<std::shared_ptr<program::Variable>>  > ();
    parsing_context.locationToActiveVars[rightEndLocationName] = parsing_context.getActiveProgramVars();
    std::vector<std::shared_ptr<program::Statement>> emptyElse;
    auto skipStatement = std::shared_ptr<program::SkipStatement>(new program::SkipStatement(0));
    parsing_context.locationToActiveVars[skipStatement->location] = parsing_context.getActiveProgramVars();
    emptyElse.push_back(std::move(skipStatement));
    yylhs.value.as <  std::shared_ptr<program::IfElseStatement>  > () = std::shared_ptr<program::IfElseStatement>(new program::IfElseStatement(yystack_[9].location.begin.line, std::move(yystack_[7].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[3].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ()), std::move(emptyElse)));
  }
#line 1708 "../src/parser/WhileParser.cpp"
    break;

  case 57:
#line 566 "WhileParser.yy"
    {
    auto leftEndLocationName = "l" + std::to_string(yystack_[16].location.begin.line) + "_lEnd";
    auto rightEndLocationName = "l" + std::to_string(yystack_[16].location.begin.line) + "_rEnd";
    parsing_context.locationToActiveVars[leftEndLocationName] = yystack_[9].value.as <  std::vector<std::shared_ptr<program::Variable>>  > ();
    parsing_context.locationToActiveVars[rightEndLocationName] = yystack_[2].value.as <  std::vector<std::shared_ptr<program::Variable>>  > ();
    yylhs.value.as <  std::shared_ptr<program::IfElseStatement>  > () = std::shared_ptr<program::IfElseStatement>(new program::IfElseStatement(yystack_[16].location.begin.line, std::move(yystack_[14].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[10].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ()), std::move(yystack_[3].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ())));
  }
#line 1720 "../src/parser/WhileParser.cpp"
    break;

  case 58:
#line 577 "WhileParser.yy"
    {
    parsing_context.pushProgramVars();
  }
#line 1728 "../src/parser/WhileParser.cpp"
    break;

  case 59:
#line 581 "WhileParser.yy"
    {
    parsing_context.popProgramVars();
    yylhs.value.as <  std::shared_ptr<program::WhileStatement>  > () = std::shared_ptr<program::WhileStatement>(new program::WhileStatement(yystack_[5].location.begin.line, std::move(yystack_[4].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[1].value.as <  std::vector<std::shared_ptr<program::Statement>>  > ())));
  }
#line 1737 "../src/parser/WhileParser.cpp"
    break;

  case 60:
#line 589 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<program::BreakStatement>  > () = std::shared_ptr<program::BreakStatement>(new program::BreakStatement(yystack_[0].location.begin.line));
  }
#line 1745 "../src/parser/WhileParser.cpp"
    break;

  case 61:
#line 595 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<program::ContinueStatement>  > () = std::shared_ptr<program::ContinueStatement>(new program::ContinueStatement(yystack_[0].location.begin.line));
  }
#line 1753 "../src/parser/WhileParser.cpp"
    break;

  case 62:
#line 601 "WhileParser.yy"
    {
    yylhs.value.as <  std::shared_ptr<program::ReturnStatement>  > () = std::shared_ptr<program::ReturnStatement>(new program::ReturnStatement(yystack_[1].location.begin.line, std::move(yystack_[1].value.as <  std::shared_ptr<program::Expression>  > ())));
  }
#line 1761 "../src/parser/WhileParser.cpp"
    break;

  case 63:
#line 607 "WhileParser.yy"
    {yylhs.value.as <  std::shared_ptr<program::SkipStatement>  > () = std::shared_ptr<program::SkipStatement>(new program::SkipStatement(yystack_[1].location.begin.line));}
#line 1767 "../src/parser/WhileParser.cpp"
    break;

  case 64:
#line 612 "WhileParser.yy"
    {
    yylhs.value.as <  std::vector<std::shared_ptr<program::Variable>>  > () = parsing_context.getActiveProgramVars();
  }
#line 1775 "../src/parser/WhileParser.cpp"
    break;

  case 65:
#line 619 "WhileParser.yy"
    {
    parsing_context.pushProgramVars();
  }
#line 1783 "../src/parser/WhileParser.cpp"
    break;

  case 66:
#line 626 "WhileParser.yy"
    {
    parsing_context.popProgramVars();
  }
#line 1791 "../src/parser/WhileParser.cpp"
    break;

  case 67:
#line 633 "WhileParser.yy"
    {
    if (yystack_[1].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::BoolVariable(yystack_[0].value.as < std::string > (), false, false, parsing_context.numberOfTraces));
    }
    else if (yystack_[1].value.as < std::string > () == "Nat" || yystack_[1].value.as < std::string > () == "Time" || yystack_[1].value.as < std::string > () == "Trace")
    {
      error(yystack_[1].location, "Program variables can't have type " + yystack_[1].value.as < std::string > ());
    }
    else
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::IntVariable(yystack_[0].value.as < std::string > (), false, false, parsing_context.numberOfTraces));
    }
  }
#line 1810 "../src/parser/WhileParser.cpp"
    break;

  case 68:
#line 648 "WhileParser.yy"
    {
    if (yystack_[1].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::BoolVariable(yystack_[0].value.as < std::string > (), true, false, parsing_context.numberOfTraces));
    }
    else if (yystack_[1].value.as < std::string > () == "Nat" || yystack_[1].value.as < std::string > () == "Time" || yystack_[1].value.as < std::string > () == "Trace")
    {
      error(yystack_[1].location, "Program variables can't have type " + yystack_[1].value.as < std::string > ());
    }
    else
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::IntVariable(yystack_[0].value.as < std::string > (), true, false, parsing_context.numberOfTraces));
    }
  }
#line 1829 "../src/parser/WhileParser.cpp"
    break;

  case 69:
#line 663 "WhileParser.yy"
    {
    if (yystack_[3].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::BoolVariable(yystack_[0].value.as < std::string > (), false, true, parsing_context.numberOfTraces));
    }
    else if (yystack_[3].value.as < std::string > () == "Nat" || yystack_[3].value.as < std::string > () == "Time" || yystack_[3].value.as < std::string > () == "Trace")
    {
      error(yystack_[3].location, "Program variables can't have type " + yystack_[3].value.as < std::string > ());
    }
    else
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::IntVariable(yystack_[0].value.as < std::string > (), false, true, parsing_context.numberOfTraces));
    }
  }
#line 1848 "../src/parser/WhileParser.cpp"
    break;

  case 70:
#line 678 "WhileParser.yy"
    {
    if (yystack_[3].value.as < std::string > () == "Bool")
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::BoolVariable(yystack_[0].value.as < std::string > (), true, true, parsing_context.numberOfTraces));
    }
    else if (yystack_[3].value.as < std::string > () == "Nat" || yystack_[3].value.as < std::string > () == "Time" || yystack_[3].value.as < std::string > () == "Trace")
    {
      error(yystack_[3].location, "Program variables can't have type " + yystack_[3].value.as < std::string > ());
    }
    else
    {
      yylhs.value.as <  std::shared_ptr<program::Variable>  > () = std::shared_ptr<program::Variable>(new program::IntVariable(yystack_[0].value.as < std::string > (), true, true, parsing_context.numberOfTraces));
    }
  }
#line 1867 "../src/parser/WhileParser.cpp"
    break;

  case 71:
#line 695 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::move(yystack_[1].value.as <  std::shared_ptr<program::Expression>  > ()); }
#line 1873 "../src/parser/WhileParser.cpp"
    break;

  case 72:
#line 696 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ()); }
#line 1879 "../src/parser/WhileParser.cpp"
    break;

  case 73:
#line 697 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanConstant>(new program::BooleanConstant(true)); }
#line 1885 "../src/parser/WhileParser.cpp"
    break;

  case 74:
#line 698 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanConstant>(new program::BooleanConstant(false)); }
#line 1891 "../src/parser/WhileParser.cpp"
    break;

  case 75:
#line 699 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticConstant>(new program::ArithmeticConstant(std::move(yystack_[0].value.as < int > ())));}
#line 1897 "../src/parser/WhileParser.cpp"
    break;

  case 76:
#line 700 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::Multiplication>(new program::Multiplication(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1903 "../src/parser/WhileParser.cpp"
    break;

  case 77:
#line 701 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::Addition>(new program::Addition(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1909 "../src/parser/WhileParser.cpp"
    break;

  case 78:
#line 702 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::Subtraction>(new program::Subtraction(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1915 "../src/parser/WhileParser.cpp"
    break;

  case 79:
#line 703 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::Modulo>(new program::Modulo(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1921 "../src/parser/WhileParser.cpp"
    break;

  case 80:
#line 705 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GT, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1927 "../src/parser/WhileParser.cpp"
    break;

  case 81:
#line 706 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::GE, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1933 "../src/parser/WhileParser.cpp"
    break;

  case 82:
#line 707 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LT, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1939 "../src/parser/WhileParser.cpp"
    break;

  case 83:
#line 708 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::LE, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1945 "../src/parser/WhileParser.cpp"
    break;

  case 84:
#line 709 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1951 "../src/parser/WhileParser.cpp"
    break;

  case 85:
#line 710 "WhileParser.yy"
    { auto formula = std::shared_ptr<program::ArithmeticComparison>(new program::ArithmeticComparison(program::ArithmeticComparison::Kind::EQ, std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));
                             yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanNot>(new program::BooleanNot(std::move(formula)));}
#line 1958 "../src/parser/WhileParser.cpp"
    break;

  case 86:
#line 712 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanAnd>(new program::BooleanAnd(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1964 "../src/parser/WhileParser.cpp"
    break;

  case 87:
#line 713 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanOr>(new program::BooleanOr(std::move(yystack_[2].value.as <  std::shared_ptr<program::Expression>  > ()), std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1970 "../src/parser/WhileParser.cpp"
    break;

  case 88:
#line 714 "WhileParser.yy"
    { yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::BooleanNot>(new program::BooleanNot(std::move(yystack_[0].value.as <  std::shared_ptr<program::Expression>  > ())));}
#line 1976 "../src/parser/WhileParser.cpp"
    break;

  case 89:
#line 720 "WhileParser.yy"
    { 
  	auto var = parsing_context.getProgramVar(yystack_[0].value.as < std::string > ());
    if(var->isArray)
    {
      error(yystack_[0].location, "Array variable " + var->name + " needs index for access");
    }
    yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::VariableAccess>(new VariableAccess(std::move(var)));
  }
#line 1989 "../src/parser/WhileParser.cpp"
    break;

  case 90:
#line 729 "WhileParser.yy"
    {
	  auto var = parsing_context.getProgramVar(yystack_[3].value.as < std::string > ());
    if(!var->isArray)
    {
      error(yystack_[3].location, "Variable " + var->name + " is not an array");
    }
    yylhs.value.as <  std::shared_ptr<program::Expression>  > () = std::shared_ptr<program::ArrayApplication>(new ArrayApplication(std::move(var), std::move(yystack_[1].value.as <  std::shared_ptr<program::Expression>  > ())));
  }
#line 2002 "../src/parser/WhileParser.cpp"
    break;


#line 2006 "../src/parser/WhileParser.cpp"

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
          yyn = yypact_[yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yyterror_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
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
      error_token.state = yyn;
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
    size_t yycount = 0;
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
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (!yyla.empty ())
      {
        int yytoken = yyla.type_get ();
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
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
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
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
    size_t yyi = 0;
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


  const short WhileParser::yypact_ninf_ = -196;

  const signed char WhileParser::yytable_ninf_ = -1;

  const short
  WhileParser::yypact_[] =
  {
      21,     9,    69,    58,    28,  -196,    32,  -196,    58,  -196,
      63,    77,    80,  -196,  -196,    81,   -32,  -196,    58,    86,
      98,    98,    98,  -196,  -196,  -196,  -196,   125,  -196,  -196,
      90,   111,   116,    80,  -196,    98,    98,    98,    98,    98,
      98,    98,    98,    98,    98,    98,    98,    98,    99,   118,
      98,  -196,  -196,  -196,   114,    98,    98,    98,    98,    98,
      98,    98,    98,    98,    47,  -196,    60,   119,    98,   121,
     121,    95,  -196,   188,   122,   123,   124,   127,   130,   140,
     141,   142,   143,  -196,  -196,  -196,  -196,   150,    94,     0,
    -196,    45,  -196,   152,    52,   147,   148,    52,   149,   131,
     161,   -12,  -196,  -196,  -196,  -196,  -196,  -196,  -196,  -196,
       6,   174,  -196,  -196,  -196,  -196,  -196,  -196,  -196,  -196,
    -196,  -196,   133,  -196,  -196,  -196,    52,  -196,  -196,    52,
      52,  -196,   285,  -196,  -196,  -196,   245,  -196,   -11,    52,
     172,  -196,    52,  -196,    52,   166,    98,    98,    92,   214,
    -196,    52,    52,    52,    52,    52,    52,    52,    52,    52,
      52,    52,    52,   173,  -196,   175,  -196,   231,   145,   259,
     273,  -196,   178,   186,  -196,  -196,  -196,    43,    43,  -196,
       7,     7,     7,     7,   318,   318,   308,   297,  -196,   157,
    -196,  -196,  -196,  -196,  -196,  -196,   185,   187,  -196,  -196,
    -196,  -196,   164,  -196,   197,  -196,   190,  -196,  -196,   176,
    -196,  -196
  };

  const unsigned char
  WhileParser::yydefact_[] =
  {
       2,     0,     0,     0,     0,     1,     0,     7,     6,    40,
       0,     0,     3,    41,     4,     0,     0,     8,     0,     0,
       0,     0,     0,     7,    42,    22,    23,     0,    15,    16,
       0,     0,     0,     5,    44,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    12,    12,     0,     0,     0,     0,
      12,     9,    10,    11,    64,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    13,     0,     0,     0,     0,
       0,     0,    43,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    29,    14,    30,    31,     0,     0,     0,
      37,     0,    17,     0,     0,     0,     0,     0,     0,     0,
      89,     0,    45,    47,    48,    49,    50,    51,    52,    53,
       0,     0,    24,    21,    18,    19,    20,    25,    26,    27,
      28,    32,     0,    33,    38,    35,     0,    73,    74,     0,
       0,    75,    58,    72,    60,    61,     0,    63,     0,     0,
       0,    67,     0,    46,     0,     0,     0,     0,     0,     0,
      88,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    62,     0,    68,     0,     0,     0,
       0,    39,     0,     0,    65,    71,    76,    77,    78,    79,
      80,    81,    82,    83,    84,    85,    87,    86,    44,     0,
      90,    69,    55,    54,    34,    36,     0,    64,    70,    44,
      59,    64,     0,    66,    56,    65,     0,    44,    64,     0,
      66,    57
  };

  const short
  WhileParser::yypgoto_[] =
  {
    -196,  -196,  -196,  -196,   192,   182,  -196,   -38,   -19,  -196,
    -196,   144,   -43,  -196,   204,  -196,   -96,  -196,  -196,  -196,
    -196,  -196,  -196,  -196,  -196,  -196,  -195,     8,     5,  -196,
     -72,   -73
  };

  const short
  WhileParser::yydefgoto_[] =
  {
      -1,     2,     3,    18,     7,    12,    17,    64,    65,   146,
     147,    89,    90,     8,     9,    34,    54,   102,   103,   104,
     105,   163,   106,   107,   108,   109,    73,   196,   204,   110,
     132,   133
  };

  const unsigned char
  WhileParser::yytable_[] =
  {
     111,    30,    31,    32,   140,   165,   202,    66,    20,    21,
      22,   142,    71,   209,    88,   123,    55,    56,    57,    58,
      59,    60,    61,    62,    63,   136,   143,    67,    68,   151,
     152,   153,   154,   141,   166,     1,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    84,   124,    84,   124,    87,
      25,    26,    84,     4,   148,   127,   128,   149,   150,    88,
     125,    27,    83,    25,    26,   151,   129,   167,   154,     5,
     169,     6,   170,   130,    27,    85,    10,    11,    14,   176,
     177,   178,   179,   180,   181,   182,   183,   184,   185,   186,
     187,    15,   197,    28,    16,    29,    19,   100,    25,    26,
     131,    25,    26,   201,    24,    51,    28,   174,    29,    27,
      92,   208,    27,    69,   151,   152,   153,   154,   155,   156,
     157,   158,   159,   160,   161,   162,    52,   172,   173,   111,
      35,    53,    70,    72,    86,    88,   111,   112,   113,   114,
     122,    28,   115,    29,    28,   116,    29,    36,    37,    38,
      39,    40,    41,    42,    43,   117,   118,   119,   120,    44,
      45,    46,    47,    48,    49,   121,   126,   134,   135,   137,
      93,    50,    94,    95,    96,    97,    98,   139,   138,   144,
     145,   171,    93,   203,    94,    95,    96,    97,    98,   168,
     191,   188,   189,   194,    93,   210,    94,    95,    96,    97,
      98,   195,   198,   199,   205,    33,   200,    99,   207,   100,
      23,   101,    13,   206,    91,   211,     0,     0,     0,    99,
       0,   100,     0,   101,     0,     0,     0,     0,     0,   175,
       0,    99,     0,   100,     0,   101,   151,   152,   153,   154,
     155,   156,   157,   158,   159,   160,   161,   162,   190,     0,
       0,     0,     0,   151,   152,   153,   154,   155,   156,   157,
     158,   159,   160,   161,   162,   164,     0,   151,   152,   153,
     154,   155,   156,   157,   158,   159,   160,   161,   162,   192,
       0,   151,   152,   153,   154,   155,   156,   157,   158,   159,
     160,   161,   162,   193,     0,   151,   152,   153,   154,   155,
     156,   157,   158,   159,   160,   161,   162,   151,   152,   153,
     154,   155,   156,   157,   158,   159,   160,   161,   162,   151,
     152,   153,   154,   155,   156,   157,   158,   159,   160,   161,
     151,   152,   153,   154,   155,   156,   157,   158,   159,   160,
     151,   152,   153,   154,   155,   156,   157,   158
  };

  const short
  WhileParser::yycheck_[] =
  {
      73,    20,    21,    22,    16,    16,   201,    45,    40,    41,
      42,     5,    50,   208,    14,    15,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    97,    20,    46,    47,    22,
      23,    24,    25,    45,    45,    14,    55,    56,    57,    58,
      59,    60,    61,    62,    63,    64,    89,    66,    91,    68,
       3,     4,    71,    44,   126,     3,     4,   129,   130,    14,
      15,    14,    15,     3,     4,    22,    14,   139,    25,     0,
     142,    13,   144,    21,    14,    15,    48,    45,    15,   151,
     152,   153,   154,   155,   156,   157,   158,   159,   160,   161,
     162,    14,   188,    46,    14,    48,    15,    45,     3,     4,
      48,     3,     4,   199,    18,    15,    46,    15,    48,    14,
      15,   207,    14,    14,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    15,   146,   147,   202,
       5,    15,    14,    19,    15,    14,   209,    15,    15,    15,
      46,    46,    15,    48,    46,    15,    48,    22,    23,    24,
      25,    26,    27,    28,    29,    15,    15,    15,    15,    34,
      35,    36,    37,    38,    39,    15,    14,    20,    20,    20,
       6,    46,     8,     9,    10,    11,    12,    16,    47,     5,
      47,    15,     6,    19,     8,     9,    10,    11,    12,    17,
      45,    18,    17,    15,     6,    19,     8,     9,    10,    11,
      12,    15,    45,    18,     7,    23,    19,    43,    18,    45,
      18,    47,     8,   205,    70,   210,    -1,    -1,    -1,    43,
      -1,    45,    -1,    47,    -1,    -1,    -1,    -1,    -1,    15,
      -1,    43,    -1,    45,    -1,    47,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    17,    -1,
      -1,    -1,    -1,    22,    23,    24,    25,    26,    27,    28,
      29,    30,    31,    32,    33,    20,    -1,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    20,
      -1,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    20,    -1,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    22,
      23,    24,    25,    26,    27,    28,    29,    30,    31,    32,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      22,    23,    24,    25,    26,    27,    28,    29
  };

  const unsigned char
  WhileParser::yystos_[] =
  {
       0,    14,    52,    53,    44,     0,    13,    55,    64,    65,
      48,    45,    56,    65,    15,    14,    14,    57,    54,    15,
      40,    41,    42,    55,    18,     3,     4,    14,    46,    48,
      59,    59,    59,    56,    66,     5,    22,    23,    24,    25,
      26,    27,    28,    29,    34,    35,    36,    37,    38,    39,
      46,    15,    15,    15,    67,    59,    59,    59,    59,    59,
      59,    59,    59,    59,    58,    59,    58,    59,    59,    14,
      14,    58,    19,    77,    59,    59,    59,    59,    59,    59,
      59,    59,    59,    15,    59,    15,    15,    59,    14,    62,
      63,    62,    15,     6,     8,     9,    10,    11,    12,    43,
      45,    47,    68,    69,    70,    71,    73,    74,    75,    76,
      80,    82,    15,    15,    15,    15,    15,    15,    15,    15,
      15,    15,    46,    15,    63,    15,    14,     3,     4,    14,
      21,    48,    81,    82,    20,    20,    81,    20,    47,    16,
      16,    45,     5,    20,     5,    47,    60,    61,    81,    81,
      81,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    72,    20,    16,    45,    81,    17,    81,
      81,    15,    59,    59,    15,    15,    81,    81,    81,    81,
      81,    81,    81,    81,    81,    81,    81,    81,    18,    17,
      17,    45,    20,    20,    15,    15,    78,    67,    45,    18,
      19,    67,    77,    19,    79,     7,    78,    18,    67,    77,
      19,    79
  };

  const unsigned char
  WhileParser::yyr1_[] =
  {
       0,    51,    53,    52,    54,    52,    55,    56,    56,    57,
      57,    57,    58,    58,    58,    59,    59,    59,    59,    59,
      59,    59,    59,    59,    59,    59,    59,    59,    59,    59,
      59,    59,    59,    60,    59,    61,    59,    62,    62,    63,
      64,    64,    66,    65,    67,    67,    67,    68,    68,    68,
      68,    68,    68,    68,    69,    69,    70,    70,    72,    71,
      73,    74,    75,    76,    77,    78,    79,    80,    80,    80,
      80,    81,    81,    81,    81,    81,    81,    81,    81,    81,
      81,    81,    81,    81,    81,    81,    81,    81,    81,    82,
      82
  };

  const unsigned char
  WhileParser::yyr2_[] =
  {
       0,     2,     0,     3,     0,     7,     1,     0,     2,     4,
       4,     4,     0,     1,     2,     1,     1,     4,     5,     5,
       5,     5,     1,     1,     5,     5,     5,     5,     5,     4,
       4,     4,     5,     0,     8,     0,     8,     1,     2,     4,
       1,     2,     0,     8,     0,     3,     4,     1,     1,     1,
       1,     1,     1,     1,     4,     4,    10,    17,     0,     6,
       2,     2,     3,     2,     0,     0,     0,     2,     3,     4,
       5,     3,     1,     1,     1,     1,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     2,     1,
       4
  };



  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const WhileParser::yytname_[] =
  {
  "\"EOF\"", "error", "$undefined", "\"true\"", "\"false\"", "\"=\"",
  "\"if\"", "\"else\"", "\"while\"", "\"break\"", "\"continue\"",
  "\"return\"", "\"skip\"", "\"func\"", "\"(\"", "\")\"", "\"[\"", "\"]\"",
  "\"{\"", "\"}\"", "\";\"", "\"!\"", "\"*\"", "\"+\"", "\"-\"", "\"mod\"",
  "\">\"", "\">=\"", "\"<\"", "\"<=\"", "\"==\"", "\"!=\"", "\"||\"",
  "\"&&\"", "\"and\"", "\"or\"", "\"not\"", "\"=>\"", "\"forall\"",
  "\"exists\"", "\"axiom\"", "\"lemma\"", "\"conjecture\"", "\"const\"",
  "\"set-traces\"", "\"program identifier\"", "\"smtlib identifier\"",
  "\"type identifier\"", "\"number\"", "DIV", "UMINUS", "$accept",
  "problem", "$@1", "$@2", "program", "smtlib_problemitem_list",
  "smtlib_problemitem", "smtlib_term_list", "smtlib_term", "$@3", "$@4",
  "smtlib_quantvar_list", "smtlib_quantvar", "function_list", "function",
  "$@5", "statement_list", "statement", "assignment_statement",
  "if_else_statement", "while_statement", "$@6", "break_statement",
  "continue_statement", "return_statement", "skip_statement",
  "active_vars_dummy", "push_dummy", "pop_dummy", "var_definition_head",
  "expr", "location", YY_NULLPTR
  };

#if YYDEBUG
  const unsigned short
  WhileParser::yyrline_[] =
  {
       0,   157,   157,   157,   166,   165,   183,   190,   191,   195,
     201,   207,   215,   216,   217,   221,   242,   246,   278,   290,
     302,   314,   326,   327,   328,   339,   351,   363,   375,   387,
     388,   389,   390,   392,   391,   402,   401,   414,   415,   419,
     453,   454,   459,   458,   480,   481,   487,   497,   498,   499,
     500,   501,   502,   503,   507,   528,   547,   561,   577,   576,
     588,   595,   601,   607,   611,   618,   625,   632,   647,   662,
     677,   695,   696,   697,   698,   699,   700,   701,   702,   703,
     705,   706,   707,   708,   709,   710,   712,   713,   714,   719,
     728
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
      *yycdebug_ << ' ' << i->state;
    *yycdebug_ << '\n';
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  WhileParser::yy_reduce_print_ (int yyrule)
  {
    unsigned yylno = yyrline_[yyrule];
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
#line 2564 "../src/parser/WhileParser.cpp"

#line 739 "WhileParser.yy"

void parser::WhileParser::error(const location_type& l,
                              const std::string& m)
{
  std::cout << "Error while parsing location " << l << ":\n" << m << std::endl;
  parsing_context.errorFlag = true;
  exit(1);
}
