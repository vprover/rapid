// A Bison parser, made by GNU Bison 3.5.1.

// Skeleton interface for Bison LALR(1) parsers in C++

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


/**
 ** \file ../src/parser/WhileParser.hpp
 ** Define the parser::parser class.
 */

// C++ LALR(1) parser skeleton written by Akim Demaille.

// Undocumented macros, especially those whose name start with YY_,
// are private implementation details.  Do not rely on them.

#ifndef YY_YY_SRC_PARSER_WHILEPARSER_HPP_INCLUDED
# define YY_YY_SRC_PARSER_WHILEPARSER_HPP_INCLUDED
// "%code requires" blocks.
#line 10 "WhileParser.yy"

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

#line 76 "../src/parser/WhileParser.hpp"

# include <cassert>
# include <cstdlib> // std::abort
# include <iostream>
# include <stdexcept>
# include <string>
# include <vector>

#if defined __cplusplus
# define YY_CPLUSPLUS __cplusplus
#else
# define YY_CPLUSPLUS 199711L
#endif

// Support move semantics when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_MOVE           std::move
# define YY_MOVE_OR_COPY   move
# define YY_MOVE_REF(Type) Type&&
# define YY_RVREF(Type)    Type&&
# define YY_COPY(Type)     Type
#else
# define YY_MOVE
# define YY_MOVE_OR_COPY   copy
# define YY_MOVE_REF(Type) Type&
# define YY_RVREF(Type)    const Type&
# define YY_COPY(Type)     const Type&
#endif

// Support noexcept when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_NOEXCEPT noexcept
# define YY_NOTHROW
#else
# define YY_NOEXCEPT
# define YY_NOTHROW throw ()
#endif

// Support constexpr when possible.
#if 201703 <= YY_CPLUSPLUS
# define YY_CONSTEXPR constexpr
#else
# define YY_CONSTEXPR
#endif

#include <typeinfo>
#ifndef YY_ASSERT
# include <cassert>
# define YY_ASSERT assert
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && ! defined __ICC && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                            \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif

#line 4 "WhileParser.yy"
namespace parser {
#line 211 "../src/parser/WhileParser.hpp"




  /// A Bison parser.
  class WhileParser
  {
  public:
#ifndef YYSTYPE
  /// A buffer to store and retrieve objects.
  ///
  /// Sort of a variant, but does not keep track of the nature
  /// of the stored data, since that knowledge is available
  /// via the current parser state.
  class semantic_type
  {
  public:
    /// Type of *this.
    typedef semantic_type self_type;

    /// Empty construction.
    semantic_type () YY_NOEXCEPT
      : yybuffer_ ()
      , yytypeid_ (YY_NULLPTR)
    {}

    /// Construct and fill.
    template <typename T>
    semantic_type (YY_RVREF (T) t)
      : yytypeid_ (&typeid (T))
    {
      YY_ASSERT (sizeof (T) <= size);
      new (yyas_<T> ()) T (YY_MOVE (t));
    }

    /// Destruction, allowed only if empty.
    ~semantic_type () YY_NOEXCEPT
    {
      YY_ASSERT (!yytypeid_);
    }

# if 201103L <= YY_CPLUSPLUS
    /// Instantiate a \a T in here from \a t.
    template <typename T, typename... U>
    T&
    emplace (U&&... u)
    {
      YY_ASSERT (!yytypeid_);
      YY_ASSERT (sizeof (T) <= size);
      yytypeid_ = & typeid (T);
      return *new (yyas_<T> ()) T (std::forward <U>(u)...);
    }
# else
    /// Instantiate an empty \a T in here.
    template <typename T>
    T&
    emplace ()
    {
      YY_ASSERT (!yytypeid_);
      YY_ASSERT (sizeof (T) <= size);
      yytypeid_ = & typeid (T);
      return *new (yyas_<T> ()) T ();
    }

    /// Instantiate a \a T in here from \a t.
    template <typename T>
    T&
    emplace (const T& t)
    {
      YY_ASSERT (!yytypeid_);
      YY_ASSERT (sizeof (T) <= size);
      yytypeid_ = & typeid (T);
      return *new (yyas_<T> ()) T (t);
    }
# endif

    /// Instantiate an empty \a T in here.
    /// Obsolete, use emplace.
    template <typename T>
    T&
    build ()
    {
      return emplace<T> ();
    }

    /// Instantiate a \a T in here from \a t.
    /// Obsolete, use emplace.
    template <typename T>
    T&
    build (const T& t)
    {
      return emplace<T> (t);
    }

    /// Accessor to a built \a T.
    template <typename T>
    T&
    as () YY_NOEXCEPT
    {
      YY_ASSERT (yytypeid_);
      YY_ASSERT (*yytypeid_ == typeid (T));
      YY_ASSERT (sizeof (T) <= size);
      return *yyas_<T> ();
    }

    /// Const accessor to a built \a T (for %printer).
    template <typename T>
    const T&
    as () const YY_NOEXCEPT
    {
      YY_ASSERT (yytypeid_);
      YY_ASSERT (*yytypeid_ == typeid (T));
      YY_ASSERT (sizeof (T) <= size);
      return *yyas_<T> ();
    }

    /// Swap the content with \a that, of same type.
    ///
    /// Both variants must be built beforehand, because swapping the actual
    /// data requires reading it (with as()), and this is not possible on
    /// unconstructed variants: it would require some dynamic testing, which
    /// should not be the variant's responsibility.
    /// Swapping between built and (possibly) non-built is done with
    /// self_type::move ().
    template <typename T>
    void
    swap (self_type& that) YY_NOEXCEPT
    {
      YY_ASSERT (yytypeid_);
      YY_ASSERT (*yytypeid_ == *that.yytypeid_);
      std::swap (as<T> (), that.as<T> ());
    }

    /// Move the content of \a that to this.
    ///
    /// Destroys \a that.
    template <typename T>
    void
    move (self_type& that)
    {
# if 201103L <= YY_CPLUSPLUS
      emplace<T> (std::move (that.as<T> ()));
# else
      emplace<T> ();
      swap<T> (that);
# endif
      that.destroy<T> ();
    }

# if 201103L <= YY_CPLUSPLUS
    /// Move the content of \a that to this.
    template <typename T>
    void
    move (self_type&& that)
    {
      emplace<T> (std::move (that.as<T> ()));
      that.destroy<T> ();
    }
#endif

    /// Copy the content of \a that to this.
    template <typename T>
    void
    copy (const self_type& that)
    {
      emplace<T> (that.as<T> ());
    }

    /// Destroy the stored \a T.
    template <typename T>
    void
    destroy ()
    {
      as<T> ().~T ();
      yytypeid_ = YY_NULLPTR;
    }

  private:
    /// Prohibit blind copies.
    self_type& operator= (const self_type&);
    semantic_type (const self_type&);

    /// Accessor to raw memory as \a T.
    template <typename T>
    T*
    yyas_ () YY_NOEXCEPT
    {
      void *yyp = yybuffer_.yyraw;
      return static_cast<T*> (yyp);
     }

    /// Const accessor to raw memory as \a T.
    template <typename T>
    const T*
    yyas_ () const YY_NOEXCEPT
    {
      const void *yyp = yybuffer_.yyraw;
      return static_cast<const T*> (yyp);
     }

    /// An auxiliary type to compute the largest semantic type.
    union union_type
    {
      // smtlib_formula
      char dummy1[sizeof ( std::shared_ptr<const logic::Formula> )];

      // smtlib_problemitem
      char dummy2[sizeof ( std::shared_ptr<const logic::ProblemItem> )];

      // smtlib_quantvar
      char dummy3[sizeof ( std::shared_ptr<const logic::Symbol> )];

      // smtlib_term
      char dummy4[sizeof ( std::shared_ptr<const logic::Term> )];

      // formula
      char dummy5[sizeof ( std::shared_ptr<const program::BoolExpression> )];

      // function
      char dummy6[sizeof ( std::shared_ptr<const program::Function> )];

      // if_else_statement
      char dummy7[sizeof ( std::shared_ptr<const program::IfElse> )];

      // assignment_statement
      char dummy8[sizeof ( std::shared_ptr<const program::IntAssignment> )];

      // expr
      // location
      char dummy9[sizeof ( std::shared_ptr<const program::IntExpression> )];

      // program
      char dummy10[sizeof ( std::shared_ptr<const program::Program> )];

      // skip_statement
      char dummy11[sizeof ( std::shared_ptr<const program::SkipStatement> )];

      // statement
      char dummy12[sizeof ( std::shared_ptr<const program::Statement> )];

      // var_definition_head
      char dummy13[sizeof ( std::shared_ptr<const program::Variable> )];

      // while_statement
      char dummy14[sizeof ( std::shared_ptr<const program::WhileStatement> )];

      // function_list
      char dummy15[sizeof ( std::vector< std::shared_ptr<const program::Function>> )];

      // smtlib_formula_list
      char dummy16[sizeof ( std::vector<std::shared_ptr<const logic::Formula>> )];

      // smtlib_problemitem_list
      char dummy17[sizeof ( std::vector<std::shared_ptr<const logic::ProblemItem> > )];

      // smtlib_quantvar_list
      char dummy18[sizeof ( std::vector<std::shared_ptr<const logic::Symbol>> )];

      // smtlib_term_list
      char dummy19[sizeof ( std::vector<std::shared_ptr<const logic::Term>> )];

      // statement_list
      char dummy20[sizeof ( std::vector<std::shared_ptr<const program::Statement>> )];

      // active_vars_dummy
      char dummy21[sizeof ( std::vector<std::shared_ptr<const program::Variable>> )];

      // "number"
      char dummy22[sizeof (int)];

      // "program identifier"
      // "smtlib identifier"
      // "type identifier"
      char dummy23[sizeof (std::string)];
    };

    /// The size of the largest semantic type.
    enum { size = sizeof (union_type) };

    /// A buffer to store semantic values.
    union
    {
      /// Strongest alignment constraints.
      long double yyalign_me;
      /// A buffer large enough to store any of the semantic values.
      char yyraw[size];
    } yybuffer_;

    /// Whether the content is built: if defined, the name of the stored type.
    const std::type_info *yytypeid_;
  };

#else
    typedef YYSTYPE semantic_type;
#endif
    /// Symbol locations.
    typedef Location location_type;

    /// Syntax errors thrown from user actions.
    struct syntax_error : std::runtime_error
    {
      syntax_error (const location_type& l, const std::string& m)
        : std::runtime_error (m)
        , location (l)
      {}

      syntax_error (const syntax_error& s)
        : std::runtime_error (s.what ())
        , location (s.location)
      {}

      ~syntax_error () YY_NOEXCEPT YY_NOTHROW;

      location_type location;
    };

    /// Tokens.
    struct token
    {
      enum yytokentype
      {
        TOK_END = 0,
        TOK_TRUE = 258,
        TOK_FALSE = 259,
        TOK_ASSIGN = 260,
        TOK_IF = 261,
        TOK_ELSE = 262,
        TOK_WHILE = 263,
        TOK_SKIP = 264,
        TOK_FUNC = 265,
        TOK_LPAR = 266,
        TOK_RPAR = 267,
        TOK_LBRA = 268,
        TOK_RBRA = 269,
        TOK_LCUR = 270,
        TOK_RCUR = 271,
        TOK_SCOL = 272,
        TOK_NOT = 273,
        TOK_MUL = 274,
        TOK_PLUS = 275,
        TOK_MINUS = 276,
        TOK_MOD = 277,
        TOK_GT = 278,
        TOK_GE = 279,
        TOK_LT = 280,
        TOK_LE = 281,
        TOK_EQ = 282,
        TOK_NEQ = 283,
        TOK_OR = 284,
        TOK_AND = 285,
        TOK_ANDSMTLIB = 286,
        TOK_ORSMTLIB = 287,
        TOK_NOTSMTLIB = 288,
        TOK_IMPSMTLIB = 289,
        TOK_FORALLSMTLIB = 290,
        TOK_EXISTSSMTLIB = 291,
        TOK_AXIOM = 292,
        TOK_LEMMA = 293,
        TOK_CONJECTURE = 294,
        TOK_CONST = 295,
        TOK_SETTRACES = 296,
        TOK_PROGRAM_ID = 297,
        TOK_SMTLIB_ID = 298,
        TOK_TYPE = 299,
        TOK_INTEGER = 300,
        TOK_DIV = 301,
        TOK_UMINUS = 302
      };
    };

    /// (External) token type, as returned by yylex.
    typedef token::yytokentype token_type;

    /// Symbol type: an internal symbol number.
    typedef int symbol_number_type;

    /// The symbol type number to denote an empty symbol.
    enum { empty_symbol = -2 };

    /// Internal symbol number for tokens (subsumed by symbol_number_type).
    typedef signed char token_number_type;

    /// A complete symbol.
    ///
    /// Expects its Base type to provide access to the symbol type
    /// via type_get ().
    ///
    /// Provide access to semantic value and location.
    template <typename Base>
    struct basic_symbol : Base
    {
      /// Alias to Base.
      typedef Base super_type;

      /// Default constructor.
      basic_symbol ()
        : value ()
        , location ()
      {}

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      basic_symbol (basic_symbol&& that);
#endif

      /// Copy constructor.
      basic_symbol (const basic_symbol& that);

      /// Constructor for valueless symbols, and symbols from each type.
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, location_type&& l)
        : Base (t)
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const location_type& l)
        : Base (t)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const logic::Formula> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const logic::Formula> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const logic::ProblemItem> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const logic::ProblemItem> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const logic::Symbol> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const logic::Symbol> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const logic::Term> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const logic::Term> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::BoolExpression> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::BoolExpression> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::Function> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::Function> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::IfElse> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::IfElse> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::IntAssignment> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::IntAssignment> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::IntExpression> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::IntExpression> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::Program> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::Program> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::SkipStatement> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::SkipStatement> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::Statement> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::Statement> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::Variable> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::Variable> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::shared_ptr<const program::WhileStatement> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::shared_ptr<const program::WhileStatement> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector< std::shared_ptr<const program::Function>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector< std::shared_ptr<const program::Function>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const logic::Formula>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const logic::Formula>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const logic::ProblemItem> > && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const logic::ProblemItem> > & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const logic::Symbol>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const logic::Symbol>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const logic::Term>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const logic::Term>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const program::Statement>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const program::Statement>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t,  std::vector<std::shared_ptr<const program::Variable>> && v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const  std::vector<std::shared_ptr<const program::Variable>> & v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, int&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const int& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif
#if 201103L <= YY_CPLUSPLUS
      basic_symbol (typename Base::kind_type t, std::string&& v, location_type&& l)
        : Base (t)
        , value (std::move (v))
        , location (std::move (l))
      {}
#else
      basic_symbol (typename Base::kind_type t, const std::string& v, const location_type& l)
        : Base (t)
        , value (v)
        , location (l)
      {}
#endif

      /// Destroy the symbol.
      ~basic_symbol ()
      {
        clear ();
      }

      /// Destroy contents, and record that is empty.
      void clear ()
      {
        // User destructor.
        symbol_number_type yytype = this->type_get ();
        basic_symbol<Base>& yysym = *this;
        (void) yysym;
        switch (yytype)
        {
       default:
          break;
        }

        // Type destructor.
switch (yytype)
    {
      case 56: // smtlib_formula
        value.template destroy<  std::shared_ptr<const logic::Formula>  > ();
        break;

      case 54: // smtlib_problemitem
        value.template destroy<  std::shared_ptr<const logic::ProblemItem>  > ();
        break;

      case 60: // smtlib_quantvar
        value.template destroy<  std::shared_ptr<const logic::Symbol>  > ();
        break;

      case 62: // smtlib_term
        value.template destroy<  std::shared_ptr<const logic::Term>  > ();
        break;

      case 78: // formula
        value.template destroy<  std::shared_ptr<const program::BoolExpression>  > ();
        break;

      case 64: // function
        value.template destroy<  std::shared_ptr<const program::Function>  > ();
        break;

      case 69: // if_else_statement
        value.template destroy<  std::shared_ptr<const program::IfElse>  > ();
        break;

      case 68: // assignment_statement
        value.template destroy<  std::shared_ptr<const program::IntAssignment>  > ();
        break;

      case 79: // expr
      case 80: // location
        value.template destroy<  std::shared_ptr<const program::IntExpression>  > ();
        break;

      case 52: // program
        value.template destroy<  std::shared_ptr<const program::Program>  > ();
        break;

      case 75: // skip_statement
        value.template destroy<  std::shared_ptr<const program::SkipStatement>  > ();
        break;

      case 67: // statement
        value.template destroy<  std::shared_ptr<const program::Statement>  > ();
        break;

      case 77: // var_definition_head
        value.template destroy<  std::shared_ptr<const program::Variable>  > ();
        break;

      case 73: // while_statement
        value.template destroy<  std::shared_ptr<const program::WhileStatement>  > ();
        break;

      case 63: // function_list
        value.template destroy<  std::vector< std::shared_ptr<const program::Function>>  > ();
        break;

      case 55: // smtlib_formula_list
        value.template destroy<  std::vector<std::shared_ptr<const logic::Formula>>  > ();
        break;

      case 53: // smtlib_problemitem_list
        value.template destroy<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > ();
        break;

      case 59: // smtlib_quantvar_list
        value.template destroy<  std::vector<std::shared_ptr<const logic::Symbol>>  > ();
        break;

      case 61: // smtlib_term_list
        value.template destroy<  std::vector<std::shared_ptr<const logic::Term>>  > ();
        break;

      case 66: // statement_list
        value.template destroy<  std::vector<std::shared_ptr<const program::Statement>>  > ();
        break;

      case 76: // active_vars_dummy
        value.template destroy<  std::vector<std::shared_ptr<const program::Variable>>  > ();
        break;

      case 45: // "number"
        value.template destroy< int > ();
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.template destroy< std::string > ();
        break;

      default:
        break;
    }

        Base::clear ();
      }

      /// Whether empty.
      bool empty () const YY_NOEXCEPT;

      /// Destructive move, \a s is emptied into this.
      void move (basic_symbol& s);

      /// The semantic value.
      semantic_type value;

      /// The location.
      location_type location;

    private:
#if YY_CPLUSPLUS < 201103L
      /// Assignment operator.
      basic_symbol& operator= (const basic_symbol& that);
#endif
    };

    /// Type access provider for token (enum) based symbols.
    struct by_type
    {
      /// Default constructor.
      by_type ();

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      by_type (by_type&& that);
#endif

      /// Copy constructor.
      by_type (const by_type& that);

      /// The symbol type as needed by the constructor.
      typedef token_type kind_type;

      /// Constructor from (external) token numbers.
      by_type (kind_type t);

      /// Record that this symbol is empty.
      void clear ();

      /// Steal the symbol type from \a that.
      void move (by_type& that);

      /// The (internal) type number (corresponding to \a type).
      /// \a empty when empty.
      symbol_number_type type_get () const YY_NOEXCEPT;

      /// The symbol type.
      /// \a empty_symbol when empty.
      /// An int, not token_number_type, to be able to store empty_symbol.
      int type;
    };

    /// "External" symbols: returned by the scanner.
    struct symbol_type : basic_symbol<by_type>
    {
      /// Superclass.
      typedef basic_symbol<by_type> super_type;

      /// Empty symbol.
      symbol_type () {}

      /// Constructor for valueless symbols, and symbols from each type.
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, location_type l)
        : super_type(token_type (tok), std::move (l))
      {
        YY_ASSERT (tok == token::TOK_END || tok == token::TOK_TRUE || tok == token::TOK_FALSE || tok == token::TOK_ASSIGN || tok == token::TOK_IF || tok == token::TOK_ELSE || tok == token::TOK_WHILE || tok == token::TOK_SKIP || tok == token::TOK_FUNC || tok == token::TOK_LPAR || tok == token::TOK_RPAR || tok == token::TOK_LBRA || tok == token::TOK_RBRA || tok == token::TOK_LCUR || tok == token::TOK_RCUR || tok == token::TOK_SCOL || tok == token::TOK_NOT || tok == token::TOK_MUL || tok == token::TOK_PLUS || tok == token::TOK_MINUS || tok == token::TOK_MOD || tok == token::TOK_GT || tok == token::TOK_GE || tok == token::TOK_LT || tok == token::TOK_LE || tok == token::TOK_EQ || tok == token::TOK_NEQ || tok == token::TOK_OR || tok == token::TOK_AND || tok == token::TOK_ANDSMTLIB || tok == token::TOK_ORSMTLIB || tok == token::TOK_NOTSMTLIB || tok == token::TOK_IMPSMTLIB || tok == token::TOK_FORALLSMTLIB || tok == token::TOK_EXISTSSMTLIB || tok == token::TOK_AXIOM || tok == token::TOK_LEMMA || tok == token::TOK_CONJECTURE || tok == token::TOK_CONST || tok == token::TOK_SETTRACES || tok == token::TOK_DIV || tok == token::TOK_UMINUS);
      }
#else
      symbol_type (int tok, const location_type& l)
        : super_type(token_type (tok), l)
      {
        YY_ASSERT (tok == token::TOK_END || tok == token::TOK_TRUE || tok == token::TOK_FALSE || tok == token::TOK_ASSIGN || tok == token::TOK_IF || tok == token::TOK_ELSE || tok == token::TOK_WHILE || tok == token::TOK_SKIP || tok == token::TOK_FUNC || tok == token::TOK_LPAR || tok == token::TOK_RPAR || tok == token::TOK_LBRA || tok == token::TOK_RBRA || tok == token::TOK_LCUR || tok == token::TOK_RCUR || tok == token::TOK_SCOL || tok == token::TOK_NOT || tok == token::TOK_MUL || tok == token::TOK_PLUS || tok == token::TOK_MINUS || tok == token::TOK_MOD || tok == token::TOK_GT || tok == token::TOK_GE || tok == token::TOK_LT || tok == token::TOK_LE || tok == token::TOK_EQ || tok == token::TOK_NEQ || tok == token::TOK_OR || tok == token::TOK_AND || tok == token::TOK_ANDSMTLIB || tok == token::TOK_ORSMTLIB || tok == token::TOK_NOTSMTLIB || tok == token::TOK_IMPSMTLIB || tok == token::TOK_FORALLSMTLIB || tok == token::TOK_EXISTSSMTLIB || tok == token::TOK_AXIOM || tok == token::TOK_LEMMA || tok == token::TOK_CONJECTURE || tok == token::TOK_CONST || tok == token::TOK_SETTRACES || tok == token::TOK_DIV || tok == token::TOK_UMINUS);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, int v, location_type l)
        : super_type(token_type (tok), std::move (v), std::move (l))
      {
        YY_ASSERT (tok == token::TOK_INTEGER);
      }
#else
      symbol_type (int tok, const int& v, const location_type& l)
        : super_type(token_type (tok), v, l)
      {
        YY_ASSERT (tok == token::TOK_INTEGER);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      symbol_type (int tok, std::string v, location_type l)
        : super_type(token_type (tok), std::move (v), std::move (l))
      {
        YY_ASSERT (tok == token::TOK_PROGRAM_ID || tok == token::TOK_SMTLIB_ID || tok == token::TOK_TYPE);
      }
#else
      symbol_type (int tok, const std::string& v, const location_type& l)
        : super_type(token_type (tok), v, l)
      {
        YY_ASSERT (tok == token::TOK_PROGRAM_ID || tok == token::TOK_SMTLIB_ID || tok == token::TOK_TYPE);
      }
#endif
    };

    /// Build a parser object.
    WhileParser (parser::WhileParsingContext &context_yyarg);
    virtual ~WhileParser ();

    /// Parse.  An alias for parse ().
    /// \returns  0 iff parsing succeeded.
    int operator() ();

    /// Parse.
    /// \returns  0 iff parsing succeeded.
    virtual int parse ();

#if YYDEBUG
    /// The current debugging stream.
    std::ostream& debug_stream () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging stream.
    void set_debug_stream (std::ostream &);

    /// Type for debugging levels.
    typedef int debug_level_type;
    /// The current debugging level.
    debug_level_type debug_level () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging level.
    void set_debug_level (debug_level_type l);
#endif

    /// Report a syntax error.
    /// \param loc    where the syntax error is found.
    /// \param msg    a description of the syntax error.
    virtual void error (const location_type& loc, const std::string& msg);

    /// Report a syntax error.
    void error (const syntax_error& err);

    // Implementation of make_symbol for each symbol type.
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_END (location_type l)
      {
        return symbol_type (token::TOK_END, std::move (l));
      }
#else
      static
      symbol_type
      make_END (const location_type& l)
      {
        return symbol_type (token::TOK_END, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_TRUE (location_type l)
      {
        return symbol_type (token::TOK_TRUE, std::move (l));
      }
#else
      static
      symbol_type
      make_TRUE (const location_type& l)
      {
        return symbol_type (token::TOK_TRUE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_FALSE (location_type l)
      {
        return symbol_type (token::TOK_FALSE, std::move (l));
      }
#else
      static
      symbol_type
      make_FALSE (const location_type& l)
      {
        return symbol_type (token::TOK_FALSE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_ASSIGN (location_type l)
      {
        return symbol_type (token::TOK_ASSIGN, std::move (l));
      }
#else
      static
      symbol_type
      make_ASSIGN (const location_type& l)
      {
        return symbol_type (token::TOK_ASSIGN, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_IF (location_type l)
      {
        return symbol_type (token::TOK_IF, std::move (l));
      }
#else
      static
      symbol_type
      make_IF (const location_type& l)
      {
        return symbol_type (token::TOK_IF, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_ELSE (location_type l)
      {
        return symbol_type (token::TOK_ELSE, std::move (l));
      }
#else
      static
      symbol_type
      make_ELSE (const location_type& l)
      {
        return symbol_type (token::TOK_ELSE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_WHILE (location_type l)
      {
        return symbol_type (token::TOK_WHILE, std::move (l));
      }
#else
      static
      symbol_type
      make_WHILE (const location_type& l)
      {
        return symbol_type (token::TOK_WHILE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_SKIP (location_type l)
      {
        return symbol_type (token::TOK_SKIP, std::move (l));
      }
#else
      static
      symbol_type
      make_SKIP (const location_type& l)
      {
        return symbol_type (token::TOK_SKIP, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_FUNC (location_type l)
      {
        return symbol_type (token::TOK_FUNC, std::move (l));
      }
#else
      static
      symbol_type
      make_FUNC (const location_type& l)
      {
        return symbol_type (token::TOK_FUNC, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LPAR (location_type l)
      {
        return symbol_type (token::TOK_LPAR, std::move (l));
      }
#else
      static
      symbol_type
      make_LPAR (const location_type& l)
      {
        return symbol_type (token::TOK_LPAR, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_RPAR (location_type l)
      {
        return symbol_type (token::TOK_RPAR, std::move (l));
      }
#else
      static
      symbol_type
      make_RPAR (const location_type& l)
      {
        return symbol_type (token::TOK_RPAR, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LBRA (location_type l)
      {
        return symbol_type (token::TOK_LBRA, std::move (l));
      }
#else
      static
      symbol_type
      make_LBRA (const location_type& l)
      {
        return symbol_type (token::TOK_LBRA, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_RBRA (location_type l)
      {
        return symbol_type (token::TOK_RBRA, std::move (l));
      }
#else
      static
      symbol_type
      make_RBRA (const location_type& l)
      {
        return symbol_type (token::TOK_RBRA, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LCUR (location_type l)
      {
        return symbol_type (token::TOK_LCUR, std::move (l));
      }
#else
      static
      symbol_type
      make_LCUR (const location_type& l)
      {
        return symbol_type (token::TOK_LCUR, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_RCUR (location_type l)
      {
        return symbol_type (token::TOK_RCUR, std::move (l));
      }
#else
      static
      symbol_type
      make_RCUR (const location_type& l)
      {
        return symbol_type (token::TOK_RCUR, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_SCOL (location_type l)
      {
        return symbol_type (token::TOK_SCOL, std::move (l));
      }
#else
      static
      symbol_type
      make_SCOL (const location_type& l)
      {
        return symbol_type (token::TOK_SCOL, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_NOT (location_type l)
      {
        return symbol_type (token::TOK_NOT, std::move (l));
      }
#else
      static
      symbol_type
      make_NOT (const location_type& l)
      {
        return symbol_type (token::TOK_NOT, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MUL (location_type l)
      {
        return symbol_type (token::TOK_MUL, std::move (l));
      }
#else
      static
      symbol_type
      make_MUL (const location_type& l)
      {
        return symbol_type (token::TOK_MUL, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_PLUS (location_type l)
      {
        return symbol_type (token::TOK_PLUS, std::move (l));
      }
#else
      static
      symbol_type
      make_PLUS (const location_type& l)
      {
        return symbol_type (token::TOK_PLUS, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MINUS (location_type l)
      {
        return symbol_type (token::TOK_MINUS, std::move (l));
      }
#else
      static
      symbol_type
      make_MINUS (const location_type& l)
      {
        return symbol_type (token::TOK_MINUS, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_MOD (location_type l)
      {
        return symbol_type (token::TOK_MOD, std::move (l));
      }
#else
      static
      symbol_type
      make_MOD (const location_type& l)
      {
        return symbol_type (token::TOK_MOD, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_GT (location_type l)
      {
        return symbol_type (token::TOK_GT, std::move (l));
      }
#else
      static
      symbol_type
      make_GT (const location_type& l)
      {
        return symbol_type (token::TOK_GT, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_GE (location_type l)
      {
        return symbol_type (token::TOK_GE, std::move (l));
      }
#else
      static
      symbol_type
      make_GE (const location_type& l)
      {
        return symbol_type (token::TOK_GE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LT (location_type l)
      {
        return symbol_type (token::TOK_LT, std::move (l));
      }
#else
      static
      symbol_type
      make_LT (const location_type& l)
      {
        return symbol_type (token::TOK_LT, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LE (location_type l)
      {
        return symbol_type (token::TOK_LE, std::move (l));
      }
#else
      static
      symbol_type
      make_LE (const location_type& l)
      {
        return symbol_type (token::TOK_LE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_EQ (location_type l)
      {
        return symbol_type (token::TOK_EQ, std::move (l));
      }
#else
      static
      symbol_type
      make_EQ (const location_type& l)
      {
        return symbol_type (token::TOK_EQ, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_NEQ (location_type l)
      {
        return symbol_type (token::TOK_NEQ, std::move (l));
      }
#else
      static
      symbol_type
      make_NEQ (const location_type& l)
      {
        return symbol_type (token::TOK_NEQ, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_OR (location_type l)
      {
        return symbol_type (token::TOK_OR, std::move (l));
      }
#else
      static
      symbol_type
      make_OR (const location_type& l)
      {
        return symbol_type (token::TOK_OR, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_AND (location_type l)
      {
        return symbol_type (token::TOK_AND, std::move (l));
      }
#else
      static
      symbol_type
      make_AND (const location_type& l)
      {
        return symbol_type (token::TOK_AND, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_ANDSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_ANDSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_ANDSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_ANDSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_ORSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_ORSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_ORSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_ORSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_NOTSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_NOTSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_NOTSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_NOTSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_IMPSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_IMPSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_IMPSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_IMPSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_FORALLSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_FORALLSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_FORALLSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_FORALLSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_EXISTSSMTLIB (location_type l)
      {
        return symbol_type (token::TOK_EXISTSSMTLIB, std::move (l));
      }
#else
      static
      symbol_type
      make_EXISTSSMTLIB (const location_type& l)
      {
        return symbol_type (token::TOK_EXISTSSMTLIB, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_AXIOM (location_type l)
      {
        return symbol_type (token::TOK_AXIOM, std::move (l));
      }
#else
      static
      symbol_type
      make_AXIOM (const location_type& l)
      {
        return symbol_type (token::TOK_AXIOM, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_LEMMA (location_type l)
      {
        return symbol_type (token::TOK_LEMMA, std::move (l));
      }
#else
      static
      symbol_type
      make_LEMMA (const location_type& l)
      {
        return symbol_type (token::TOK_LEMMA, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_CONJECTURE (location_type l)
      {
        return symbol_type (token::TOK_CONJECTURE, std::move (l));
      }
#else
      static
      symbol_type
      make_CONJECTURE (const location_type& l)
      {
        return symbol_type (token::TOK_CONJECTURE, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_CONST (location_type l)
      {
        return symbol_type (token::TOK_CONST, std::move (l));
      }
#else
      static
      symbol_type
      make_CONST (const location_type& l)
      {
        return symbol_type (token::TOK_CONST, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_SETTRACES (location_type l)
      {
        return symbol_type (token::TOK_SETTRACES, std::move (l));
      }
#else
      static
      symbol_type
      make_SETTRACES (const location_type& l)
      {
        return symbol_type (token::TOK_SETTRACES, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_PROGRAM_ID (std::string v, location_type l)
      {
        return symbol_type (token::TOK_PROGRAM_ID, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_PROGRAM_ID (const std::string& v, const location_type& l)
      {
        return symbol_type (token::TOK_PROGRAM_ID, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_SMTLIB_ID (std::string v, location_type l)
      {
        return symbol_type (token::TOK_SMTLIB_ID, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_SMTLIB_ID (const std::string& v, const location_type& l)
      {
        return symbol_type (token::TOK_SMTLIB_ID, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_TYPE (std::string v, location_type l)
      {
        return symbol_type (token::TOK_TYPE, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_TYPE (const std::string& v, const location_type& l)
      {
        return symbol_type (token::TOK_TYPE, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_INTEGER (int v, location_type l)
      {
        return symbol_type (token::TOK_INTEGER, std::move (v), std::move (l));
      }
#else
      static
      symbol_type
      make_INTEGER (const int& v, const location_type& l)
      {
        return symbol_type (token::TOK_INTEGER, v, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_DIV (location_type l)
      {
        return symbol_type (token::TOK_DIV, std::move (l));
      }
#else
      static
      symbol_type
      make_DIV (const location_type& l)
      {
        return symbol_type (token::TOK_DIV, l);
      }
#endif
#if 201103L <= YY_CPLUSPLUS
      static
      symbol_type
      make_UMINUS (location_type l)
      {
        return symbol_type (token::TOK_UMINUS, std::move (l));
      }
#else
      static
      symbol_type
      make_UMINUS (const location_type& l)
      {
        return symbol_type (token::TOK_UMINUS, l);
      }
#endif


  private:
    /// This class is not copyable.
    WhileParser (const WhileParser&);
    WhileParser& operator= (const WhileParser&);

    /// Stored state numbers (used for stacks).
    typedef unsigned char state_type;

    /// Generate an error message.
    /// \param yystate   the state where the error occurred.
    /// \param yyla      the lookahead token.
    virtual std::string yysyntax_error_ (state_type yystate,
                                         const symbol_type& yyla) const;

    /// Compute post-reduction state.
    /// \param yystate   the current state
    /// \param yysym     the nonterminal to push on the stack
    static state_type yy_lr_goto_state_ (state_type yystate, int yysym);

    /// Whether the given \c yypact_ value indicates a defaulted state.
    /// \param yyvalue   the value to check
    static bool yy_pact_value_is_default_ (int yyvalue);

    /// Whether the given \c yytable_ value indicates a syntax error.
    /// \param yyvalue   the value to check
    static bool yy_table_value_is_error_ (int yyvalue);

    static const short yypact_ninf_;
    static const signed char yytable_ninf_;

    /// Convert a scanner token number \a t to a symbol number.
    /// In theory \a t should be a token_type, but character literals
    /// are valid, yet not members of the token_type enum.
    static token_number_type yytranslate_ (int t);

    // Tables.
    // YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
    // STATE-NUM.
    static const short yypact_[];

    // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
    // Performed when YYTABLE does not specify something else to do.  Zero
    // means the default is an error.
    static const signed char yydefact_[];

    // YYPGOTO[NTERM-NUM].
    static const short yypgoto_[];

    // YYDEFGOTO[NTERM-NUM].
    static const short yydefgoto_[];

    // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
    // positive, shift that token.  If negative, reduce the rule whose
    // number is the opposite.  If YYTABLE_NINF, syntax error.
    static const unsigned char yytable_[];

    static const short yycheck_[];

    // YYSTOS[STATE-NUM] -- The (internal number of the) accessing
    // symbol of state STATE-NUM.
    static const signed char yystos_[];

    // YYR1[YYN] -- Symbol number of symbol that rule YYN derives.
    static const signed char yyr1_[];

    // YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.
    static const signed char yyr2_[];


    /// Convert the symbol name \a n to a form suitable for a diagnostic.
    static std::string yytnamerr_ (const char *n);


    /// For a symbol, its name in clear.
    static const char* const yytname_[];
#if YYDEBUG
    // YYRLINE[YYN] -- Source line where rule number YYN was defined.
    static const short yyrline_[];
    /// Report on the debug stream that the rule \a r is going to be reduced.
    virtual void yy_reduce_print_ (int r);
    /// Print the state stack on the debug stream.
    virtual void yystack_print_ ();

    /// Debugging level.
    int yydebug_;
    /// Debug stream.
    std::ostream* yycdebug_;

    /// \brief Display a symbol type, value and location.
    /// \param yyo    The output stream.
    /// \param yysym  The symbol.
    template <typename Base>
    void yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const;
#endif

    /// \brief Reclaim the memory associated to a symbol.
    /// \param yymsg     Why this token is reclaimed.
    ///                  If null, print nothing.
    /// \param yysym     The symbol.
    template <typename Base>
    void yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const;

  private:
    /// Type access provider for state based symbols.
    struct by_state
    {
      /// Default constructor.
      by_state () YY_NOEXCEPT;

      /// The symbol type as needed by the constructor.
      typedef state_type kind_type;

      /// Constructor.
      by_state (kind_type s) YY_NOEXCEPT;

      /// Copy constructor.
      by_state (const by_state& that) YY_NOEXCEPT;

      /// Record that this symbol is empty.
      void clear () YY_NOEXCEPT;

      /// Steal the symbol type from \a that.
      void move (by_state& that);

      /// The (internal) type number (corresponding to \a state).
      /// \a empty_symbol when empty.
      symbol_number_type type_get () const YY_NOEXCEPT;

      /// The state number used to denote an empty symbol.
      /// We use the initial state, as it does not have a value.
      enum { empty_state = 0 };

      /// The state.
      /// \a empty when empty.
      state_type state;
    };

    /// "Internal" symbol: element of the stack.
    struct stack_symbol_type : basic_symbol<by_state>
    {
      /// Superclass.
      typedef basic_symbol<by_state> super_type;
      /// Construct an empty symbol.
      stack_symbol_type ();
      /// Move or copy construction.
      stack_symbol_type (YY_RVREF (stack_symbol_type) that);
      /// Steal the contents from \a sym to build this.
      stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) sym);
#if YY_CPLUSPLUS < 201103L
      /// Assignment, needed by push_back by some old implementations.
      /// Moves the contents of that.
      stack_symbol_type& operator= (stack_symbol_type& that);

      /// Assignment, needed by push_back by other implementations.
      /// Needed by some other old implementations.
      stack_symbol_type& operator= (const stack_symbol_type& that);
#endif
    };

    /// A stack with random access from its top.
    template <typename T, typename S = std::vector<T> >
    class stack
    {
    public:
      // Hide our reversed order.
      typedef typename S::reverse_iterator iterator;
      typedef typename S::const_reverse_iterator const_iterator;
      typedef typename S::size_type size_type;
      typedef typename std::ptrdiff_t index_type;

      stack (size_type n = 200)
        : seq_ (n)
      {}

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      const T&
      operator[] (index_type i) const
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      T&
      operator[] (index_type i)
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Steal the contents of \a t.
      ///
      /// Close to move-semantics.
      void
      push (YY_MOVE_REF (T) t)
      {
        seq_.push_back (T ());
        operator[] (0).move (t);
      }

      /// Pop elements from the stack.
      void
      pop (std::ptrdiff_t n = 1) YY_NOEXCEPT
      {
        for (; 0 < n; --n)
          seq_.pop_back ();
      }

      /// Pop all elements from the stack.
      void
      clear () YY_NOEXCEPT
      {
        seq_.clear ();
      }

      /// Number of elements on the stack.
      index_type
      size () const YY_NOEXCEPT
      {
        return index_type (seq_.size ());
      }

      std::ptrdiff_t
      ssize () const YY_NOEXCEPT
      {
        return std::ptrdiff_t (size ());
      }

      /// Iterator on top of the stack (going downwards).
      const_iterator
      begin () const YY_NOEXCEPT
      {
        return seq_.rbegin ();
      }

      /// Bottom of the stack.
      const_iterator
      end () const YY_NOEXCEPT
      {
        return seq_.rend ();
      }

      /// Present a slice of the top of a stack.
      class slice
      {
      public:
        slice (const stack& stack, index_type range)
          : stack_ (stack)
          , range_ (range)
        {}

        const T&
        operator[] (index_type i) const
        {
          return stack_[range_ - i];
        }

      private:
        const stack& stack_;
        index_type range_;
      };

    private:
      stack (const stack&);
      stack& operator= (const stack&);
      /// The wrapped container.
      S seq_;
    };


    /// Stack type.
    typedef stack<stack_symbol_type> stack_type;

    /// The stack.
    stack_type yystack_;

    /// Push a new state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param sym  the symbol
    /// \warning the contents of \a s.value is stolen.
    void yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym);

    /// Push a new look ahead token on the state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param s    the state
    /// \param sym  the symbol (for its value and location).
    /// \warning the contents of \a sym.value is stolen.
    void yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym);

    /// Pop \a n symbols from the stack.
    void yypop_ (int n = 1);

    /// Some specific tokens.
    static const token_number_type yy_error_token_ = 1;
    static const token_number_type yy_undef_token_ = 2;

    /// Constants.
    enum
    {
      yyeof_ = 0,
      yylast_ = 246,     ///< Last index in yytable_.
      yynnts_ = 33,  ///< Number of nonterminal symbols.
      yyfinal_ = 5, ///< Termination state number.
      yyntokens_ = 48  ///< Number of tokens.
    };


    // User arguments.
    parser::WhileParsingContext &context;
  };

  inline
  WhileParser::token_number_type
  WhileParser::yytranslate_ (int t)
  {
    // YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to
    // TOKEN-NUM as returned by yylex.
    static
    const token_number_type
    translate_table[] =
    {
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47
    };
    const int user_token_number_max_ = 302;

    if (t <= 0)
      return yyeof_;
    else if (t <= user_token_number_max_)
      return translate_table[t];
    else
      return yy_undef_token_;
  }

  // basic_symbol.
#if 201103L <= YY_CPLUSPLUS
  template <typename Base>
  WhileParser::basic_symbol<Base>::basic_symbol (basic_symbol&& that)
    : Base (std::move (that))
    , value ()
    , location (std::move (that.location))
  {
    switch (this->type_get ())
    {
      case 56: // smtlib_formula
        value.move<  std::shared_ptr<const logic::Formula>  > (std::move (that.value));
        break;

      case 54: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (std::move (that.value));
        break;

      case 60: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (std::move (that.value));
        break;

      case 62: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (std::move (that.value));
        break;

      case 78: // formula
        value.move<  std::shared_ptr<const program::BoolExpression>  > (std::move (that.value));
        break;

      case 64: // function
        value.move<  std::shared_ptr<const program::Function>  > (std::move (that.value));
        break;

      case 69: // if_else_statement
        value.move<  std::shared_ptr<const program::IfElse>  > (std::move (that.value));
        break;

      case 68: // assignment_statement
        value.move<  std::shared_ptr<const program::IntAssignment>  > (std::move (that.value));
        break;

      case 79: // expr
      case 80: // location
        value.move<  std::shared_ptr<const program::IntExpression>  > (std::move (that.value));
        break;

      case 52: // program
        value.move<  std::shared_ptr<const program::Program>  > (std::move (that.value));
        break;

      case 75: // skip_statement
        value.move<  std::shared_ptr<const program::SkipStatement>  > (std::move (that.value));
        break;

      case 67: // statement
        value.move<  std::shared_ptr<const program::Statement>  > (std::move (that.value));
        break;

      case 77: // var_definition_head
        value.move<  std::shared_ptr<const program::Variable>  > (std::move (that.value));
        break;

      case 73: // while_statement
        value.move<  std::shared_ptr<const program::WhileStatement>  > (std::move (that.value));
        break;

      case 63: // function_list
        value.move<  std::vector< std::shared_ptr<const program::Function>>  > (std::move (that.value));
        break;

      case 55: // smtlib_formula_list
        value.move<  std::vector<std::shared_ptr<const logic::Formula>>  > (std::move (that.value));
        break;

      case 53: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (std::move (that.value));
        break;

      case 59: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (std::move (that.value));
        break;

      case 61: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (std::move (that.value));
        break;

      case 66: // statement_list
        value.move<  std::vector<std::shared_ptr<const program::Statement>>  > (std::move (that.value));
        break;

      case 76: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<const program::Variable>>  > (std::move (that.value));
        break;

      case 45: // "number"
        value.move< int > (std::move (that.value));
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.move< std::string > (std::move (that.value));
        break;

      default:
        break;
    }

  }
#endif

  template <typename Base>
  WhileParser::basic_symbol<Base>::basic_symbol (const basic_symbol& that)
    : Base (that)
    , value ()
    , location (that.location)
  {
    switch (this->type_get ())
    {
      case 56: // smtlib_formula
        value.copy<  std::shared_ptr<const logic::Formula>  > (YY_MOVE (that.value));
        break;

      case 54: // smtlib_problemitem
        value.copy<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (that.value));
        break;

      case 60: // smtlib_quantvar
        value.copy<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (that.value));
        break;

      case 62: // smtlib_term
        value.copy<  std::shared_ptr<const logic::Term>  > (YY_MOVE (that.value));
        break;

      case 78: // formula
        value.copy<  std::shared_ptr<const program::BoolExpression>  > (YY_MOVE (that.value));
        break;

      case 64: // function
        value.copy<  std::shared_ptr<const program::Function>  > (YY_MOVE (that.value));
        break;

      case 69: // if_else_statement
        value.copy<  std::shared_ptr<const program::IfElse>  > (YY_MOVE (that.value));
        break;

      case 68: // assignment_statement
        value.copy<  std::shared_ptr<const program::IntAssignment>  > (YY_MOVE (that.value));
        break;

      case 79: // expr
      case 80: // location
        value.copy<  std::shared_ptr<const program::IntExpression>  > (YY_MOVE (that.value));
        break;

      case 52: // program
        value.copy<  std::shared_ptr<const program::Program>  > (YY_MOVE (that.value));
        break;

      case 75: // skip_statement
        value.copy<  std::shared_ptr<const program::SkipStatement>  > (YY_MOVE (that.value));
        break;

      case 67: // statement
        value.copy<  std::shared_ptr<const program::Statement>  > (YY_MOVE (that.value));
        break;

      case 77: // var_definition_head
        value.copy<  std::shared_ptr<const program::Variable>  > (YY_MOVE (that.value));
        break;

      case 73: // while_statement
        value.copy<  std::shared_ptr<const program::WhileStatement>  > (YY_MOVE (that.value));
        break;

      case 63: // function_list
        value.copy<  std::vector< std::shared_ptr<const program::Function>>  > (YY_MOVE (that.value));
        break;

      case 55: // smtlib_formula_list
        value.copy<  std::vector<std::shared_ptr<const logic::Formula>>  > (YY_MOVE (that.value));
        break;

      case 53: // smtlib_problemitem_list
        value.copy<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (that.value));
        break;

      case 59: // smtlib_quantvar_list
        value.copy<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (that.value));
        break;

      case 61: // smtlib_term_list
        value.copy<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (that.value));
        break;

      case 66: // statement_list
        value.copy<  std::vector<std::shared_ptr<const program::Statement>>  > (YY_MOVE (that.value));
        break;

      case 76: // active_vars_dummy
        value.copy<  std::vector<std::shared_ptr<const program::Variable>>  > (YY_MOVE (that.value));
        break;

      case 45: // "number"
        value.copy< int > (YY_MOVE (that.value));
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.copy< std::string > (YY_MOVE (that.value));
        break;

      default:
        break;
    }

  }



  template <typename Base>
  bool
  WhileParser::basic_symbol<Base>::empty () const YY_NOEXCEPT
  {
    return Base::type_get () == empty_symbol;
  }

  template <typename Base>
  void
  WhileParser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move (s);
    switch (this->type_get ())
    {
      case 56: // smtlib_formula
        value.move<  std::shared_ptr<const logic::Formula>  > (YY_MOVE (s.value));
        break;

      case 54: // smtlib_problemitem
        value.move<  std::shared_ptr<const logic::ProblemItem>  > (YY_MOVE (s.value));
        break;

      case 60: // smtlib_quantvar
        value.move<  std::shared_ptr<const logic::Symbol>  > (YY_MOVE (s.value));
        break;

      case 62: // smtlib_term
        value.move<  std::shared_ptr<const logic::Term>  > (YY_MOVE (s.value));
        break;

      case 78: // formula
        value.move<  std::shared_ptr<const program::BoolExpression>  > (YY_MOVE (s.value));
        break;

      case 64: // function
        value.move<  std::shared_ptr<const program::Function>  > (YY_MOVE (s.value));
        break;

      case 69: // if_else_statement
        value.move<  std::shared_ptr<const program::IfElse>  > (YY_MOVE (s.value));
        break;

      case 68: // assignment_statement
        value.move<  std::shared_ptr<const program::IntAssignment>  > (YY_MOVE (s.value));
        break;

      case 79: // expr
      case 80: // location
        value.move<  std::shared_ptr<const program::IntExpression>  > (YY_MOVE (s.value));
        break;

      case 52: // program
        value.move<  std::shared_ptr<const program::Program>  > (YY_MOVE (s.value));
        break;

      case 75: // skip_statement
        value.move<  std::shared_ptr<const program::SkipStatement>  > (YY_MOVE (s.value));
        break;

      case 67: // statement
        value.move<  std::shared_ptr<const program::Statement>  > (YY_MOVE (s.value));
        break;

      case 77: // var_definition_head
        value.move<  std::shared_ptr<const program::Variable>  > (YY_MOVE (s.value));
        break;

      case 73: // while_statement
        value.move<  std::shared_ptr<const program::WhileStatement>  > (YY_MOVE (s.value));
        break;

      case 63: // function_list
        value.move<  std::vector< std::shared_ptr<const program::Function>>  > (YY_MOVE (s.value));
        break;

      case 55: // smtlib_formula_list
        value.move<  std::vector<std::shared_ptr<const logic::Formula>>  > (YY_MOVE (s.value));
        break;

      case 53: // smtlib_problemitem_list
        value.move<  std::vector<std::shared_ptr<const logic::ProblemItem> >  > (YY_MOVE (s.value));
        break;

      case 59: // smtlib_quantvar_list
        value.move<  std::vector<std::shared_ptr<const logic::Symbol>>  > (YY_MOVE (s.value));
        break;

      case 61: // smtlib_term_list
        value.move<  std::vector<std::shared_ptr<const logic::Term>>  > (YY_MOVE (s.value));
        break;

      case 66: // statement_list
        value.move<  std::vector<std::shared_ptr<const program::Statement>>  > (YY_MOVE (s.value));
        break;

      case 76: // active_vars_dummy
        value.move<  std::vector<std::shared_ptr<const program::Variable>>  > (YY_MOVE (s.value));
        break;

      case 45: // "number"
        value.move< int > (YY_MOVE (s.value));
        break;

      case 42: // "program identifier"
      case 43: // "smtlib identifier"
      case 44: // "type identifier"
        value.move< std::string > (YY_MOVE (s.value));
        break;

      default:
        break;
    }

    location = YY_MOVE (s.location);
  }

  // by_type.
  inline
  WhileParser::by_type::by_type ()
    : type (empty_symbol)
  {}

#if 201103L <= YY_CPLUSPLUS
  inline
  WhileParser::by_type::by_type (by_type&& that)
    : type (that.type)
  {
    that.clear ();
  }
#endif

  inline
  WhileParser::by_type::by_type (const by_type& that)
    : type (that.type)
  {}

  inline
  WhileParser::by_type::by_type (token_type t)
    : type (yytranslate_ (t))
  {}

  inline
  void
  WhileParser::by_type::clear ()
  {
    type = empty_symbol;
  }

  inline
  void
  WhileParser::by_type::move (by_type& that)
  {
    type = that.type;
    that.clear ();
  }

  inline
  int
  WhileParser::by_type::type_get () const YY_NOEXCEPT
  {
    return type;
  }

#line 4 "WhileParser.yy"
} // parser
#line 2644 "../src/parser/WhileParser.hpp"





#endif // !YY_YY_SRC_PARSER_WHILEPARSER_HPP_INCLUDED
