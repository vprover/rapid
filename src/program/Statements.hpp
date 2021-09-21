#ifndef __Assignment__
#define __Assignment__

#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <unordered_map>

#include "Expression.hpp"
#include "Variable.hpp"

namespace program {
class WhileStatement;

class TransformationInfo;

/**
 * Will be modified only in course of the program transformation.
 * After that the statements and their children can be seen as "const".
 */
class Statement {
 public:
  Statement(unsigned lineNumber)
      : location("l" + std::to_string(lineNumber != 0
                                          ? lineNumber
                                          : Statement::additionalTimepoints--)),
        enclosingLoops(std::make_unique<std::vector<WhileStatement *>>()) {}

  virtual ~Statement() {}

  const std::string location;
  /*
   * enclosingLoops can only be computed after all enclosing loops are
   * constructed, and the implementation only constructs them immediately after
   * the whole function is constructed in the parser. This field can therefore
   * only be used afterwards. Since enclosingLoops can't be computed at
   * construction time, we need our programs to be constant only up to the
   * enclosingLoop-field. we achieve this by using indirection: constness is not
   * transitive in c++, so we get a (constant) pointer to a (not necessarily
   * constant) vector enclosingLoops, which we can fill up in the
   * parser-post-computation.
   */
  std::unique_ptr<std::vector<WhileStatement *>> enclosingLoops;

  virtual std::string toString(int indentation) const = 0;

  /**
   * Will be decremented starting with UINT_MAX  (counts downward to avoid
   * collisions with existing line numbers) for example generating the implicit
   * else branch gives:
   *
   * line nr                          Code
   * --------------------------------------------------
   * n + 0                               : if (...) {
   * n + 1                               : ...
   * n + m                               : }
   * UINT_MAX - additionalTimepoints     : else {  // Added automatically
   * UINT_MAX - additionalTimepoints - 1 : skip    // Added automatically
   * -                                   : }       // Added automatically
   * n + m + 1                           : ...
   */
  static unsigned additionalTimepoints;

  static TransformationInfo transformBlock(
      std::vector<std::shared_ptr<Statement>> &statements,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces);

  virtual TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) = 0;
};

struct StatementSharedPtrHash {
  size_t operator()(const std::shared_ptr<const Statement> &ptr) const {
    return std::hash<std::string>()(ptr->location);
  }
};

std::ostream &operator<<(std::ostream &ostr, Statement &v);

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream &operator<<(
    std::ostream &ostr,
    const std::vector<std::shared_ptr<program::Statement>> &e);

class Assignment : public Statement {
 public:
  Assignment(unsigned lineNumber, std::shared_ptr<Expression> lhs,
             std::shared_ptr<Expression> rhs)
      : Statement(lineNumber), lhs(std::move(lhs)), rhs(std::move(rhs)) {}

  std::shared_ptr<Expression> lhs;
  std::shared_ptr<Expression> rhs;

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class IfElseStatement : public Statement {
 public:
  IfElseStatement(unsigned lineNumber, std::shared_ptr<Expression> condition,
                  std::vector<std::shared_ptr<Statement>> ifStatements,
                  std::vector<std::shared_ptr<Statement>> elseStatements)
      : Statement(lineNumber),
        condition(std::move(condition)),
        ifStatements(std::move(ifStatements)),
        elseStatements(std::move(elseStatements)) {
    assert(this->ifStatements.size() > 0);
    assert(this->elseStatements.size() > 0);

    if (this->condition->type() != ValueType::Bool) {
      std::cout << "if-condition expected a Bool as condition" << std::endl;
      exit(1);
    }
  }

  std::shared_ptr<Expression> condition;
  std::vector<std::shared_ptr<Statement>> ifStatements;
  std::vector<std::shared_ptr<Statement>> elseStatements;

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class WhileStatement : public Statement {
 public:
  WhileStatement(unsigned lineNumber, std::shared_ptr<Expression> condition,
                 std::vector<std::shared_ptr<Statement>> bodyStatements)
      : Statement(lineNumber),
        condition(std::move(condition)),
        bodyStatements(std::move(bodyStatements)) {
    // TODO: add a skip-statement instead, maybe already during parsing
    // (challenge: unique numbering)
    assert(this->bodyStatements.size() > 0);

    if (this->condition->type() != ValueType::Bool) {
      std::cout << "while-condition expected a Bool as condition" << std::endl;
      exit(1);
    }
  }

  std::shared_ptr<Expression> condition;
  std::vector<std::shared_ptr<Statement>> bodyStatements;

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class BreakStatement : public Statement {
 public:
  BreakStatement(unsigned lineNumber) : Statement(lineNumber){};

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class ContinueStatement : public Statement {
 public:
  ContinueStatement(unsigned lineNumber) : Statement(lineNumber){};

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class ReturnStatement : public Statement {
 public:
  ReturnStatement(unsigned lineNumber, std::shared_ptr<Expression> returnValue)
      : Statement(lineNumber), returnValue(std::move(returnValue)){};

  std::string toString(int indentation) const override;

  const std::shared_ptr<Expression> returnValue;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

class SkipStatement : public Statement {
 public:
  SkipStatement(unsigned lineNumber) : Statement(lineNumber){};

  std::string toString(int indentation) const override;

  TransformationInfo transform(
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          &locationToActiveVars,
      unsigned traces) override;
};

/**
 * Contains a list of break, continue, and return that currently affect the
 * control flow If some break/continue/return is encountered a new variable is
 * introduced. The variables that are currently relevant are collected in this
 * class
 */
class TransformationInfo {
 public:
  TransformationInfo()
      : break_conditions(),
        continue_conditions(),
        return_conditions(),
        introduced_var(nullptr) {}

  std::vector<std::shared_ptr<VariableAccess>> break_conditions;
  std::vector<std::shared_ptr<VariableAccess>> continue_conditions;
  std::vector<std::shared_ptr<VariableAccess>> return_conditions;

  void mergeBreak(std::vector<std::shared_ptr<VariableAccess>> &other) {
    for (const auto &o : other) {
      break_conditions.push_back(o);
    }
  }

  void mergeContinue(std::vector<std::shared_ptr<VariableAccess>> &other) {
    for (const auto &o : other) {
      continue_conditions.push_back(o);
    }
  }

  void mergeReturn(std::vector<std::shared_ptr<VariableAccess>> &other) {
    for (const auto &o : other) {
      return_conditions.push_back(o);
    }
  }

  // The variable introduced right before
  std::shared_ptr<Variable> introduced_var;
};
}  // namespace program

#endif
