/**
 * @file Expression.hpp
 *
 * Defines class Program::Expression, representing expressions in the
 * guarded command language
 *
 */

#ifndef __ProgramExpression__
#define __ProgramExpression__

#include <iostream>
#include <memory>
#include <string>
#include <utility>

#include "ValueType.hpp"

namespace program {

class Expression {
 public:
  virtual ~Expression() = default;

  virtual ValueType type() const = 0;

  virtual std::string toString() const = 0;
};

std::ostream &operator<<(std::ostream &ostr, Expression &e);

class ArithmeticConstant : public Expression {
 public:
  ArithmeticConstant(int value) : value(value) {}

  const int value;

  ValueType type() const override { return ValueType::Int; }

  std::string toString() const override;
};

class UnaryExpression : public Expression {
 public:
  UnaryExpression(std::shared_ptr<Expression> child)
      : child(std::move(child)) {}

  const std::shared_ptr<Expression> child;
};

class BinaryExpression : public Expression {
 public:
  BinaryExpression(std::shared_ptr<Expression> child1,
                   std::shared_ptr<Expression> child2)
      : child1(std::move(child1)), child2(std::move(child2)) {}

  const std::shared_ptr<Expression> child1;
  const std::shared_ptr<Expression> child2;
};

class Addition : public BinaryExpression {
 public:
  Addition(std::shared_ptr<Expression> child1,
           std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Int) {
      std::cout << "+ expected an Int on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Int) {
      std::cout << "+ expected an Int on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Int; }

  std::string toString() const override;
};

class Subtraction : public BinaryExpression {
 public:
  Subtraction(std::shared_ptr<Expression> child1,
              std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Int) {
      std::cout << "- expected an Int on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Int) {
      std::cout << "- expected an Int on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Int; }

  std::string toString() const override;
};

class Modulo : public BinaryExpression {
 public:
  Modulo(std::shared_ptr<Expression> child1, std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Int) {
      std::cout << "`mod` expected an Int on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Int) {
      std::cout << "`mod` expected an Int on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Int; }

  std::string toString() const override;
};

class Multiplication : public BinaryExpression {
 public:
  Multiplication(std::shared_ptr<Expression> child1,
                 std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Int) {
      std::cout << "* expected an Int on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Int) {
      std::cout << "* expected an Int on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Int; }

  std::string toString() const override;
};

class BooleanConstant : public Expression {
 public:
  BooleanConstant(bool value) : value(value) {}

  const bool value;

  ValueType type() const override { return ValueType::Bool; }

  std::string toString() const override;
};

class BooleanAnd : public BinaryExpression {
 public:
  BooleanAnd(std::shared_ptr<Expression> child1,
             std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Bool) {
      std::cout << "&& expected a Bool on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Bool) {
      std::cout << "&& expected a Bool on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Bool; }

  std::string toString() const override;
};

class BooleanOr : public BinaryExpression {
 public:
  BooleanOr(std::shared_ptr<Expression> child1,
            std::shared_ptr<Expression> child2)
      : BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Bool) {
      std::cout << "|| expected a Bool on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Bool) {
      std::cout << "|| expected a Bool on the rhs" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Bool; }

  std::string toString() const override;
};

class BooleanNot : public UnaryExpression {
 public:
  BooleanNot(std::shared_ptr<Expression> child)
      : UnaryExpression(std::move(child)) {
    if (this->child->type() != ValueType::Bool) {
      std::cout << "! expected a Bool" << std::endl;
      exit(1);
    }
  }

  ValueType type() const override { return ValueType::Bool; }

  std::string toString() const override;
};

class ArithmeticComparison : public BinaryExpression {
 public:
  enum class Kind { GE, GT, LE, LT, EQ };

  ArithmeticComparison(Kind kind, std::shared_ptr<Expression> child1,
                       std::shared_ptr<Expression> child2)
      : kind(kind), BinaryExpression(std::move(child1), std::move(child2)) {
    if (this->child1->type() != ValueType::Int) {
      std::cout << "Comparison expected an Int on the lhs" << std::endl;
      exit(1);
    }
    if (this->child2->type() != ValueType::Int) {
      std::cout << "Comparison expected an Int on the rhs" << std::endl;
      exit(1);
    }
  }

  const Kind kind;

  ValueType type() const override { return ValueType::Bool; }

  std::string toString() const override;
};

}  // namespace program
#endif
