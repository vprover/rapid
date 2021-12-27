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

namespace program {

enum BasicType { STRUCT, INTEGER, NAT, ARRAY, POINTER };

class VarDecl;

class ExprType {
 public:
  ExprType(BasicType bt) : bt(bt) {}
  ExprType(std::shared_ptr<const ExprType> child)
      : bt(program::BasicType::POINTER), child(child) {}
  ExprType(std::shared_ptr<const ExprType> child, BasicType bt)
      : bt(bt), child(child) {}
  ~ExprType() {}

  std::shared_ptr<const ExprType> getChild() const { return child; }
  virtual std::string toString() const {
    if (bt == BasicType::POINTER) {
      return "->" + child->toString();
    } else if (bt == BasicType::INTEGER) {
      return "Int";
    } else if (bt == BasicType::ARRAY) {
      return "Arr";
    } else {
      return "Nat";
    }
  }
  program::BasicType type() const { return bt; };
  bool isStructType() const { 
    return bt == BasicType::STRUCT;
  }

  bool isIntType() const { 
    return bt == BasicType::INTEGER;
  }

  bool isPointerType() const { 
    return bt == BasicType::POINTER;
  }

  bool isArrayType() const { 
    return bt == BasicType::ARRAY;
  }

  bool isPointerToPointer() const {
    return (bt == BasicType::POINTER && child->type() == BasicType::POINTER);
  }

  bool isPointerToStruct() const {
    return (bt == BasicType::POINTER && child->type() == BasicType::STRUCT);
  }

  bool isPointerToNonPointer() const {
    return (bt == BasicType::POINTER && child->type() != BasicType::POINTER);    
  }

  // recursive equality def
  bool operator==(const ExprType& other) const {
    return other.bt == bt && (other.child == child || *child == *other.child);
  }

  bool operator!=(const ExprType& other) const { return !(*this == other); }

 private:
  const std::shared_ptr<const ExprType> child;
  program::BasicType bt;
};


// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const program::ExprType>>& e);

enum class Type {
  IntegerConstant,
  Addition,
  Subtraction,
  Modulo,
  Multiplication,
  VariableAccess,
  PointerDeref,
  IntArrayApplication,
  VarReference,
  FieldAccess,
};

class Expression {
 public:
  virtual ~Expression() {}

  Expression(BasicType bt) {
    exprtype = std::shared_ptr<const ExprType>(new ExprType(bt));
  }

  Expression(std::shared_ptr<const ExprType> typ) {
    exprtype = typ;
  }

  virtual bool containsReference() const { return false; }

  virtual bool isConstVar() const { return false; }

  virtual Type type() const = 0;

  virtual std::string toString() const = 0;

  virtual const std::shared_ptr<const ExprType> exprType() const {
    return exprtype;
  }

  virtual bool isArithmeticExpr() const { 
    return exprtype->type() == BasicType::INTEGER ||
           exprtype->type() == BasicType::NAT;
  }

  virtual bool isPointerExpr() const { 
    return exprtype->type() == BasicType::POINTER;
  }

  virtual bool isStructExpr() const { 
    return exprtype->type() == BasicType::STRUCT;
  }

 protected:
  std::shared_ptr<const ExprType> exprtype;
};
std::ostream& operator<<(std::ostream& ostr, const Expression& e);

class ArithmeticConstant : public Expression {
 public:
  ArithmeticConstant(unsigned value) : Expression(BasicType::INTEGER), value(value) {}

  const int value;

  Type type() const override { return program::Type::IntegerConstant; }
  std::string toString() const override;
};

class Addition : public Expression {
 public:
  Addition(std::shared_ptr<const Expression> summand1,
           std::shared_ptr<const Expression> summand2)
      : Expression(BasicType::INTEGER), summand1(std::move(summand1)), summand2(std::move(summand2)) {}

  const std::shared_ptr<const Expression> summand1;
  const std::shared_ptr<const Expression> summand2;

  Type type() const override { return program::Type::Addition; }
  std::string toString() const override;
};

class Subtraction : public Expression {
 public:
  Subtraction(std::shared_ptr<const Expression> child1,
              std::shared_ptr<const Expression> child2)
      : Expression(BasicType::INTEGER), child1(std::move(child1)), child2(std::move(child2)) {}

  const std::shared_ptr<const Expression> child1;
  const std::shared_ptr<const Expression> child2;

  Type type() const override { return program::Type::Subtraction; }
  std::string toString() const override;
};

class Modulo : public Expression {
 public:
  Modulo(std::shared_ptr<const Expression> child1,
         std::shared_ptr<const Expression> child2)
      : Expression(BasicType::INTEGER), child1(std::move(child1)), child2(std::move(child2)) {}

  const std::shared_ptr<const Expression> child1;
  const std::shared_ptr<const Expression> child2;

  Type type() const override { return program::Type::Modulo; }
  std::string toString() const override;
};

class Multiplication : public Expression {
 public:
  Multiplication(std::shared_ptr<const Expression> factor1,
                 std::shared_ptr<const Expression> factor2)
      : Expression(BasicType::INTEGER), factor1(std::move(factor1)), factor2(std::move(factor2)) {}

  const std::shared_ptr<const Expression> factor1;
  const std::shared_ptr<const Expression> factor2;

  Type type() const override { return program::Type::Multiplication; }
  std::string toString() const override;
};

class BoolExpression {
 public:
  virtual ~BoolExpression() {}

  enum class Type {
    BooleanConstant,
    BooleanAnd,
    BooleanOr,
    BooleanNot,
    ArithmeticComparison
  };
  virtual Type type() const = 0;

  virtual std::string toString() const = 0;
};
std::ostream& operator<<(std::ostream& ostr, const BoolExpression& e);

class BooleanConstant : public BoolExpression {
 public:
  BooleanConstant(bool value) : value(value) {}

  const bool value;

  Type type() const override { return BoolExpression::Type::BooleanConstant; }
  std::string toString() const override;
};

class BooleanAnd : public BoolExpression {
 public:
  BooleanAnd(std::shared_ptr<const BoolExpression> child1,
             std::shared_ptr<const BoolExpression> child2)
      : child1(std::move(child1)), child2(std::move(child2)) {}

  const std::shared_ptr<const BoolExpression> child1;
  const std::shared_ptr<const BoolExpression> child2;

  Type type() const override { return BoolExpression::Type::BooleanAnd; }
  std::string toString() const override;
};

class BooleanOr : public BoolExpression {
 public:
  BooleanOr(std::shared_ptr<const BoolExpression> child1,
            std::shared_ptr<const BoolExpression> child2)
      : child1(std::move(child1)), child2(std::move(child2)) {}

  const std::shared_ptr<const BoolExpression> child1;
  const std::shared_ptr<const BoolExpression> child2;

  Type type() const override { return BoolExpression::Type::BooleanOr; }
  std::string toString() const override;
};

class BooleanNot : public BoolExpression {
 public:
  BooleanNot(std::shared_ptr<const BoolExpression> child)
      : child(std::move(child)) {}

  const std::shared_ptr<const BoolExpression> child;

  Type type() const override { return BoolExpression::Type::BooleanNot; }
  std::string toString() const override;
};

class ArithmeticComparison : public BoolExpression {
 public:
  enum class Kind { GE, GT, LE, LT, EQ };

  ArithmeticComparison(Kind kind, std::shared_ptr<const Expression> child1,
                       std::shared_ptr<const Expression> child2)
      : kind(kind), child1(std::move(child1)), child2(std::move(child2)) {}

  const Kind kind;
  const std::shared_ptr<const Expression> child1;
  const std::shared_ptr<const Expression> child2;

  Type type() const override {
    return BoolExpression::Type::ArithmeticComparison;
  }
  std::string toString() const override;
};

}  // namespace program
#endif
