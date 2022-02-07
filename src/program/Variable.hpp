/**
 *
 * @file Variable.hpp
 *
 * Program variables (and variables coming from assertion quantifiers)
 */

#ifndef __ProgramVariable__
#define __ProgramVariable__

#include <cassert>
#include <cstddef>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <list>

#include "Expression.hpp"

namespace program {

class Variable {
 public:
  Variable(std::string name, bool isConstant,
           std::shared_ptr<const ExprType> vt, unsigned numberOfTraces)
      : name(name),
        isConstant(isConstant),
        vt(vt),
        numberOfTraces(numberOfTraces) {}

  const std::string name;
  const bool isConstant;
  const unsigned numberOfTraces;
  const std::shared_ptr<const ExprType> vt;

  bool isPointer() const { return vt->type() == program::BasicType::POINTER; }

  bool isArray() const { return vt->type() == program::BasicType::ARRAY; }

  bool isStruct() const { return vt->type() == program::BasicType::STRUCT; }

  bool isNat() const { return vt->type() == program::BasicType::NAT; }

  bool isInt() const { return vt->type() == program::BasicType::INTEGER; }

  // sanity-assertion: if two variables have the same name, they agree on all
  // other properties.
  bool operator==(const Variable& rhs) const {
    assert(!(name == rhs.name) ||
           (isConstant == rhs.isConstant && *vt == *rhs.vt &&
            numberOfTraces == rhs.numberOfTraces));
    return (name == rhs.name);
  }
  bool operator!=(const Variable& rhs) const { return !operator==(rhs); }
};
}  // namespace program

namespace std {
template <>
struct hash<program::Variable> {
  std::size_t operator()(const program::Variable& v) const noexcept {
    return std::hash<std::string>{}(v.name);
  }
};
}  // namespace std

namespace program {

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const program::Variable>>& e);

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::list<std::shared_ptr<const program::Variable>>& e);

class StructType : public ExprType {
  public:
  
  StructType(std::string name, 
    std::list<std::shared_ptr<const program::Variable>> f) :
      fields(f), 
      name(name),
    ExprType(BasicType::STRUCT) {}

  std::string getName() const { return name; }
  std::shared_ptr<const program::Variable> getField(std::string name) const;
  std::list<std::shared_ptr<const program::Variable>> getFields() const { return fields; }

  std::string toString() const override;

  private:
    std::list<std::shared_ptr<const program::Variable>> fields;
    std::string name;
};

class VariableAccess : public Expression {
 public:
  VariableAccess(std::shared_ptr<const Variable> var)
      : Expression(var->vt), var(var) {
    assert(this->var != nullptr);
    //assert(this->var->vt->type() == program::BasicType::INTEGER ||
    //       this->var->vt->type() == program::BasicType::NAT);
  }

  const std::shared_ptr<const Variable> var;

  bool isConstVar() const override { return var->isConstant; };

  program::Type type() const override {
    return program::Type::VariableAccess;
  }

  std::string toString() const override;
};

class StructFieldAccess : public Expression {
 public:
  StructFieldAccess(std::shared_ptr<const Variable> field,
                    std::shared_ptr<const Expression> struc) :
  Expression(field->vt), field(std::move(field)), struc(std::move(struc)){
    //TODO check that if it is a pointer, it points to a struc
    assert(this->struc->isStructExpr() ||
           this->struc->isPointerExpr());
  }

  program::Type type() const override {
    return program::Type::FieldAccess;
  }

  std::string toString() const override;

  std::shared_ptr<const Expression> getStruct() const {
    return struc;
  }

  std::shared_ptr<const Variable> getField() const {
    return field;
  }

  private:
    const std::shared_ptr<const Variable> field;
    const std::shared_ptr<const Expression> struc;
};

class IntArrayApplication : public Expression {
 public:
  IntArrayApplication(std::shared_ptr<const Variable> array,
                      std::shared_ptr<const Expression> index)
      : Expression(array->vt), array(std::move(array)), index(std::move(index)) {
    assert(this->array != nullptr);
    assert(this->index != nullptr);
    assert(this->array->vt->type() == program::BasicType::ARRAY);
  }

  const std::shared_ptr<const Variable> array;
  const std::shared_ptr<const Expression> index;

  bool isConstVar() const override { return array->isConstant; };

  program::Type type() const override {
    return program::Type::IntArrayApplication;
  }

  std::string toString() const override;
};

class DerefExpression : public Expression {
 public:
  DerefExpression(std::shared_ptr<const Expression> expr)
      : Expression(
          std::shared_ptr<const program::ExprType>(new ExprType(
            expr->exprType()->getChild()->getChild(), 
            expr->exprType()->getChild()->type()      
          )) 
        ), expr(expr) {
    assert(expr != nullptr);
    assert(expr->exprType()->type() == program::BasicType::POINTER);
  }

  const std::shared_ptr<const Expression> expr;

  bool containsReference() const override { return expr->containsReference(); }

  program::Type type() const override {
    return program::Type::PointerDeref;
  }

  std::string toString() const override;
};


class VarReference : public Expression {
 public:
  VarReference(std::shared_ptr<const Variable> var)
      : Expression(std::shared_ptr<const program::ExprType>(new ExprType(var->vt))),
        referent(var) {
    assert(referent != nullptr);
  }

  const std::shared_ptr<const Variable> referent;

  bool containsReference() const override { return true; }

  program::Type type() const override { return program::Type::VarReference; }

  std::string toString() const override;
};
}  // namespace program

#endif  // __ProgramVariable__
