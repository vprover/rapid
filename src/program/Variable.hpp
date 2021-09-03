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

#include "Expression.hpp"
#include "ValueType.hpp"

namespace program {

class Variable {
 public:
  Variable(std::string name, bool isConstant, bool isArray,
           unsigned numberOfTraces)
      : name(name),
        isConstant(isConstant),
        isArray(isArray),
        numberOfTraces(numberOfTraces) {}

  const std::string name;
  const bool isConstant;
  const bool isArray;
  const unsigned numberOfTraces;

  virtual ValueType type() const = 0;

  // sanity-assertion: if two variables have the same name, they agree on all
  // other properties.
  bool operator==(Variable& rhs) const {
    assert(!(name == rhs.name) ||
           (isConstant == rhs.isConstant && isArray == rhs.isArray &&
            type() == rhs.type() && numberOfTraces == rhs.numberOfTraces));
    return (name == rhs.name);
  }
  bool operator!=(Variable& rhs) const { return !operator==(rhs); }
};

class IntVariable : public Variable {
 public:
  IntVariable(std::string name, bool isConstant, bool isArray,
              unsigned numberOfTraces)
      : Variable(name, isConstant, isArray, numberOfTraces) {}

  ValueType type() const override { return ValueType::Int; }
};

class BoolVariable : public Variable {
 public:
  BoolVariable(std::string name, bool isConstant, bool isArray,
               unsigned numberOfTraces)
      : Variable(name, isConstant, isArray, numberOfTraces) {}

  ValueType type() const override { return ValueType::Bool; }
};
}  // namespace program

namespace std {
template <>
struct hash<program::Variable> {
  std::size_t operator()(program::Variable& v) const noexcept {
    return std::hash<std::string>{}(v.name);
  }
};
}  // namespace std

namespace program {

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<program::Variable>>& e);

class VariableAccess : public Expression {
 public:
  VariableAccess(std::shared_ptr<Variable> var) : Expression(), var(var) {
    assert(this->var != nullptr);
    assert(!this->var->isArray);
  }

  const std::shared_ptr<Variable> var;

  ValueType type() const override { return var->type(); }

  std::string toString() const override;
};

class ArrayApplication : public Expression {
 public:
  ArrayApplication(std::shared_ptr<Variable> array,
                   std::shared_ptr<Expression> index)
      : array(std::move(array)), index(std::move(index)) {
    assert(this->array != nullptr);
    assert(this->index != nullptr);
    assert(this->array->isArray);
    if (this->index->type() != ValueType::Int) {
      std::cout << "[] expected an Int as index" << std::endl;
      exit(1);
    }
  }

  const std::shared_ptr<Variable> array;
  const std::shared_ptr<Expression> index;

  ValueType type() const override { return array->type(); }

  std::string toString() const override;
};
}  // namespace program

#endif  // __ProgramVariable__
