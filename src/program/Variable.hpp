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

  // sanity-assertion: if two variables have the same name, they agree on all
  // other properties.
  bool operator==(const Variable& rhs) const {
    assert(!(name == rhs.name) ||
           (isConstant == rhs.isConstant && isArray == rhs.isArray &&
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

class IntVariableAccess : public IntExpression {
 public:
  IntVariableAccess(std::shared_ptr<const Variable> var)
      : IntExpression(), var(var) {
    assert(this->var != nullptr);
    assert(!this->var->isArray);
  }

  const std::shared_ptr<const Variable> var;

  IntExpression::Type type() const override {
    return IntExpression::Type::IntVariableAccess;
  }

  std::string toString() const override;
};

class IntArrayApplication : public IntExpression {
 public:
  IntArrayApplication(std::shared_ptr<const Variable> array,
                      std::shared_ptr<const IntExpression> index)
      : array(std::move(array)), index(std::move(index)) {
    assert(this->array != nullptr);
    assert(this->index != nullptr);
    assert(this->array->isArray);
  }

  const std::shared_ptr<const Variable> array;
  const std::shared_ptr<const IntExpression> index;

  IntExpression::Type type() const override {
    return IntExpression::Type::IntArrayApplication;
  }

  std::string toString() const override;
};
}  // namespace program

#endif  // __ProgramVariable__
