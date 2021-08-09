/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "Options.hpp"

namespace program {

    std::string VariableAccess::toString() const
    {
        return var->name;
    }

    std::string ArrayApplication::toString() const
    {
        return array->name + "[" + index->toString() + "]";
    }
}

std::string IntVariableAccess::toString() const { return var->name; }

std::string IntArrayApplication::toString() const {
  return array->name + "[" + index->toString() + "]";
}
}  // namespace program
