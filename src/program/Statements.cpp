#include "Statements.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace program {
std::ostream& operator<<(std::ostream& ostr, const Statement& v) {
  ostr << v.toString(0);
  return ostr;
};

    std::string Assignment::toString(int indentation) const
    {
        return std::string(indentation, ' ') + lhs->toString() + " = " + rhs->toString() + " @" + location;
    }

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const program::Statement>>& e) {
  ostr << "not implemented";
  return ostr;
}
}  // namespace program
