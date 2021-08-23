#ifndef __Program__
#define __Program__

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "Statements.hpp"

namespace program {
    class Function {
    public:
        Function(std::string name,
                 std::vector<std::shared_ptr<Statement>> statements)
                : name(name), statements(std::move(statements)) {
            // TODO: add a skip-statement instead, maybe already during parsing (challenge: unique numbering)
            assert(this->statements.size() > 0);
        }

        const std::string name;
        std::vector<std::shared_ptr<Statement>> statements;
    };

    std::ostream &operator<<(std::ostream &ostr, const Function &f);

    class Program {
    public:
        Program(std::vector<std::shared_ptr<Function>> functions) : functions(std::move(functions)) {
            // TODO: enforce that one of the functions is called main
            assert(this->functions.size() > 0);
            bool containsMain = false;
            for (std::shared_ptr<Function> function : this->functions) {
                if (function->name == "main") {
                    containsMain = true;
                    break;
                }
            }
            assert(containsMain);
        }

        std::vector<std::shared_ptr<Function>> functions;
    };

    std::ostream &operator<<(std::ostream &ostr, const Program &p);
}

#endif
