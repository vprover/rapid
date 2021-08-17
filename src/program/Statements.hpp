#ifndef __Assignment__
#define __Assignment__

#include "Expression.hpp"
#include "Variable.hpp"

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <cassert>

namespace program
{
    class WhileStatement;
    class Statement
    {
    public:
        Statement(unsigned lineNumber) :
            location("l" + std::to_string(lineNumber != 0 ? lineNumber : -(++Statement::additionalTimepoints))),
            enclosingLoops(std::make_unique<std::vector<const WhileStatement*>>()) {}

        virtual ~Statement() {}
        
        const std::string location;
        /*
         * enclosingLoops can only be computed after all enclosing loops are constructed, and
         * the implementation only constructs them immediately after the whole function
         * is constructed in the parser. This field can therefore only be used afterwards.
         * Since enclosingLoops can't be computed at construction time, we need our programs
         * to be constant only up to the enclosingLoop-field.
         * we achieve this by using indirection: constness is not transitive in c++,
         * so we get a (constant) pointer to a (not necessarily constant) vector enclosingLoops,
         * which we can fill up in the parser-post-computation.
         */
        std::unique_ptr<std::vector<const WhileStatement*>> enclosingLoops;

        virtual std::string toString(int indentation) const = 0;

        static unsigned additionalTimepoints; // Will be incremented and used negated (counts from down)
    };
    
    struct StatementSharedPtrHash
    {
        size_t operator()(const std::shared_ptr<const Statement>& ptr) const {return std::hash<std::string>()(ptr->location); }
    };
    
    std::ostream& operator<<(std::ostream& ostr, const Statement& v);

    // hack needed for bison: std::vector has no overload for ostream, but these overloads are needed for bison
    std::ostream& operator<<(std::ostream& ostr, const std::vector< std::shared_ptr<const program::Statement>>& e);
    
    class Assignment : public Statement
    {
    public:
        
        Assignment(unsigned lineNumber, std::shared_ptr<const Expression> lhs, std::shared_ptr<const Expression> rhs) : Statement(lineNumber), lhs(std::move(lhs)), rhs(std::move(rhs)){}
        
        const std::shared_ptr<const Expression> lhs;
        const std::shared_ptr<const Expression> rhs;
        
        std::string toString(int indentation) const override;
    };

    class IfElseStatement : public Statement
    {
    public:
        
        IfElseStatement(unsigned lineNumber, std::shared_ptr<const Expression> condition, std::vector<std::shared_ptr<const Statement>> ifStatements, std::vector<std::shared_ptr<const Statement>> elseStatements) : Statement(lineNumber), condition(std::move(condition)), ifStatements(std::move(ifStatements)), elseStatements(std::move(elseStatements))
        {
            assert(this->ifStatements.size() > 0);
            assert(this->elseStatements.size() > 0);

            if (this->condition->type() != ValueType::Bool) {
                std::cout << "if-condition expected a Bool as condition" << std::endl;
                exit(1);
            }
        }
        
        const std::shared_ptr<const Expression> condition;
        const std::vector<std::shared_ptr<const Statement>> ifStatements;
        const std::vector<std::shared_ptr<const Statement>> elseStatements;
        
        std::string toString(int indentation) const override;
    };
    
    class WhileStatement : public Statement
    {
    public:
        
        WhileStatement(unsigned lineNumber, std::shared_ptr<const Expression> condition, std::vector<std::shared_ptr<const Statement>> bodyStatements) : Statement(lineNumber), condition(std::move(condition)), bodyStatements(std::move(bodyStatements))
        {
            // TODO: add a skip-statement instead, maybe already during parsing (challenge: unique numbering)
            assert(this->bodyStatements.size() > 0);

            if (this->condition->type() != ValueType::Bool) {
                std::cout << "while-condition expected a Bool as condition" << std::endl;
                exit(1);
            }
        }

        const std::shared_ptr<const Expression> condition;
        const std::vector<std::shared_ptr<const Statement>> bodyStatements;
        
        std::string toString(int indentation) const override;
    };

    class BreakStatement : public Statement {
    public:
        BreakStatement(unsigned lineNumber) : Statement(lineNumber) {};

        std::string toString(int indentation) const override;
    };

    class ContinueStatement : public Statement {
    public:
        ContinueStatement(unsigned lineNumber) : Statement(lineNumber) {};

        std::string toString(int indentation) const override;
    };

    class ReturnStatement : public Statement {
    public:
        ReturnStatement(unsigned lineNumber, std::shared_ptr<const Expression> returnValue) : Statement(lineNumber), returnValue(std::move(returnValue)) {};

        std::string toString(int indentation) const override;

        const std::shared_ptr<const Expression> returnValue;
    };
    
    class SkipStatement : public Statement
    {
    public:
        SkipStatement(unsigned lineNumber) : Statement(lineNumber) {};
        
        std::string toString(int indentation) const override;
    };
}



#endif
