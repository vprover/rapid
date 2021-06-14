/**
 *
 * @file Variable.hpp
 *
 * Program variables (and variables coming from assertion quantifiers)
 */

#ifndef __ProgramVariable__
#define __ProgramVariable__

#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <cassert>
#include <functional>
#include <cstddef>

#include "Expression.hpp"

namespace program {
    
    class Variable
    {
    public:
        Variable(std::string name, bool isConstant, 
                 std::shared_ptr<const ExprType> vt, 
                 unsigned numberOfTraces) : 
                   name(name), 
                   isConstant(isConstant), 
                   vt(vt), 
                   numberOfTraces(numberOfTraces) {}

        const std::string name;
        const bool isConstant;
        const unsigned numberOfTraces;
        const std::shared_ptr<const ExprType> vt;

        bool isPointer() const {
            return vt->type() == program::BasicType::POINTER;
        }

        bool isArray() const {
            return vt->type() == program::BasicType::ARRAY;
        }

        bool isNat() const {
            return vt->type() == program::BasicType::NAT;
        }

        // sanity-assertion: if two variables have the same name, they agree on all other properties.
        bool operator==(const Variable& rhs) const { assert( !(name == rhs.name) ||
                                                            (isConstant == rhs.isConstant &&
                                                             *vt  == *rhs.vt &&
                                                             numberOfTraces  == rhs.numberOfTraces)); return (name == rhs.name); }
        bool operator!=(const Variable& rhs) const { return !operator==(rhs); }
    };
}

namespace std
{
    template<>
    struct hash<program::Variable>
    {
        std::size_t operator()(const program::Variable& v) const noexcept
        {
            return std::hash<std::string>{}(v.name);
        }
    };
}

namespace program {

    // hack needed for bison: std::vector has no overload for ostream, but these overloads are needed for bison
    std::ostream& operator<<(std::ostream& ostr, const std::vector< std::shared_ptr<const program::Variable>>& e);
    
    class IntOrNatVariableAccess : public IntExpression
    {
    public:
        IntOrNatVariableAccess(std::shared_ptr<const Variable> var) : IntExpression(), var(var)
        {
            assert(this->var != nullptr);
            assert(this->var->vt->type() == program::BasicType::INTEGER ||
                   this->var->vt->type() == program::BasicType::NAT);
        }
        
        const std::shared_ptr<const Variable> var;

        bool isConstVar() const override { return var->isConstant; };

        program::Type type() const override {return program::Type::IntOrNatVariableAccess;}
        
        std::string toString() const override;
    };

    class IntArrayApplication : public IntExpression
    {
    public:
        IntArrayApplication(std::shared_ptr<const Variable> array, std::shared_ptr<const IntExpression> index) : array(std::move(array)), index(std::move(index))
        {
            assert(this->array != nullptr);
            assert(this->index != nullptr);
            assert(this->array->vt->type() == program::BasicType::ARRAY);
        }
        
        const std::shared_ptr<const Variable> array;
        const std::shared_ptr<const IntExpression> index;
        
        bool isConstVar() const override { return array->isConstant; };

        program::Type type() const override {return program::Type::IntArrayApplication;}

        std::string toString() const override;
    };

    class PointerExpression : public Expression
    {
    public:
        PointerExpression(std::shared_ptr<const ExprType> type) 
        {
            exprtype = type;
            assert(type->type() == program::BasicType::POINTER);            
        }

        virtual bool isPointerExpr() const override { return true; }
    };
    std::ostream& operator<<(std::ostream& ostr, const IntExpression& e);

    class DerefP2IExpression : public IntExpression
    {
    public:
        DerefP2IExpression(std::shared_ptr<const PointerExpression> expr) : expr(expr)
        {
            assert(expr != nullptr);
            assert(expr->exprType()->type() == program::BasicType::POINTER);
            assert(expr->exprType()->getChild()->type() == program::BasicType::INTEGER);
        }
 
        const std::shared_ptr<const PointerExpression> expr;

        bool containsReference() const override { return expr->containsReference(); }

        program::Type type() const override {return program::Type::PointerDeref;}

        std::string toString() const override;
    };

    class PointerVariableAccess : public PointerExpression
    {
    public:
        PointerVariableAccess(std::shared_ptr<const Variable> var) 
        : PointerExpression(var->vt), var(var)
        {
            assert(this->var != nullptr);
            assert(this->var->vt->type() == program::BasicType::POINTER);
        }

        const std::shared_ptr<const Variable> var;

        bool isConstVar() const override { return var->isConstant; };
        
        program::Type type() const override {return program::Type::PointerVariableAccess;}

        std::string toString() const override;
    };

    class DerefP2PExpression : public PointerExpression
    {
    public:
        DerefP2PExpression(std::shared_ptr<const PointerExpression> expr) 
        : PointerExpression(expr->exprType()->getChild()), expr(expr)
        {
            assert(expr != nullptr);
            assert(expr->exprType()->getChild()->type() == program::BasicType::POINTER);
        }

        const std::shared_ptr<const PointerExpression> expr;

        virtual bool containsReference() const override { return expr->containsReference(); }

        program::Type type() const override {return program::Type::PointerDeref;}

        std::string toString() const override;
    };

    class VarReference : public PointerExpression
    {
    public:
        VarReference(std::shared_ptr<const Expression> expr) 
        : PointerExpression(std::shared_ptr<const program::ExprType>(new ExprType(expr->exprType()))), 
          referent(expr)
        {
     //       assert(this->referent->type() ==  program::Type::PointerVariableAccess);            
        }

        const std::shared_ptr<const Expression> referent;

        bool containsReference() const override { return true; }
        
        program::Type type() const override {return program::Type::VarReference;}

        std::string toString() const override;
    };
}

#endif // __ProgramVariable__
