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

    enum BasicType
    {
        INTEGER,
        NAT,
        ARRAY,
        POINTER
    };

    class ExprType
    {
    public:
        ExprType(BasicType vt) : 
            vt(vt) {}
        virtual ~ExprType() {}


        virtual std::shared_ptr<const ExprType> getChild() const
        {return std::shared_ptr<const ExprType>(this); }
        //virtual std::string toString();
        program::BasicType type() const { return vt; };

    private:
        program::BasicType vt;
    };

    class PointerExprType
       : public ExprType
    {
    public:
        PointerExprType(std::shared_ptr<const ExprType> child) : 
            ExprType(program::BasicType::POINTER),
            child(std::move(child)) {}
        ~PointerExprType() {}

        virtual std::shared_ptr<const ExprType> getChild() const
        { return child; }

        const std::shared_ptr<const ExprType> child;
        //virtual std::string toString();
    };
    
    class Variable
    {
    public:
        Variable(std::string name, bool isConstant, 
                 std::shared_ptr<const ExprType> vt, 
                 unsigned numberOfTraces) : 
                   name(name), 
                   isConstant(isConstant), 
                   vt(std::move(vt)), 
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
                                                             vt->type()    == rhs.vt->type() &&
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
        
        program::Type type() const override {return program::Type::IntArrayApplication;}

        std::string toString() const override;
    };

    class PointerExpression : public Expression
    {
    public:
        PointerExpression(std::shared_ptr<const ExprType> type) 
                        : type(type) 
        {
            assert(type->type() == program::BasicType::POINTER);            
        }

      const std::shared_ptr<const ExprType> type;
    };
    std::ostream& operator<<(std::ostream& ostr, const IntExpression& e);

    class DerefP2IExpression : public IntExpression
    {
    public:
        DerefP2IExpression(std::shared_ptr<const PointerExpression> expr) : expr(expr)
        {
            assert(this->expr != nullptr);
            assert(this->expr->type->type() == program::BasicType::POINTER);
            assert(expr->type->getChild()->type() == program::BasicType::INTEGER);
        }

        const std::shared_ptr<const PointerExpression> expr;

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
        
        program::Type type() const override {return program::Type::PointerVariableAccess;}

        std::string toString() const override;
    };

    class DerefP2PExpression : public PointerExpression
    {
    public:
        DerefP2PExpression(std::shared_ptr<const PointerExpression> expr) 
        : PointerExpression(expr->type->getChild()), expr(expr)
        {
            assert(this->expr != nullptr);
            assert(expr->type->getChild()->type() == program::BasicType::POINTER);
        }

        const std::shared_ptr<const PointerExpression> expr;

        program::Type type() const override {return program::Type::PointerDeref;}

        std::string toString() const override;
    };

    class VarReference : public PointerExpression
    {
    public:
        VarReference(std::shared_ptr<const Variable> var) 
        : PointerExpression(std::shared_ptr<const program::PointerExprType>(new PointerExprType(var->vt))), 
          referent(var){}

        const std::shared_ptr<const Variable> referent;
        
        program::Type type() const override {return program::Type::VarReference;}

        std::string toString() const override;
    };
}

#endif // __ProgramVariable__
