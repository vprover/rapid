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

    enum VariableType
    {
        INTEGER,
        NAT,
        ARRAY,
        POINTER
    };

    class VarType
    {
    public:
        VarType(VariableType vt) : 
            vt(vt) {}
        virtual ~VarType() {}

        //virtual std::string toString();
        program::VariableType type() const { return vt; };

    private:
        program::VariableType vt;
    };

    class PointerVarType
       : public VarType
    {
    public:
        PointerVarType(std::shared_ptr<const VarType> child) : 
            VarType(program::VariableType::POINTER),
            child(std::move(child)) {}
        ~PointerVarType() {}

        const std::shared_ptr<const VarType> child;
        //virtual std::string toString();
    };
    
    class Variable
    {
    public:
        Variable(std::string name, bool isConstant, 
                 std::shared_ptr<const VarType> vt, 
                 unsigned numberOfTraces) : 
                   name(name), 
                   isConstant(isConstant), 
                   vt(std::move(vt)), 
                   numberOfTraces(numberOfTraces) {}

        const std::string name;
        const bool isConstant;
        const unsigned numberOfTraces;
        const std::shared_ptr<const VarType> vt;

        bool isPointer() const {
          return vt->type() == program::VariableType::POINTER;
        }

        bool isArray() const {
            return vt->type() == program::VariableType::ARRAY;
        }

        bool isNat() const {
            return vt->type() == program::VariableType::NAT;
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
            assert(this->var->vt->type() == program::VariableType::INTEGER ||
                   this->var->vt->type() == program::VariableType::NAT);
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
            assert(this->array->vt->type() == program::VariableType::ARRAY);
        }
        
        const std::shared_ptr<const Variable> array;
        const std::shared_ptr<const IntExpression> index;
        
        program::Type type() const override {return program::Type::IntArrayApplication;}

        std::string toString() const override;
    };

    class PointerVariableAccess : public PointerExpression
    {
    public:
        PointerVariableAccess(std::shared_ptr<const Variable> var) : var(var)
        {
            assert(this->var != nullptr);
            assert(this->var->vt->type() == program::VariableType::POINTER);
        }

        const std::shared_ptr<const Variable> var;
        
        program::Type type() const override {return program::Type::PointerVariableAccess;}

        std::string toString() const override;
    };

    class DerefExpression : public PointerExpression
    {
    public:
        DerefPointerExpression(std::shared_ptr<const Variable> var) : var(var)
        {
            assert(this->var != nullptr);
            assert(this->var->vt->type() == program::VariableType::POINTER);
            assert(static_pointer_cast<const program::PointerVarType>(this->var->vt)->child->type() == program::VariableType::POINTER);
        }

        program::Type type() const override {return program::Type::PointerDeref;}

        std::string toString() const override;
    }

    class VarReference : public PointerExpression
    {
    public:
        VarReference(std::shared_ptr<const Variable> var) : referent(var){}

        const std::shared_ptr<const Variable> referent;
        
        program::Type type() const override {return program::Type::VarReference;}

        std::string toString() const override;
    };
}

#endif // __ProgramVariable__
