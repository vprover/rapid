/**
 * @file Expression.hpp
 *
 * Defines class Program::Expression, representing expressions in the
 * guarded command language
 *
 */

#ifndef __ProgramExpression__
#define __ProgramExpression__

#include <iostream>
#include <memory>
#include <string>
#include <utility>

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
        ExprType(BasicType bt) : bt(bt) {}
        ExprType(std::shared_ptr<const ExprType> child) : 
            bt(program::BasicType::POINTER),
            child(child) {}
        ~ExprType() {}


        std::shared_ptr<const ExprType> getChild() const { return child; }
        std::string toString() const {
            if(bt == BasicType::POINTER){
                return "->" + child->toString();
            } else if(bt == BasicType::INTEGER){
                return "Int";
            } else if(bt == BasicType::ARRAY){
                return "Arr";
            } else {
                return "Nat";
            }
        }
        program::BasicType type() const { return bt; };

        //recursive equality def
        bool operator==(const ExprType &other) const {
            return other.bt == bt && (other.child == child || *child == *other.child);
        }

        bool operator!=(const ExprType &other) const {
            return !(*this == other);
        }

    private:
        const std::shared_ptr<const ExprType> child;
        program::BasicType bt;
    };

    enum class Type
    {
        ArithmeticConstant,
        Addition,
        Subtraction,
        Modulo,
        Multiplication,
        IntOrNatVariableAccess,
        PointerVariableAccess,
        PointerDeref,
        IntArrayApplication,
        VarReference,
    };

    class Expression
    {
    public:
        virtual ~Expression() {}
        
        virtual bool isPointerExpr() const = 0; 

        virtual bool containsReference() const { return false; }

        virtual bool isConstVar() const { return false; }
   
        virtual Type type() const = 0;
        
        virtual std::string toString() const = 0;

        virtual const std::shared_ptr<const ExprType> exprType() const { return exprtype; }

    protected:
        std::shared_ptr<const ExprType> exprtype;
    };

    class IntExpression : public Expression
    {
    public:
        IntExpression() {
            exprtype = std::shared_ptr<const ExprType>(new ExprType(program::BasicType::INTEGER));
        }
        virtual bool isPointerExpr() const override { return false; }
    };
    std::ostream& operator<<(std::ostream& ostr, const IntExpression& e);


    class ArithmeticConstant : public IntExpression
    {
    public:
        ArithmeticConstant(unsigned value) : value(value){}
        
        const int value;
        
        Type type() const override { return program::Type::ArithmeticConstant; }
        std::string toString() const override;
    };
    
    class Addition : public IntExpression
    {
    public:
        Addition(std::shared_ptr<const IntExpression> summand1, std::shared_ptr<const IntExpression> summand2)
        : summand1(std::move(summand1)), summand2(std::move(summand2)){}
        
        const std::shared_ptr<const IntExpression> summand1;
        const std::shared_ptr<const IntExpression> summand2;
        
        Type type() const override { return program::Type::Addition; }
        std::string toString() const override;
    };

    class Subtraction : public IntExpression
    {
    public:
        Subtraction(std::shared_ptr<const IntExpression> child1, std::shared_ptr<const IntExpression> child2)
        : child1(std::move(child1)), child2(std::move(child2)){}
        
        const std::shared_ptr<const IntExpression> child1;
        const std::shared_ptr<const IntExpression> child2;
        
        Type type() const override { return program::Type::Subtraction; }
        std::string toString() const override;
    };
    
    class Modulo : public IntExpression
    {
    public:
        Modulo(std::shared_ptr<const IntExpression> child1, std::shared_ptr<const IntExpression> child2)
        : child1(std::move(child1)), child2(std::move(child2)){}
        
        const std::shared_ptr<const IntExpression> child1;
        const std::shared_ptr<const IntExpression> child2;
        
        Type type() const override { return program::Type::Modulo; }
        std::string toString() const override;
    };
    
    class Multiplication : public IntExpression
    {
    public:
        Multiplication(std::shared_ptr<const IntExpression> factor1, std::shared_ptr<const IntExpression> factor2)
        : factor1(std::move(factor1)), factor2(std::move(factor2)){}

        const std::shared_ptr<const IntExpression> factor1;
        const std::shared_ptr<const IntExpression> factor2;
        
        Type type() const override { return program::Type::Multiplication; }
        std::string toString() const override;
    };


    class BoolExpression
    {
    public:
        virtual ~BoolExpression() {}

        enum class Type
        {
            BooleanConstant,
            BooleanAnd,
            BooleanOr,
            BooleanNot,
            ArithmeticComparison
        };
        virtual Type type() const = 0;
        
        virtual std::string toString() const = 0;
    };
    std::ostream& operator<<(std::ostream& ostr, const BoolExpression& e);

    class BooleanConstant : public BoolExpression
    {
    public:
        BooleanConstant(bool value) : value(value){}
        
        const bool value;
        
        Type type() const override { return BoolExpression::Type::BooleanConstant; }
        std::string toString() const override;
    };
    
    class BooleanAnd : public BoolExpression
    {
    public:
        BooleanAnd(std::shared_ptr<const BoolExpression> child1, std::shared_ptr<const BoolExpression> child2)
        : child1(std::move(child1)), child2(std::move(child2)){}

        const std::shared_ptr<const BoolExpression> child1;
        const std::shared_ptr<const BoolExpression> child2;
        
        Type type() const override { return BoolExpression::Type::BooleanAnd; }
        std::string toString() const override;
    };
    
    class BooleanOr : public BoolExpression
    {
    public:
        BooleanOr(std::shared_ptr<const BoolExpression> child1, std::shared_ptr<const BoolExpression> child2)
        : child1(std::move(child1)), child2(std::move(child2)){}
        
        const std::shared_ptr<const BoolExpression> child1;
        const std::shared_ptr<const BoolExpression> child2;
        
        Type type() const override { return BoolExpression::Type::BooleanOr; }
        std::string toString() const override;
    };
    
    class BooleanNot : public BoolExpression
    {
    public:
        BooleanNot(std::shared_ptr<const BoolExpression> child)
        : child(std::move(child)){}
        
        const std::shared_ptr<const BoolExpression> child;
        
        Type type() const override { return BoolExpression::Type::BooleanNot; }
        std::string toString() const override;
    };
    
    class ArithmeticComparison : public BoolExpression
    {
    public:
        enum class Kind {
            GE,
            GT,
            LE,
            LT,
            EQ
        };
        
        ArithmeticComparison(Kind kind, std::shared_ptr<const IntExpression> child1, std::shared_ptr<const IntExpression> child2)
        : kind(kind), child1(std::move(child1)), child2(std::move(child2)){}
        
        const Kind kind;
        const std::shared_ptr<const IntExpression> child1;
        const std::shared_ptr<const IntExpression> child2;
        
        Type type() const override { return BoolExpression::Type::ArithmeticComparison; }
        std::string toString() const override;
    };
    

}
#endif
