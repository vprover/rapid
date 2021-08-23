#include "Statements.hpp"
#include "SymbolDeclarations.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace program {

    unsigned Statement::additionalTimepoints = 0;

    TransformationInfo Statement::transformBlock(std::vector<std::shared_ptr<Statement>> &statements, std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {

        TransformationInfo retInfo;
        TransformationInfo transformationInfo;

        for (int i = 0; i < statements.size(); i++) {

            if (i > 0) {
                if (transformationInfo.break_conditions.size() > 0 ||
                    transformationInfo.continue_conditions.size() > 0 ||
                    transformationInfo.return_conditions.size() > 0) {

                    std::shared_ptr<Expression> skipCondition = nullptr;

                    std::vector<std::shared_ptr<program::Variable>> visible;

                    for (const auto &break_condition : transformationInfo.break_conditions) {
                        if (skipCondition.get() == nullptr) {
                            skipCondition = break_condition;
                        }
                        else {
                            skipCondition = std::make_shared<BooleanOr>(skipCondition, break_condition);
                        }
                        visible.push_back(break_condition->var);
                    }
                    for (const auto &continue_condition : transformationInfo.continue_conditions) {
                        if (skipCondition.get() == nullptr) {
                            skipCondition = continue_condition;
                        }
                        else {
                            skipCondition = std::make_shared<BooleanOr>(skipCondition, continue_condition);
                        }
                        visible.push_back(continue_condition->var);
                    }
                    for (const auto &return_condition : transformationInfo.return_conditions) {
                        if (skipCondition.get() == nullptr) {
                            skipCondition = return_condition;
                        }
                        else {
                            skipCondition = std::make_shared<BooleanOr>(skipCondition, return_condition);
                        }
                        visible.push_back(return_condition->var);
                    }

                    std::vector<std::shared_ptr<Statement>> thenStmts(statements.begin() + i, statements.end());
                    std::vector<std::shared_ptr<Statement>> elseStmts;

                    elseStmts.push_back(std::make_shared<SkipStatement>(-++additionalTimepoints));
                    locationToActiveVars[elseStmts[0]->location] = visible;

                    statements[i] = std::make_shared<IfElseStatement>(
                            -++additionalTimepoints,
                            std::move(skipCondition),
                            thenStmts,
                            elseStmts
                    );
                    retInfo.mergeBreak(transformationInfo.break_conditions);
                    retInfo.mergeContinue(transformationInfo.continue_conditions);
                    retInfo.mergeReturn(transformationInfo.return_conditions);

                    locationToActiveVars[statements[i]->location] = visible;

                    transformationInfo = statements[i]->transform(locationToActiveVars, traces);
                    break;
                }
            }

            std::shared_ptr<Statement> &statement = statements[i];
            transformationInfo = statement->transform(locationToActiveVars, traces);

            if (transformationInfo.introduced_var.get() != nullptr) {
                auto access = std::make_shared<VariableAccess>(std::move(transformationInfo.introduced_var));
                auto value = std::make_shared<BooleanConstant>(true);
                statement = std::make_shared<Assignment>(
                        -(++Statement::additionalTimepoints),
                        access, value
                );
                std::vector<std::shared_ptr<program::Variable>> visible;
                visible.push_back(access->var);
                locationToActiveVars[statement->location] = visible;
            }
        }

        retInfo.mergeBreak(transformationInfo.break_conditions);
        retInfo.mergeContinue(transformationInfo.continue_conditions);
        retInfo.mergeReturn(transformationInfo.return_conditions);

        return retInfo;
    }

    std::ostream &operator<<(std::ostream &ostr, Statement &v) {
        ostr << v.toString(0);
        return ostr;
    };

    std::string Assignment::toString(int indentation) const {
        return std::string(indentation, ' ') + lhs->toString() + " = " + rhs->toString() + " @" + location;
    }

    TransformationInfo Assignment::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        return TransformationInfo();
    }

    std::string IfElseStatement::toString(int indentation) const {
        auto s = std::string(indentation, ' ') + "if (" + condition->toString() + ") @" + location + "\n";
        s += std::string(indentation, ' ') + "{\n";
        for (const auto &statement : ifStatements) {
            s += statement->toString(indentation + 3) + "\n";
        }
        s += std::string(indentation, ' ') + "}\n";
        s += std::string(indentation, ' ') + "else\n";
        s += std::string(indentation, ' ') + "{\n";
        for (const auto &statement : elseStatements) {
            s += statement->toString(indentation + 3) + "\n";
        }
        s += std::string(indentation, ' ') + "}";
        return s;
    }

    TransformationInfo IfElseStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        TransformationInfo thenInfo = Statement::transformBlock(ifStatements, locationToActiveVars, traces);
        TransformationInfo elseInfo = Statement::transformBlock(elseStatements, locationToActiveVars, traces);

        thenInfo.mergeBreak(elseInfo.break_conditions);
        thenInfo.mergeContinue(elseInfo.continue_conditions);
        thenInfo.mergeReturn(elseInfo.return_conditions);

        return thenInfo;
    }

    std::string WhileStatement::toString(int indentation) const {
        auto s = std::string(indentation, ' ') + "while (" + condition->toString() + ") @" + location + "\n";
        s += std::string(indentation, ' ') + "{\n";
        for (const auto &statement : bodyStatements) {
            s += statement->toString(indentation + 3) + "\n";
        }
        s += std::string(indentation, ' ') + "}";
        return s;
    }

    TransformationInfo WhileStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        TransformationInfo info = Statement::transformBlock(bodyStatements, locationToActiveVars, traces);
        std::shared_ptr<Expression> newCondition = condition;

        for (const auto &break_condition : info.break_conditions) {
            newCondition = std::make_shared<BooleanAnd>(condition, std::make_shared<BooleanNot>(break_condition));
        }
        for (const auto &return_condition : info.return_conditions) {
            newCondition = std::make_shared<BooleanAnd>(condition, std::make_shared<BooleanNot>(return_condition));
        }

        condition = newCondition;
        info.break_conditions.clear();
        info.continue_conditions.clear();

        return info;
    }

    std::string BreakStatement::toString(int indentation) const {
        return std::string(indentation, ' ') + "break @" + location;
    }

    TransformationInfo BreakStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        TransformationInfo info;
        std::string name = "break_" + location;
        std::shared_ptr<Variable> variable = std::make_shared<BoolVariable>(name, false, false, traces);
        info.break_conditions.push_back(std::make_shared<VariableAccess>(variable));
        info.introduced_var = std::move(variable);
        declareSymbolForProgramVar(info.introduced_var.get());
        return info;
    }

    std::string ContinueStatement::toString(int indentation) const {
        return std::string(indentation, ' ') + "continue @" + location;
    }

    TransformationInfo ContinueStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        TransformationInfo info;
        std::string name = "continue_" + location;
        std::shared_ptr<Variable> variable = std::make_shared<BoolVariable>(name, false, false, traces);
        info.continue_conditions.push_back(std::make_shared<VariableAccess>(variable));
        info.introduced_var = std::move(variable);
        declareSymbolForProgramVar(info.introduced_var.get());
        return info;
    }

    std::string ReturnStatement::toString(int indentation) const {
        return std::string(indentation, ' ') + "return " + returnValue->toString() + " @" + location;
    }

    TransformationInfo ReturnStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        TransformationInfo info;
        std::string name = "return_" + location;
        std::shared_ptr<Variable> variable = std::make_shared<BoolVariable>(name, false, false, traces);
        info.return_conditions.push_back(std::make_shared<VariableAccess>(variable));
        info.introduced_var = std::move(variable);
        declareSymbolForProgramVar(info.introduced_var.get());
        return info;
    }

    std::string SkipStatement::toString(int indentation) const {
        return std::string(indentation, ' ') + "skip @" + location;
    }

    TransformationInfo SkipStatement::transform(std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> &locationToActiveVars, unsigned traces) {
        return TransformationInfo();
    }

    // hack needed for bison: std::vector has no overload for ostream, but these overloads are needed for bison
    std::ostream &operator<<(std::ostream &ostr, const std::vector<std::shared_ptr<program::Statement>> &e) {
        ostr << "not implemented";
        return ostr;
    }
}
}  // namespace program
