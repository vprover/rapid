#include "WhileParsingContext.hpp"

#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <cassert>

namespace parser {
    bool WhileParsingContext::pushQuantifiedVars(std::vector<std::shared_ptr<const logic::Symbol>> quantifiedVars) {
        // TODO: later check that those don't exist yet.
        // insert each var into into map
        for (const auto &quantifiedVar : quantifiedVars) {
            if (quantifiedVarsDeclarations.count(quantifiedVar->name) > 0) {
                return false;
            }
            quantifiedVarsDeclarations[quantifiedVar->name] = quantifiedVar;
        }
        // push new level onto stack
        std::vector<std::string> quantifiedVarNames;
        for (const auto &quantifiedVar : quantifiedVars) {
            quantifiedVarNames.push_back(quantifiedVar->name);
        }
        quantifiedVarsStack.push_back(quantifiedVarNames);

        return true;
    }

    void WhileParsingContext::popQuantifiedVars() {
        // remove each var of last level from map
        for (const auto &quantifiedVarName : quantifiedVarsStack.back()) {
            quantifiedVarsDeclarations.erase(quantifiedVarName);
        }
        // pop last level
        quantifiedVarsStack.pop_back();
    }

    bool WhileParsingContext::isDeclared(std::string name) {
        return logic::Signature::isDeclared(name) || (quantifiedVarsDeclarations.count(name) > 0);
    }

    std::shared_ptr<const logic::Symbol> WhileParsingContext::fetch(std::string name) {
        if (quantifiedVarsDeclarations.count(name) > 0) {
            return quantifiedVarsDeclarations[name];
        }
        return logic::Signature::fetch(name);
    }

    void WhileParsingContext::pushProgramVars() {
        programVarsStack.push_back({});
    }

    void WhileParsingContext::popProgramVars() {
        // remove each var of last level from map
        for (const auto &programVarName : programVarsStack.back()) {
            programVarsDeclarations.erase(programVarName);
        }
        // pop last level
        programVarsStack.pop_back();
    }

    bool WhileParsingContext::addProgramVar(std::shared_ptr<program::Variable> programVar) {
        if (programVarsDeclarations.count(programVar->name) > 0) {
            return false;
        }
        programVarsDeclarations[programVar->name] = programVar;
        programVarsStack.back().push_back(programVar->name);

        return true;
    }

    std::shared_ptr<program::Variable> WhileParsingContext::getProgramVar(std::string name) {
        if (programVarsDeclarations.count(name) > 0) {
            return programVarsDeclarations[name];
        }
        else {
            std::cout << "program var " << name << " has not been declared!";
            assert(false);
            return nullptr;
        }
    }

    std::vector<std::shared_ptr<program::Variable>> WhileParsingContext::getActiveProgramVars() {
        // sort active vars so that nonArrayVars occur before arrayVars
        std::vector<std::shared_ptr<program::Variable>> activeVars;
        std::vector<std::shared_ptr<program::Variable>> activeArrayVars;
        for (auto &pairNameVar : programVarsDeclarations) {
            auto var = pairNameVar.second;
            if (!var->isArray) {
                activeVars.push_back(var);
            }
            else {
                activeArrayVars.push_back(var);
            }
        }
        activeVars.insert(activeVars.end(), activeArrayVars.begin(), activeArrayVars.end());

        return activeVars;
    }

# pragma mark enclosingLoops

    void WhileParsingContext::addEnclosingLoops(const program::Function &function) {
        for (const auto &statement : function.statements) {
            addEnclosingLoopsForStatement(statement.get(), {});
        }
    }

    void WhileParsingContext::addEnclosingLoopsForStatement(program::Statement *statement, std::vector<program::WhileStatement *> enclosingLoops) {
        *statement->enclosingLoops = enclosingLoops;

        if (typeid(*statement) == typeid(program::IfElseStatement)) {
            auto castedStatement = static_cast<program::IfElseStatement *>(statement);
            for (const auto &statementInBranch : castedStatement->ifStatements) {
                addEnclosingLoopsForStatement(statementInBranch.get(), enclosingLoops);
            }
            for (const auto &statementInBranch : castedStatement->elseStatements) {
                addEnclosingLoopsForStatement(statementInBranch.get(), enclosingLoops);
            }
        }
        else if (typeid(*statement) == typeid(program::WhileStatement)) {
            auto castedStatement = static_cast<program::WhileStatement *>(statement);

            auto enclosingLoopsCopy = enclosingLoops;
            enclosingLoopsCopy.push_back(castedStatement);
            for (const auto &bodyStatement : castedStatement->bodyStatements) {
                addEnclosingLoopsForStatement(bodyStatement.get(), enclosingLoopsCopy);
            }
        }
    }
}
