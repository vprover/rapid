#ifndef __WhileParsingContext__
#define __WhileParsingContext__

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "Formula.hpp"
#include "Problem.hpp"
#include "Program.hpp"
#include "Signature.hpp"
#include "Variable.hpp"

namespace parser {
    /*
     * this class is used to communicate with the bison-parser, in particular to
     * get back the parsed program.
     * furthermore it contains the context-information, which Bison's LALR parser doesn't support
     */
    class WhileParsingContext {
    public:
        WhileParsingContext() : inputFile(""), errorFlag(false), program(nullptr), problemItems(), locationToActiveVars(), numberOfTraces(1), numberOfAxioms(0), numberOfLemmas(0), numberOfConjectures(0),
            quantifiedVarsDeclarations(), quantifiedVarsStack(), programVarsDeclarations(), programVarsStack() {}

        // input
        std::string inputFile;
        bool errorFlag;

        // output
        std::unique_ptr<program::Program> program;
        std::vector<std::shared_ptr<const logic::ProblemItem>> problemItems;
        std::unordered_map<std::string, std::vector<std::shared_ptr<program::Variable>>> locationToActiveVars;
        unsigned numberOfTraces;
        int numberOfAxioms;
        int numberOfLemmas;
        int numberOfConjectures;

    private:
        // context-information
        std::unordered_map<std::string, std::shared_ptr<const logic::Symbol>> quantifiedVarsDeclarations;
        std::vector<std::vector<std::string>> quantifiedVarsStack;

        std::unordered_map<std::string, std::shared_ptr<program::Variable>> programVarsDeclarations;
        std::vector<std::vector<std::string>> programVarsStack;

    public:
        // methods which are called by bison to interact with the context
        bool pushQuantifiedVars(std::vector<std::shared_ptr<const logic::Symbol>> quantifiedVars);

        void popQuantifiedVars();

        bool isDeclared(std::string name);

        std::shared_ptr<const logic::Symbol> fetch(std::string name); // fetch symbol with given name from quantVarDecls or Signature.

        void pushProgramVars();

        void popProgramVars();

        bool addProgramVar(std::shared_ptr<program::Variable> programVar);

        std::shared_ptr<program::Variable> getProgramVar(std::string name);

        std::vector<std::shared_ptr<program::Variable>> getActiveProgramVars();

        /*
         * we need to know for each statement in which loops it is nested in.
         * we compute this information at the end of parsing each function.
         * the enclosingLoops are added directly to each statement.
         * note that we can't add the enclosing loops on the fly, since the
         * enclosing loop is only constructed after the statement is constructed.
         */
    public:
        void addEnclosingLoops(const program::Function &function);

    private:
        static void addEnclosingLoopsForStatement(program::Statement *statement,
                                                  std::vector<program::WhileStatement *> enclosingLoops);
    };
}

#endif
