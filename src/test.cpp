#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#include <filesystem>

#include "logic/Theory.hpp"

#include "program/Program.hpp"

#include "util/Options.hpp"
#include "util/Output.hpp"

#include "parser/WhileParserWrapper.hpp"

#include "analysis/Semantics.hpp"
#include "analysis/TraceLemmas.hpp"
#include "analysis/TheoryAxioms.hpp"

int main(int argc, char *argv[]) {

    std::filesystem::path testDir = std::filesystem::current_path();
    testDir /= "examples";

    int iteration = 0;

    for (const auto &dirEntry : std::filesystem::recursive_directory_iterator(testDir)) {
        if (!dirEntry.is_regular_file()) {
            continue;
        }
        if (dirEntry.path().extension().string() != ".spec" || dirEntry.path().string().find("experiments") != std::string::npos) {
            std::cout << "\nSkipping: " << dirEntry.path().string() << "\n" << std::endl;
            continue;
        }
        iteration++;

        std::cout << "\nTranslating (#" << iteration << "): " << dirEntry.path().string() << "\n" << std::endl;

        std::string input = dirEntry.path().string();

        for (int i = 0; i < 2; i++) {

            std::string output = dirEntry.path().stem().string() + "_";

            if ((i % 2) == 0) {
                std::cout << "\n[Inlining]\n" << std::endl;
                output += "inline_";
            }
            else {
                std::cout << "\n[Not Inlining]\n" << std::endl;
                output += "noinline_";
            }

            char *params[] = {(char *) "", (char *) "-overwriteExisting", (char *) "on", (char *) "-inlineSemantics", (char *) ((i % 2) == 0 ? "on" : "off"), (char *) "-dir", &output[0], &input[0]};
            util::Configuration::instance().setAllValues(std::extent<decltype(params)>::value, params);

            yylex_destroy(); // reset flex
            yyset_lineno(1);
            loc.initialize();
            logic::Signature::reset(); // reset signatures

            if (util::Output::initialize()) {
                // parse inputFile
                parser::WhileParserResult parserResult = parser::parse(dirEntry.path().string());

                // setup outputDir
                std::string outputDir = util::Configuration::instance().outputDir();

                // generate problem
                std::vector<std::shared_ptr<const logic::ProblemItem>> problemItems;

                analysis::TheoryAxioms theoryAxiomsGenerator;
                std::vector<std::shared_ptr<const logic::Axiom>> theoryAxioms = theoryAxiomsGenerator.generate();
                for (const auto &axiom : theoryAxioms) {
                    problemItems.push_back(axiom);
                }

                analysis::Semantics s(*parserResult.program, parserResult.locationToActiveVars, parserResult.problemItems, parserResult.numberOfTraces);
                auto[semantics, inlinedVarValues] = s.generateSemantics();
                problemItems.insert(problemItems.end(), semantics.begin(), semantics.end());

                auto traceLemmas = analysis::generateTraceLemmas(*parserResult.program, parserResult.locationToActiveVars, parserResult.numberOfTraces, semantics, inlinedVarValues);
                problemItems.insert(problemItems.end(), traceLemmas.begin(), traceLemmas.end());

                problemItems.insert(problemItems.end(), parserResult.problemItems.begin(), parserResult.problemItems.end());

                logic::Problem problem(problemItems);

                // generate reasoning tasks, convert each reasoning task to smtlib, and output it to output-file
                std::vector<logic::ReasoningTask> tasks = problem.generateReasoningTasks();
                for (const auto &task : tasks) {
                    std::stringstream preamble;
                    preamble << util::Output::comment << *parserResult.program << util::Output::nocomment;
                    task.outputSMTLIBToDir(outputDir, preamble.str());
                }
            }
        }
    }
    // Hope no assertion was violated till here (does not test that the translation is correct but only that there is no problem during translation!)
    return 0;
}
