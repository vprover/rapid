#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "analysis/Semantics.hpp"
#include "analysis/TheoryAxioms.hpp"
#include "analysis/TraceLemmas.hpp"
#include "logic/Problem.hpp"
#include "logic/Theory.hpp"
#include "parser/WhileParserWrapper.hpp"
#include "program/Program.hpp"
#include "util/Options.hpp"
#include "util/Output.hpp"

void outputUsage() {
  std::cout
      << "Usage: rapid "
      << "-dir <outputDir> "
      << "[-inlineSemantics on|off] "
      << "[-lemmaPredicates on|off] "
      << "[-nat on|off] "
      << "[-integerIterations on|off]"
      << "[-inlineLemmas on|off]"
      << "[-postcondition on|off]"
      << "[-overwriteExisting on|off] "
      << "<filename>" << std::endl;
}

int main(int argc, char *argv[]) {
  if (argc <= 1) {
    outputUsage();
  } else {
    if (util::Configuration::instance().setAllValues(argc, argv)) {
      if (util::Output::initialize()) {
        std::string inputFile = argv[argc - 1];

        // check that inputFile ends in ".spec"
        std::string extension = ".spec";
        assert(inputFile.size() > extension.size());
        assert(inputFile.compare(inputFile.size() - extension.size(),
                                 extension.size(), extension) == 0);
        auto inputFileWithoutExtension =
            inputFile.substr(0, inputFile.size() - extension.size());

        // parse inputFile
        auto parserResult = parser::parse(inputFile);

        // setup outputDir
        auto outputDir = util::Configuration::instance().outputDir();
        if (outputDir == "") {
          std::cout << "Error: dir parameter required" << std::endl;
          exit(1);
        }

        // generate problem
        std::vector<std::shared_ptr<const logic::ProblemItem>> problemItems;

        analysis::TheoryAxioms theoryAxiomsGenerator;
        auto theoryAxioms = theoryAxiomsGenerator.generate();
        for (const auto& axiom : theoryAxioms) {
          problemItems.push_back(axiom);
        }

        analysis::Semantics::applyTransformations(parserResult.program->functions,
                                                  parserResult.locationToActiveVars,
                                                  parserResult.numberOfTraces);
        analysis::Semantics s(*parserResult.program,
                              parserResult.locationToActiveVars,
                              parserResult.problemItems,
                              parserResult.numberOfTraces);
        auto [semantics, inlinedVarValues] = s.generateSemantics();
        problemItems.insert(problemItems.end(), semantics.begin(),
                            semantics.end());

        if (util::Configuration::instance().outputTraceLemmas()) {
          
          auto traceLemmas = analysis::generateTraceLemmas(
              *parserResult.program, parserResult.locationToActiveVars,
              parserResult.numberOfTraces, semantics, inlinedVarValues);
          problemItems.insert(problemItems.end(), traceLemmas.begin(),
                              traceLemmas.end());
        } else {
          // perhaps we want to add in conjunction with trace lemmas?
          auto lemmas = analysis::generateNonTraceLemmas(
              *parserResult.program, parserResult.locationToActiveVars,
              parserResult.numberOfTraces, semantics, inlinedVarValues);
          problemItems.insert(problemItems.end(), lemmas.begin(), lemmas.end());
        }

        problemItems.insert(problemItems.end(),
                            parserResult.problemItems.begin(),
                            parserResult.problemItems.end());
        logic::Problem problem(problemItems);

        // generate reasoning tasks, convert each reasoning task to smtlib or
        // tptp, and output it to output-file
        auto tasks = problem.generateReasoningTasks();
        for (const auto& task : tasks) {
          std::stringstream preamble;
          preamble << util::Output::comment << *parserResult.program
                   << util::Output::nocomment;
          if (util::Configuration::instance().tptp()) {
            task.outputTPTPToDir(outputDir, preamble.str());
          } else {
            task.outputSMTLIBToDir(outputDir, preamble.str());
          }
        }

        if (util::Configuration::instance().postcondition()) {
          for (const auto& task : tasks) {
            if (task.conjecture.get()->name.find("user-conjecture") !=
                std::string::npos) {
              std::stringstream preamble;
              preamble << util::Output::comment << *parserResult.program
                       << util::Output::nocomment;
              task.outputTPTPToDir(outputDir, preamble.str());
            }
          }
        }
      }
    }
    return 0;
  }
}
