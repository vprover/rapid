#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "analysis/Semantics.hpp"
#include "analysis/GenerateMemConjectures.hpp"
#include "analysis/TheoryAxioms.hpp"
#include "analysis/TraceLemmas.hpp"
#include "logic/LogicProblem.hpp"
#include "logic/Theory.hpp"
#include "parser/WhileParserWrapper.hpp"
#include "program/Program.hpp"
#include "util/Options.hpp"
#include "util/Output.hpp"
#include "solvers/SolverInterface.hpp"

void outputUsage() {
  std::cout << "Usage: rapid <filename>" << std::endl;
  std::cout << "Run with -help for more detailed usage information" << std::endl;  
}

int main(int argc, char* argv[]) {
  if (argc <= 1) {
    outputUsage();
  } else {
    if (util::Output::initialize()) {
      if (util::Configuration::instance().setAllValues(argc, argv)) {
        std::string inputFile = argv[argc - 1];

        // check that inputFile ends in ".spec"
        std::string extension = ".spec";
        assert(inputFile.size() > extension.size());
        assert(inputFile.compare(inputFile.size() - extension.size(),
                                 extension.size(), extension) == 0);
        auto inputFileWithoutExtension =
            inputFile.substr(0, inputFile.size() - extension.size());
        std::string inputFileName;
        auto i = inputFileWithoutExtension.rfind('/');
        if (i != std::string::npos) {
          inputFileName = inputFileWithoutExtension.substr(
              i + 1, inputFileWithoutExtension.length() - i);
        } else {
          inputFileName = inputFileWithoutExtension;
        }

        util::Output::status("Parsing benchmark");

        // parse inputFile
        auto parserResult = parser::parse(inputFile);

        util::Output::status("Parsing successful. Translating to FOL");

        // generate problem
        std::vector<std::shared_ptr<const logic::ProblemItem>> problemItems;

        analysis::TheoryAxioms theoryAxiomsGenerator;
        auto theoryAxioms = theoryAxiomsGenerator.generate();
        for (const auto& axiom : theoryAxioms) {
          problemItems.push_back(axiom);
        }

        analysis::Semantics s(
            *parserResult.program, parserResult.locationToActiveVars,
            parserResult.problemItems, parserResult.numberOfTraces);
        auto [semantics, inlinedVarValues] = s.generateSemantics();

        problemItems.insert(problemItems.end(), semantics.begin(),
                            semantics.end());

        // When attempting to reason about memory safety, we output
        // special conjectures
        if (util::Configuration::instance().memSafetyMode()) {
          analysis::MemConjectureGenerator mcg(*parserResult.program);
          auto memSafetyConjectures = mcg.generateMemSafetyConjectures();
          problemItems.insert(problemItems.end(), memSafetyConjectures.begin(),
                             memSafetyConjectures.end()); 
        }

        auto lemmasToOutput = util::Configuration::instance().outputTraceLemmas();
        if (lemmasToOutput == "all" || lemmasToOutput == "inductive") {
          auto traceLemmas = analysis::generateTraceLemmas(
              *parserResult.program, parserResult.locationToActiveVars,
              parserResult.numberOfTraces, semantics, inlinedVarValues);
          problemItems.insert(problemItems.end(), traceLemmas.begin(),
                              traceLemmas.end());
        } 
        if (lemmasToOutput == "all" || lemmasToOutput == "dense") {
          std::cout << "about to generate non-trace lemma" << std::endl;
          auto lemmas = analysis::generateNonTraceLemmas(
              *parserResult.program, parserResult.locationToActiveVars,
              parserResult.numberOfTraces, semantics, inlinedVarValues);
          problemItems.insert(problemItems.end(), lemmas.begin(), lemmas.end());
        }

        problemItems.insert(problemItems.end(),
                            parserResult.problemItems.begin(),
                            parserResult.problemItems.end());

        logic::Problem problem(problemItems);

        // generate reasoning task. then either convert to SMT-LIB
        // and output or pass to prover via programmatic interface
        auto tasks = problem.generateReasoningTasks();

        for (auto& task : tasks) {
          std::stringstream preamble;
          preamble << util::Output::comment << *parserResult.program
                   << util::Output::nocomment;
       
          if(util::Configuration::instance().outputToFile()){
            auto outputDir = util::Configuration::instance().outputDir();
            if (util::Configuration::instance().tptp()) {
              task.outputTPTPToDir(outputDir, preamble.str());
            } else {
              task.outputSMTLIBToDir(outputDir, inputFileName, preamble.str());
            }
          } else {
            util::Output::status("Attempting to prove main conjecture\n");
            std::cout << task.conjecture->formula->prettyString() << "\n" << std::endl;
            task.setPrint(); 
            auto& solver = solvers::VampireSolver::instance();
            auto [proven, time] = solver.solveTask(task, logic::TaskType::MAIN);
            if(proven){
              std::cout << "Verification successful in time " + time + "!" << std::endl;
            } else {
              std::cout << "Verification failed. You can try adding hand crafted invariants and running again" << std::endl;              
            }
          }
        }
      }
      
      util::Output::close();
    }
    return 0;
  }
}
