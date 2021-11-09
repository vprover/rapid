#include "Problem.hpp"

#include <algorithm>
#include <ctime>
#include <fstream>

#include "Options.hpp"
#include "Output.hpp"

namespace logic {

std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const ProblemItem>>& f) {
  ostr << "not implemented";
  return ostr;
}

void ReasoningTask::outputSMTLIBToDir(std::string dirPath,
                                      std::string inputFileName,
                                      std::string preamble) const {
  std::string conjName =
      memSafetyVerification
          ? "memory-safety-verification-condition"
          : (memSafetyViolationCheck ? "memory-safety-violation-check"
                                     : conjecture->name);

  auto outfileName = dirPath + inputFileName + "-" + conjName + ".smt2";
  if (std::ifstream(outfileName)) {
    std::cout << "Error: The output-file " << outfileName << " already exists!"
              << std::endl;
    exit(1);
  }

  std::cout << "Generating reasoning task in " << outfileName << "\n";
  std::ofstream outfile(outfileName);

  if (!util::Configuration::instance().generateBenchmark()) {
    outfile << preamble;
  }

  // output task
  outputSMTLIB(outfile);
}

void ReasoningTask::outputSMTLIB(std::ostream& ostr) const {
  auto smtlibLogic = "UFDTLIA";  // uninterpreted functions, datatypes and
                                 // linear integer arithmetic

  // if encoding is used as smtlib-benchmark, add meta information
  if (util::Configuration::instance().generateBenchmark()) {
    ostr << "(set-info :smt-lib-version 2.6)\n";
    ostr << "(set-logic " << smtlibLogic << ")\n";

    std::time_t t = std::time(0);
    std::tm* now = std::localtime(&t);

    ostr << "(set-info :source |\n"
         << "Generated on: " << (now->tm_year + 1900) << "-"
         << (now->tm_mon + 1) << "-" << now->tm_mday << "\n"
         << "Generator: Rapid\n"
         << "Application: Software Verification\n"
         << "Target solver: Vampire\n"
         << "|)\n"
         << "(set-info :license "
            "\"https://creativecommons.org/licenses/by/4.0/\")\n"
         << "(set-info :category crafted)\n"
         << "(set-info :status unknown)\n\n";
  } else {
    ostr << "\n(set-logic " << smtlibLogic << ")\n\n";
  }

  // output sort declarations
  for (const auto& pair : Sorts::nameToSort()) {
    ostr << declareSortSMTLIB(*pair.second);
  }

  // output symbol definitions
  for (const auto& symbol : Signature::signatureOrderedByInsertion()) {
    ostr << symbol->declareSymbolSMTLIB();
  }

  // output each axiom
  for (const auto& axiom : axioms) {
    assert(axiom->type == ProblemItem::Type::Lemma ||
           axiom->type == ProblemItem::Type::Axiom ||
           axiom->type == ProblemItem::Type::Definition);
    if (axiom->name != "") {
      ostr << "\n; "
           << (axiom->type == ProblemItem::Type::Axiom ? "Axiom: "
                                                       : "Definition: ")
           << axiom->name;
    }
    ostr << "\n(assert\n" << axiom->formula->toSMTLIB(3) + "\n)\n";
  }

  // output conjecture
  assert(conjecture != nullptr);

  // if benchmark is used as smtlib-benchmark, replace (assert-not F) by (assert
  // (not F))
  if (util::Configuration::instance().generateBenchmark()) {
    ostr << "\n; negated conjecture\n"
         << "(assert\n"
         << "   (not\n"
         << conjecture->formula->toSMTLIB(6) << "\n"
         << "   )\n"
         << ")\n";
  } else {
    if (conjecture->name != "") {
      ostr << "\n; Conjecture: " << conjecture->name;
    }
    ostr << "\n(assert-not\n" << conjecture->formula->toSMTLIB(3) + "\n)\n";
  }

  ostr << "\n(check-sat)\n" << std::endl;
}

void ReasoningTask::outputTPTPToDir(std::string dirPath,
                                    std::string preamble) const {
  auto outfileName = dirPath + conjecture->name + ".p";
  if (std::ifstream(outfileName)) {
    std::cout << "Error: The output-file " << outfileName << " already exists!"
              << std::endl;
    exit(1);
  }

  std::cout << "Generating reasoning task in " << outfileName << "\n";
  std::ofstream outfile(outfileName);

  if (!util::Configuration::instance().generateBenchmark()) {
    outfile << preamble;
  }

  // output task
  outputTPTP(outfile);
}

void ReasoningTask::outputTPTP(std::ostream& ostr) const {
  std::string logic = "tff";
  if (util::Configuration::instance().hol()) {
    logic = "thf";
  }

  for (const auto& pair : Sorts::nameToSort()) {
    ostr << declareSortTPTP(*pair.second);
  }

  // output symbol definitions
  for (const auto& symbol : Signature::signatureOrderedByInsertion()) {
    ostr << symbol->declareSymbolTPTP();
  }

  for (const auto& axiom : axioms) {
    assert(axiom->type == ProblemItem::Type::Axiom ||
           axiom->type == ProblemItem::Type::Definition);
    if (axiom->name != "") {
      ostr << "\n% "
           << (axiom->type == ProblemItem::Type::Axiom ? "Axiom: "
                                                       : "Definition: ")
           << axiom->name;
    }
    ostr << "\n" + logic + "(unnamed, axiom,\n"
         << axiom->formula->toTPTP(3) + "\n).\n";
  }
  // output conjecture
  assert(conjecture != nullptr);

  ostr << "\n\% negated conjecture\n"
       << logic + "(postcondition, conjecture, \n"
       << conjecture->formula->toTPTP() << ").\n";
}

std::vector<ReasoningTask> Problem::generateReasoningTasks() const {
  std::vector<ReasoningTask> tasks;

  std::vector<std::shared_ptr<const Conjecture>> conjectures;
  std::vector<std::shared_ptr<const ProblemItem>> axioms;

  for (int i = 0; i < items.size(); ++i) {
    auto item = items[i];

    if (item->type != ProblemItem::Type::Conjecture) {
      axioms.push_back(item);
    }

    if (item->type == ProblemItem::Type::Conjecture) {
      // TODO use static cast instead?
      conjectures.push_back(
          std::make_shared<Conjecture>(item->formula, item->name));
    }
  }

  for (auto& conj : conjectures) {
    tasks.push_back(ReasoningTask(axioms, conj, false, false));
  }

  if (memSafetyConj1 != nullptr) {
    // TODO perhaps allow users to separate these checks?
    assert(memSafetyConj2 != nullptr);
    tasks.push_back(ReasoningTask(axioms, memSafetyConj1, false, true));
    tasks.push_back(ReasoningTask(axioms, memSafetyConj2, true, false));
  }

  return tasks;
}

}  // namespace logic
