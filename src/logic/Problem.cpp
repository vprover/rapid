#include "Problem.hpp"

#include <algorithm>
#include <ctime>
#include <fstream>

#include "Options.hpp"
#include "Output.hpp"

namespace logic {

std::ostream &operator<<(
    std::ostream &ostr,
    const std::vector<std::shared_ptr<const ProblemItem>> &f) {
  ostr << "not implemented";
  return ostr;
}

void ReasoningTask::outputSMTLIBToDir(std::string dirPath,
                                      std::string preamble) const {
  auto outfileName = dirPath + conjecture->name + ".smt2";
  if (std::ifstream(outfileName)) {
    if (!util::Configuration::instance().overwriteExisting()) {
      std::cout << "Error: The output-file " << outfileName
                << " already exists!" << std::endl;
      exit(1);
    }
    if (remove(outfileName.c_str())) {
      std::cout << "Could not delete existing file " << outfileName
                << std::endl;
    }
    std::cout << "Overwriting file " << outfileName << std::endl;
  }

  std::cout << "Generating reasoning task in " << outfileName << "\n";
  std::ofstream outfile(outfileName);

  if (!util::Configuration::instance().generateBenchmark()) {
    outfile << preamble;
  }

  // output task
  outputSMTLIB(outfile);
}

void ReasoningTask::outputSMTLIB(std::ostream &ostr) const {
  auto smtlibLogic = "UFDTLIA";  // uninterpreted functions, datatypes and
                                 // linear integer arithmetic

  // if encoding is used as smtlib-benchmark, add meta information
  if (util::Configuration::instance().generateBenchmark()) {
    ostr << "(set-info :smt-lib-version 2.6)\n";
    ostr << "(set-logic " << smtlibLogic << ")\n";

    std::time_t t = std::time(0);
    std::tm *now = std::localtime(&t);

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
  for (const auto &pair : Sorts::nameToSort()) {
    ostr << declareSortSMTLIB(*pair.second);
  }

  // output symbol definitions
  for (const auto &symbol : Signature::signatureOrderedByInsertion()) {
    ostr << symbol->declareSymbolSMTLIB();
  }

  // output each axiom
  for (const auto &axiom : axioms) {
    assert(axiom->type == ProblemItem::Type::Axiom ||
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
  auto outfileName = dirPath + conjecture->name + "_postcondition.p";
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
  // TODO: output negated loop conditions
  // for (const auto& axiom : axioms)
  // {
  //     assert(axiom->type == ProblemItem::Type::Axiom || axiom->type ==
  //     ProblemItem::Type::Definition); if (axiom->name != "")
  //     {
  //         ostr << "\n; " << (axiom->type == ProblemItem::Type::Axiom ?
  //         "Axiom: " : "Definition: ") << axiom->name;
  //     }
  //     ostr << "\n(assert\n" << axiom->formula->toSMTLIB(3) + "\n)\n";
  // }

  // output conjecture
  assert(conjecture != nullptr);

  ostr << "\n% negated conjecture\n"
       << "tff(postcondition, conjecture, " << conjecture->formula->toTPTP(0)
       << ").\n";
}

std::vector<ReasoningTask> Problem::generateReasoningTasks() const {
  std::vector<ReasoningTask> tasks;

  for (int i = 0; i < items.size(); ++i) {
    auto item = items[i];

    // print postcondition in tptp format for symbol elimination
    if (util::Configuration::instance().postcondition() &&
        item->type == ProblemItem::Type::Conjecture) {
      // generate output for each conjecture in a seperate file to be used to
      // verify which invariants generated by symbol elimination are used to
      // proof the conjecture
    }

    // if the item is a lemma or conjecture, generate a new reasoning task to
    // prove that lemma/conjecture removed this line to only generate
    // conjectures
    if (item->type == ProblemItem::Type::Lemma ||
        item->type == ProblemItem::Type::Conjecture)
    // if (item->type == ProblemItem::Type::Conjecture)
    {
      // collect all previous axioms, which are not hidden or occur in fromItems
      std::vector<std::shared_ptr<const ProblemItem>> currentAxioms;
      for (int j = 0; j < i; ++j) {
        auto curr = items[j];

        if (item->fromItems.empty()) {
          // implicit mode: collect all axioms visible for implicit mode
          if ((curr->type == ProblemItem::Type::Axiom ||
               curr->type == ProblemItem::Type::Definition)) {
            if (curr->visibility == ProblemItem::Visibility::All ||
                curr->visibility == ProblemItem::Visibility::Implicit) {
              currentAxioms.push_back(curr);
            }
          } else if (curr->type == ProblemItem::Type::Lemma) {
            if (curr->visibility == ProblemItem::Visibility::All ||
                curr->visibility == ProblemItem::Visibility::Implicit) {
              currentAxioms.push_back(std::make_shared<Axiom>(
                  curr->formula, "already-proven-lemma " + curr->name));
            }
          }
        } else {
          // explicit mode: collect all axioms, which are either visible for
          // explicit mode or occur in fromItems
          if (curr->visibility == ProblemItem::Visibility::All ||
              std::find(item->fromItems.begin(), item->fromItems.end(),
                        curr->name) != item->fromItems.end()) {
            if ((curr->type == ProblemItem::Type::Axiom ||
                 curr->type == ProblemItem::Type::Definition)) {
              currentAxioms.push_back(curr);
            } else if (curr->type == ProblemItem::Type::Lemma) {
              currentAxioms.push_back(std::make_shared<Axiom>(
                  curr->formula, "already-proven-lemma " + curr->name));
            }
          }
        }
      }

      // sanity check: if explicit mode is used, all axioms must have been found
      // (note: there could be other axioms too)
      if (!item->fromItems.empty()) {
        assert(item->fromItems.size() <= currentAxioms.size());
      }

      // add item as conjecture
      auto conjecture = std::make_shared<Conjecture>(item->formula, item->name);
      auto task = ReasoningTask(currentAxioms, conjecture);
      tasks.push_back(task);
    }
  }
  return tasks;
}

}  // namespace logic
