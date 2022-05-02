#include "Problem.hpp"

#include <algorithm>
#include <ctime>
#include <fstream>
#include <regex>

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
                                      std::string preamble) const {
  auto outfileName = dirPath + conjecture->name + ".smt2";

  // don't print semantics multiple times for invgen mode
  if (util::Configuration::instance().invariantGeneration() 
      && conjecture->name.find("user-conjecture") != std::string::npos 
      && conjecture->name.find("-0") == std::string::npos
      && !isPostcondition) {
    return;
  }
  
  if (isPostcondition) {
    outfileName = dirPath + conjecture->name + "_postcondition.smt2";
  }
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
    if(axiom->type == ProblemItem::Type::Axiom ||
           axiom->type == ProblemItem::Type::Definition){
      if (axiom->name != "") {
            ostr << "\n; "
                << (axiom->type == ProblemItem::Type::Axiom ? "Axiom: "
                                                            : "Definition: ")
                << axiom->name;
          }
          ostr << "\n(assert\n" << axiom->formula->toSMTLIB(3) + "\n)\n";
    }
  }

  // output conjecture
  assert(conjecture != nullptr);

  if (isPostcondition) {
    //print negated loop conditions
    for (const auto &axiom : axioms) {
      if(axiom->type == ProblemItem::Type::LoopCondition){
        if (axiom->name != "") {
              ostr << "\n; "
                  << axiom->name;
            }
            ostr << "\n(assert\n" << toTargetSymbolsSMTLIB(axiom->formula->toSMTLIB(3)) + "\n)\n";
      }
    }
    // print 
    auto conj = toTargetSymbolsSMTLIB(conjecture->formula->toSMTLIB(3));
    ostr << "\n(assert-not\n" << conj + "\n)\n" << std::endl;
  } else if(util::Configuration::instance().invariantGeneration()) {
    // don't print conjecture with semantics
    ostr << std::endl;
  } else {
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
  
}

// replace trace logic function terms with target symbols for postcondition
  std::string ReasoningTask::toTargetSymbolsSMTLIB(std::string formula) const{
    std::string str = formula;
    std::string toReplace(" main_end");
    std::string replacement("_final");
    std::string toReplace2("()");
    std::string replacement2("");
    while (util::Configuration::instance().invariantGeneration() 
        && (str.find(toReplace) != std::string::npos 
        || str.find(toReplace2) != std::string::npos)) {
      
      //remove any main_end references
      size_t pos = str.find(toReplace);
      if (pos != std::string::npos)
        str = str.replace(pos, toReplace.length(), replacement);

      // remove () for constants
      size_t pos2 = str.find(toReplace2);
      if (pos2 != std::string::npos)
        str = str.replace(pos2, toReplace2.length(), replacement2);
    }
    //replace location for loop conditions
    std::regex reg(" \\(l[0-9]+ [^)]*\\)");
    str = regex_replace(str, reg, "_final");
    return str;
}

void ReasoningTask::outputTPTPToDir(std::string dirPath,
                                    std::string preamble) const {
  auto outfileName = dirPath + conjecture->name + "_postcondition.p";
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
  
  assert(conjecture != nullptr);
  // output conjecture
  ostr << "\n\% negated conjecture\n"
       << logic + "(postcondition, conjecture, \n"
       << conjecture->formula->toTPTP() << ").\n" << std::endl;    
}

// replace trace logic function terms with target symbols for postcondition
std::string ReasoningTask::toTargetSymbolsTPTP(std::string formula) const{
  std::string str = formula;
  if (util::Configuration::instance().postcondition() && str.find("main_end") != std::string::npos) {
    std::string toReplace("(main_end");
    std::string replacement("_final(");
    size_t pos = str.find(toReplace);
    str = str.replace(pos, toReplace.length(), replacement);

    // remove () for constants
    std::string toReplace2("()");
    std::string replacement2("");
    size_t pos2 = str.find(toReplace2);
    if (pos2 != std::string::npos)
      str = str.replace(pos2, toReplace2.length(), replacement2);

    // replace (, for function terms with (
    std::string toReplace3("(,");
    std::string replacement3("(");
    size_t pos3 = str.find(toReplace3);
    if (pos3 != std::string::npos)
      str = str.replace(pos3, toReplace3.length(), replacement3);
  }
  return str;
}   

std::vector<ReasoningTask> Problem::generateReasoningTasks() const {
  std::vector<ReasoningTask> tasks;

  for (int i = 0; i < items.size(); ++i) {
    auto item = items[i];

    // generate output for each conjecture in a seperate file to be used to
    // verify which invariants generated by symbol elimination are used to
    // proof the conjecture
    if (util::Configuration::instance().invariantGeneration() &&
        item->type == ProblemItem::Type::Conjecture) {
      // add item as conjecture
      auto conjecture = std::make_shared<Conjecture>(item->formula, item->name);
      std::vector<std::shared_ptr<const ProblemItem>> negatedLoopConditions;
      for (int j = 0; j < i; ++j) {
        auto curr = items[j];
        // collect all loop conditions
        if (curr->type == ProblemItem::Type::LoopCondition) {
            negatedLoopConditions.push_back(std::make_shared<LoopCondition>(
                curr->formula, curr->name));
        } 
        
      }
      auto task = ReasoningTask(negatedLoopConditions, conjecture, true);
      tasks.push_back(task);
    }

    // if the item is a lemma or conjecture, generate a new reasoning task to
    // prove that lemma/conjecture 
    // remove this line to only generate conjectures
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

      //add conjecture
      auto conjecture = std::make_shared<Conjecture>(item->formula, item->name);
      auto task = ReasoningTask(currentAxioms, conjecture);
      tasks.push_back(task);
    }
  }
  return tasks;
}

}  // namespace logic
