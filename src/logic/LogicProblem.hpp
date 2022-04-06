#ifndef __ProblemRapid__
#define __ProblemRapid__

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "Formula.hpp"

namespace logic {

/*
 * abstract class for wrapping a formula and tagging it as either axiom,
 * definition, lemma or conjecture
 */
class ProblemItem {
 public:
  enum class Type { Program, Axiom, Definition, Lemma, Conjecture };
  enum class Visibility { All, Implicit, None };

  ProblemItem(Type type, std::shared_ptr<const logic::Formula> formula,
              std::string name, Visibility visibility,
              std::vector<std::string> fromItems)
      : type(type),
        formula(formula),
        name(name),
        visibility(visibility),
        fromItems(fromItems) {
    // it doesn't make sense to hide conjectures
    if (type == Type::Conjecture) {
      assert(visibility == Visibility::All);
    }
    // hidden items without a name can't be used as axioms
    if (name.empty()) {
      assert(visibility != Visibility::None);
    }
    // don't have to prove axioms or definitions, so it does not make sense to
    // annotate them.
    if (type == Type::Axiom || type == Type::Definition) {
      assert(fromItems.empty());
    }
    for (const auto& name : fromItems) {
      assert(name != "");
    }
  }

  virtual ~ProblemItem() = default;

  const Type type;
  std::shared_ptr<const logic::Formula> formula;
  const std::string name;
  const Visibility visibility;
  const std::vector<std::string> fromItems;
};

// hack needed for bison: std::vector has no overload for ostream, but these
// overloads are needed for bison
std::ostream& operator<<(
    std::ostream& ostr,
    const std::vector<std::shared_ptr<const ProblemItem>>& f);

class Axiom : public ProblemItem {
 public:
  Axiom(std::shared_ptr<const logic::Formula> axiom, std::string name = "",
        ProblemItem::Visibility visibility = ProblemItem::Visibility::All)
      : ProblemItem(ProblemItem::Type::Axiom, axiom, name, visibility, {}) {}
};

// a definition is a special case of an axiom.
class Definition : public ProblemItem {
 public:
  Definition(std::shared_ptr<const logic::Formula> definition,
             std::string name = "",
             ProblemItem::Visibility visibility = ProblemItem::Visibility::All)
      : ProblemItem(ProblemItem::Type::Definition, definition, name, visibility,
                    {}) {}
};

class Lemma : public ProblemItem {
 public:
  Lemma(std::shared_ptr<const logic::Formula> lemma, std::string name = "",
        ProblemItem::Visibility visibility = ProblemItem::Visibility::All,
        std::vector<std::string> fromItems = {})
      : ProblemItem(ProblemItem::Type::Lemma, lemma, name, visibility,
                    fromItems) {}
};

class Conjecture : public ProblemItem {
 public:
  Conjecture(std::shared_ptr<const logic::Formula> conjecture,
             std::string name = "", std::vector<std::string> fromItems = {},
             bool memSafetyVerification = false, 
             bool memSafetyViolationCheck = false)
      : ProblemItem(ProblemItem::Type::Conjecture, conjecture, name,
                    ProblemItem::Visibility::All, fromItems), 
      memSafetyVerification(memSafetyVerification),
      memSafetyViolationCheck(memSafetyViolationCheck) {}

  bool memVerificationConj() const { return memSafetyVerification; }
  bool memViolationCheckConj() const { return memSafetyViolationCheck; }

private:
  bool memSafetyVerification;
  bool memSafetyViolationCheck;
};

// represents a first-order reasoning task which can be passed to a prover.
// for now sorts and signatures are not part of Problem, maybe should be
// refactored.
class ReasoningTask {
 public:
  enum class Status { SOLVED, FAILED, NOT_ATTEMPTED };

  ReasoningTask(std::vector<std::shared_ptr<const ProblemItem>> axioms,
                std::shared_ptr<const Conjecture> conjecture)
      : axioms(axioms),
        conjecture(conjecture),
        status(Status::NOT_ATTEMPTED) {}

  std::vector<std::shared_ptr<const ProblemItem>> axioms;
  const std::shared_ptr<const Conjecture> conjecture;
  Status status;

  /*
   * generate a new file in the directory 'dirPath' and output the reasoning
   * task in SMTLIB syntax. the preamble string is added at the beginning of the
   * file.
   */
  void outputSMTLIBToDir(std::string dirPath, std::string inputFileName,
                         std::string preamble) const;

  void addAxiom(std::shared_ptr<const Axiom> axiom){
    axioms.push_back(axiom);
  }

  void addAxioms(std::vector<std::shared_ptr<const Axiom>> axms){
    axioms.insert(axioms.end(), axms.begin(),
                  axms.end());
  }

  /*
   * generate a new file in the directory 'dirPath' and output the reasoning
   * task in TPTP syntax. the preamble string is added at the beginning of the
   * file.
   */
  void outputTPTPToDir(std::string dirPath, std::string preamble) const;

  void outputSMTLIB(std::ostream& ostr) const;
 private:
  void outputTPTP(std::ostream& ostr) const;
};

/* represents a list of axioms, lemmas and conjectures,
 * where each lemma and each conjecture needs to be proven
 * from the preceding axioms and lemmas.
 * This is done by generating a ReasoningTask for each such
 * lemma or conjecture, which can then be passed to a prover
 */
class Problem {
 public:
  Problem(std::vector<std::shared_ptr<const ProblemItem>> items)
      : items(std::move(items)) {}

  std::vector<std::shared_ptr<const ProblemItem>> items;

  std::vector<ReasoningTask> generateReasoningTasks() const;
};
}  // namespace logic
#endif
