#ifndef __ProgramTraverser__
#define __ProgramTraverser__

#include <cassert>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "Formula.hpp"
#include "Program.hpp"
#include "Variable.hpp"

namespace analysis {
// abstract traversal of programs for generating output, e.g. for generating
// formulas. the main method generate() traverses the program and calls the
// corresponding version of generateOutputFor() for each statement of the
// program the intended usage is to subclass this class and override those
// generateOutputFor() methods for the relevant statements.
template <class OutputType>
class ProgramTraverser {
 public:
  ProgramTraverser(
      const program::Program &program,
      std::unordered_map<std::string,
                         std::vector<std::shared_ptr<program::Variable>>>
          locationToActiveVars,
      unsigned numberOfTraces)
      : program(program),
        locationToActiveVars(locationToActiveVars),
        numberOfTraces(numberOfTraces) {}

  void generate(OutputType &output);

 protected:
  const program::Program &program;
  const std::unordered_map<std::string,
                           std::vector<std::shared_ptr<program::Variable>>>
      locationToActiveVars;
  const unsigned numberOfTraces;

 private:
  void visitStatement(program::Statement *statement, OutputType &output);

  virtual void generateOutputFor(program::Assignment *statement,
                                 OutputType &output);

  virtual void generateOutputFor(program::IfElseStatement *statement,
                                 OutputType &output);

  virtual void generateOutputFor(program::WhileStatement *statement,
                                 OutputType &output);

  virtual void generateOutputFor(program::SkipStatement *statement,
                                 OutputType &output);
};

template <class OutputType>
void ProgramTraverser<OutputType>::generate(OutputType &output) {
  for (const auto &function : program.functions) {
    for (const auto &statement : function->statements) {
      visitStatement(statement.get(), output);
    }
  }
}

template <class OutputType>
void ProgramTraverser<OutputType>::visitStatement(program::Statement *statement,
                                                  OutputType &output) {
  if (typeid(*statement) == typeid(program::Assignment)) {
    auto castedAssignment = static_cast<program::Assignment *>(statement);
    // generate output
    generateOutputFor(castedAssignment, output);
  } else if (typeid(*statement) == typeid(program::IfElseStatement)) {
    auto castedIfElse = static_cast<program::IfElseStatement *>(statement);

    // generate output
    generateOutputFor(castedIfElse, output);

    // recurse on both branches
    for (const auto &statement : castedIfElse->ifStatements) {
      visitStatement(statement.get(), output);
    }
    for (const auto &statement : castedIfElse->elseStatements) {
      visitStatement(statement.get(), output);
    }
  } else if (typeid(*statement) == typeid(program::WhileStatement)) {
    auto castedWhile = static_cast<program::WhileStatement *>(statement);

    // generate output
    generateOutputFor(castedWhile, output);

    // recurse on body
    for (const auto &statement : castedWhile->bodyStatements) {
      visitStatement(statement.get(), output);
    }
  } else if (typeid(*statement) == typeid(program::SkipStatement)) {
    auto castedSkip = static_cast<program::SkipStatement *>(statement);
    // generate output
    generateOutputFor(castedSkip, output);
  } else {
    assert(false);
  }
}

template <class OutputType>
void ProgramTraverser<OutputType>::generateOutputFor(
    program::Assignment *statement, OutputType &output) {}

template <class OutputType>
void ProgramTraverser<OutputType>::generateOutputFor(
    program::IfElseStatement *statement, OutputType &output) {}

template <class OutputType>
void ProgramTraverser<OutputType>::generateOutputFor(
    program::WhileStatement *statement, OutputType &output) {}

template <class OutputType>
void ProgramTraverser<OutputType>::generateOutputFor(
    program::SkipStatement *statement, OutputType &output) {}
}  // namespace analysis
#endif
