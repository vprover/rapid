#ifndef __Options__
#define __Options__

#include <iostream>
#include <map>
#include <string>
#include <vector>

namespace util {

class Option {
 public:
  std::string name() { return _name; }
  std::string description(){ return _description; }
  bool experimental(){ return _experimental; }

  // return true if the value was succesfully set
  virtual bool setValue(std::string v) = 0;

  virtual bool isBooleanOption() { return false; }
  virtual bool isMultiChoiceOption() { return false; }

 protected:
  Option(std::string name, std::string description, bool experimental = false) : 
    _name(name), _description(description), _experimental(experimental) {}

  bool _experimental;
  std::string _description;
  std::string _name;
};

class BooleanOption : public Option {
 public:
  BooleanOption(std::string name, std::string description, 
               bool defaultValue, bool experimental = false)
      : Option(name, description, experimental), _value(defaultValue) {}

  virtual bool isBooleanOption() { return true; }

  bool setValue(std::string v);

  bool getValue() { return _value; }

 protected:
  bool _value;
};

class StringOption : public Option {
 public:
  StringOption(std::string name, std::string description, 
               std::string defaultValue)
      : Option(name, description), _value(defaultValue) {}

  bool setValue(std::string v) {
    _value = v;
    return true;
  }

  std::string getValue() { return _value; }

 protected:
  std::string _value;
};

class MultiChoiceOption : public Option {
 public:
  MultiChoiceOption(std::string name, std::string description, 
                    std::vector<std::string> choices,
                    std::string defaultValue)
      : Option(name, description), _value(defaultValue), _choices(choices) {}

  virtual bool isMultiChoiceOption() { return true; }
  std::vector<std::string> choices(){
    return _choices;
  }

  bool setValue(std::string v);

  std::string getValue() { return _value; }

 protected:
  std::string _value;

  std::vector<std::string> _choices;
};

class Configuration {
 public:
  Configuration()
      : _outputDir("-dir", "directory in which to store the SMT file", ""),
        _generateBenchmark("-generateBenchmark", "", false),
        _nativeNat("-nat", "use natural numbers to denote loop iterations", true),
        _inlineSemantics("-inlineSemantics", "", true),
        _variableDifferences("-varDiff", "", false),
        _axiomatiseToInt("-axToInt", "axiomatises the toInt function which converts nats to ints", false),
        _memSafetyMode("-memSafetyMode", "adds axioms in attempt to reason about memory safety", false, true),
        _explodeMemRegions("-explodeMemRegions", 
          "explicit list regions in memory instead of using ranges", false),
        _useListPredicate("-useLists", "", {"off", "acyclic", "cyclic"}, "off"),
        _memoryModel("-memoryModel", "", {"typed","untyped"}, "typed"),
        _useLocSets("-useLocSets", 
          "use sets isntead of predicates to determine locations within a data structure", true),
        _lemmaPredicates("-lemmaPredicates", "", true),
        _integerIterations("-integerIterations", "use integers to denote loop iterations", false),
        _inlineLemmas("-inlineLemmas", "", false),
        _postcondition("-postcondition", "",  false),
        _outputTraceLemmas("-outputTraceLemmas", "output trace lemmas", false),
        _tptp("-tptp", "output theorem proving problem in TPTP syntax", false),
        _hol("-hol", "output theorem proving problem using HOL", false, true),
        _allOptions() {
    registerOption(&_outputDir);
    registerOption(&_generateBenchmark);
    registerOption(&_nativeNat);
    registerOption(&_inlineSemantics);
    registerOption(&_variableDifferences);
    registerOption(&_axiomatiseToInt);
    // Try and find memory safety bugs. May not
    // be fully functional at the moment. Even when functional,
    // could only find bugs that were on every execution path
    registerOption(&_memSafetyMode);
    // Rather than reasoning that particular mem location is not
    // in a range (! X. lb <= x < ub. var != x), we explode
    // the range. Works better for small ranges
    // Only compatible with the untyped memory model
    registerOption(&_explodeMemRegions);

    registerOption(&_useListPredicate);

    registerOption(&_useLocSets);
    // Currently can use a typed or untyped memory model
    // Untyped models memory as a massive integer array
    registerOption(&_memoryModel);  

    // uses lemma predicates for Rapid Vampire
    registerOption(&_lemmaPredicates);

    // semantics with iterations using integer instead of natural number sort
    registerOption(&_integerIterations);

    // inline lemmas as one big formula without naming
    registerOption(&_inlineLemmas);

    // postcondition mode prints color and target symbols
    registerOption(&_postcondition);

    // outputs trace lemmas. With Vampire's new support for induction
    // these are not required
    registerOption(&_outputTraceLemmas);

    // tptp outputs formula in TPTP syntax
    registerOption(&_tptp);

    // hol outputs formula in TPTP HOL syntax
    registerOption(&_hol);
  }

  //TODO check for incompatible or nonsensical options
  bool setAllValues(int argc, char* argv[]);
  void outputOptionsHelp();

  Option* getOption(std::string name);

  std::string outputDir() { return _outputDir.getValue(); }
  bool generateBenchmark() { return _generateBenchmark.getValue(); }
  bool nativeNat() { return _nativeNat.getValue(); }
  bool inlineSemantics() { return _inlineSemantics.getValue(); }
  bool variableDifferences() { return _variableDifferences.getValue(); }
  bool axiomatiseToInt() { return _axiomatiseToInt.getValue(); }
  bool memSafetyMode() { return _memSafetyMode.getValue(); }
  bool explodeMemRegions() { return _explodeMemRegions.getValue(); }
  std::string useLists() { return _useListPredicate.getValue(); }
  bool useLocSets() { return _useLocSets.getValue(); }
  std::string memoryModel() { return _memoryModel.getValue(); }

  bool lemmaPredicates() { return _lemmaPredicates.getValue(); }
  bool integerIterations() { return _integerIterations.getValue(); }
  bool inlineLemmas() { return _inlineLemmas.getValue(); }
  bool postcondition() { return _postcondition.getValue(); }
  bool outputTraceLemmas() { return _outputTraceLemmas.getValue(); }
  bool tptp() { return _tptp.getValue(); }
  bool hol() { return _hol.getValue(); }

  void setDontInline() { _inlineSemantics.setValue("off"); }


  static Configuration& instance() { return _instance; }

 protected:
  StringOption _outputDir;
  BooleanOption _generateBenchmark;
  BooleanOption _nativeNat;
  BooleanOption _inlineSemantics;
  BooleanOption _variableDifferences;
  BooleanOption _axiomatiseToInt;
  BooleanOption _memSafetyMode;
  BooleanOption _explodeMemRegions;
  MultiChoiceOption _useListPredicate;
  BooleanOption _useLocSets;
  MultiChoiceOption _memoryModel;  

  BooleanOption _lemmaPredicates;
  BooleanOption _integerIterations;
  BooleanOption _inlineLemmas;
  BooleanOption _postcondition;
  BooleanOption _outputTraceLemmas;
  BooleanOption _tptp;
  BooleanOption _hol;

  std::map<std::string, Option*> _allOptions;

  void registerOption(Option* o);

  static Configuration _instance;
};
}  // namespace util

#endif
