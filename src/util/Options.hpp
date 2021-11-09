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

  // return true if the value was succesfully set
  virtual bool setValue(std::string v) = 0;

 protected:
  Option(std::string name) : _name(name) {}

  std::string _name;
};

class BooleanOption : public Option {
 public:
  BooleanOption(std::string name, bool defaultValue)
      : Option(name), _value(defaultValue) {}

  bool setValue(std::string v);

  bool getValue() { return _value; }

 protected:
  bool _value;
};

class StringOption : public Option {
 public:
  StringOption(std::string name, std::string defaultValue)
      : Option(name), _value(defaultValue) {}

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
  MultiChoiceOption(std::string name, std::vector<std::string> choices,
                    std::string defaultValue)
      : Option(name), _value(defaultValue), _choices(choices) {}

  bool setValue(std::string v);

  std::string getValue() { return _value; }

 protected:
  std::string _value;

  std::vector<std::string> _choices;
};

class Configuration {
 public:
  Configuration()
      : _outputDir("-dir", ""),
        _generateBenchmark("-generateBenchmark", false),
        _nativeNat("-nat", true),
        _inlineSemantics("-inlineSemantics", true),
        _variableDifferences("-varDiff", false),
        _axiomatiseToInt("-axToInt", false),
        _memSafetyMode("-memSafetyMode", false),
        _lemmaPredicates("-lemmaPredicates", true),
        _integerIterations("-integerIterations", false),
        _inlineLemmas("-inlineLemmas", false),
        _postcondition("-postcondition", false),
        _outputTraceLemmas("-outputTraceLemmas", false),
        _tptp("-tptp", false),
        _hol("-hol", false),
        _allOptions() {
    registerOption(&_outputDir);
    registerOption(&_generateBenchmark);
    registerOption(&_nativeNat);
    registerOption(&_inlineSemantics);
    registerOption(&_variableDifferences);
    registerOption(&_axiomatiseToInt);
    registerOption(&_memSafetyMode);
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

  bool setAllValues(int argc, char* argv[]);

  Option* getOption(std::string name);

  std::string outputDir() { return _outputDir.getValue(); }
  bool generateBenchmark() { return _generateBenchmark.getValue(); }
  bool nativeNat() { return _nativeNat.getValue(); }
  bool inlineSemantics() { return _inlineSemantics.getValue(); }

  bool variableDifferences() { return _variableDifferences.getValue(); }
  bool axiomatiseToInt() { return _axiomatiseToInt.getValue(); }
  bool memSafetyMode() { return _memSafetyMode.getValue(); }

  void setDontInline() { _inlineSemantics.setValue("off"); }
  bool lemmaPredicates() { return _lemmaPredicates.getValue(); }
  bool integerIterations() { return _integerIterations.getValue(); }
  bool inlineLemmas() { return _inlineLemmas.getValue(); }
  bool postcondition() { return _postcondition.getValue(); }
  bool outputTraceLemmas() { return _outputTraceLemmas.getValue(); }
  bool tptp() { return _tptp.getValue(); }
  bool hol() { return _hol.getValue(); }

  static Configuration instance() { return _instance; }

 protected:
  StringOption _outputDir;
  BooleanOption _generateBenchmark;
  BooleanOption _nativeNat;
  BooleanOption _inlineSemantics;
  BooleanOption _variableDifferences;
  BooleanOption _axiomatiseToInt;
  BooleanOption _memSafetyMode;
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
