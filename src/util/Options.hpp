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
        _lemmaPredicates("-lemmaPredicates", true),
        _memSafetyMode("-memSafetyMode", false),

        _allOptions() {
    registerOption(&_outputDir);
    registerOption(&_generateBenchmark);
    registerOption(&_nativeNat);
    registerOption(&_inlineSemantics);
    registerOption(&_variableDifferences);
    registerOption(&_axiomatiseToInt);
    registerOption(&_lemmaPredicates);
    registerOption(&_memSafetyMode);
  }

  bool setAllValues(int argc, char* argv[]);

  Option* getOption(std::string name);

  std::string outputDir() { return _outputDir.getValue(); }
  bool generateBenchmark() { return _generateBenchmark.getValue(); }
  bool nativeNat() { return _nativeNat.getValue(); }
  bool inlineSemantics() { return _inlineSemantics.getValue(); }
  bool variableDifferences() { return _variableDifferences.getValue(); }
  bool axiomatiseToInt() { return _axiomatiseToInt.getValue(); }
  bool lemmaPredicates() { return _lemmaPredicates.getValue(); }
  bool memSafetyMode() { return _memSafetyMode.getValue(); }

  void setDontInline() { _inlineSemantics.setValue("off"); }
  static Configuration& instance() { return _instance; }

 protected:
  StringOption _outputDir;
  BooleanOption _generateBenchmark;
  BooleanOption _nativeNat;
  BooleanOption _inlineSemantics;
  BooleanOption _variableDifferences;
  BooleanOption _axiomatiseToInt;
  BooleanOption _lemmaPredicates;
  BooleanOption _memSafetyMode;

  std::map<std::string, Option*> _allOptions;

  void registerOption(Option* o);

  static Configuration _instance;
};
}  // namespace util

#endif
