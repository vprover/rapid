#include "Options.hpp"

#include <iostream>
#include <string>
#include <utility>

namespace util {

bool BooleanOption::setValue(std::string v) {
  if (v == "on") {
    _value = true;
    return true;
  } else if (v == "off") {
    _value = false;
    return true;
  } else {
    return false;
  }
}

bool MultiChoiceOption::setValue(std::string v) {
  for (auto it = _choices.begin(); it != _choices.end(); ++it) {
    if (*it == v) {
      _value = v;
      return true;
    }
  }

  return false;
}

bool Configuration::setAllValues(int argc, char* argv[]) {
  int i = 1;
  bool b = true;

  if(strcmp(argv[i], "-help") ==0){
    outputOptionsHelp();
    return false;
  }

  // ignore first argument (program name) and last (input file)
  while (i < argc - 1) {
  
    if(strcmp(argv[i], "-help") ==0){
      outputOptionsHelp();
      return false;
    }

    auto it = _allOptions.find(std::string(argv[i]));
    if (it != _allOptions.end()) {
      if (!(*it).second->setValue(argv[i + 1])) {
        b = false;
        std::cout << argv[i + 1] << " is not a correct value for option "
                  << argv[i] << " try running with -help to see options and values available" << std::endl;

      }
    } else {
      b = false;
      std::cout << "Unknown option " << argv[i] << std::endl;
    }
    i += 2;
  }
  checkValues();
  return b;
}

void Configuration::checkValues() {

  if(hol() && outputToFile() && !tptp()){
    std::cerr << "ERORR: SMT-LIB2 syntax does not support higher-order. Must use TPTP syntax with HOL";
    std::exit(EXIT_FAILURE);
  }

  if(generateBenchmark() && !outputToFile()){
    std::cerr << "ERORR: can only generate a benchmark when outputting to a file";
    std::exit(EXIT_FAILURE);        
  }

  if(outputDir() == "" && outputToFile()){
    std::cerr << "ERORR: if outputting to a file, an output directory must be specified";
    std::exit(EXIT_FAILURE);     
  }

  // should fail if output directory does not exist or already contains a file with the target
  // name.

  if(nativeNat() && integerIterations()){
    std::cerr << "WARNING: native nat option does not make sense when using integer iterations\n";
  }


}


void Configuration::outputOptionsHelp()
{
  std::cout << "\nRapid Options: \n" << std::endl;

  auto iter = _allOptions.begin();
  while (iter != _allOptions.end()) {
    auto option = iter->second;
    auto description = option->description();
    if(description == ""){
      description = "[missing description]";
    }

    if(option->experimental()){
      std::cout << "[EXPERIMENTAL] ";
    }
    std::cout << option->name() + ", ";
    if(option->isBooleanOption()){
      std::cout << "{on, off}";
    }
    if(option->isMultiChoiceOption()){
      MultiChoiceOption* mcoption = static_cast<MultiChoiceOption*>(option);
      std::cout << "{";
      bool first = true;
      for(auto& choice : mcoption->choices()){
        std::cout << (!first ? ", " : "") << choice;
        first = false;
      }
      std::cout << "}";
    }
    std::cout << "\n   " << description << std::endl;
    ++iter; 
  }
}
void Configuration::registerOption(Option* o) {
  _allOptions.insert(std::pair<std::string, Option*>(o->name(), o));
}

Configuration Configuration::_instance;

}  // namespace util
