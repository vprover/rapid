# Overview

RAPID is a software verification tool that takes a program together with a property as input and
produces a first-order-encoding of correctness in SMTLIB syntax.
This encoding can then be passed to an arbitrary first-order reasoning engine which supports SMTLIB, e.g. Vampire.

RAPID is focused on 
- programs containing arrays
- functional properties, hyperproperties, possibly with quantifier alternations
- proving properties instead of disproving them (we don't try to find bugs)

# Using RAPID
RAPID is intended to be used as follows: 
- Write your program in the supported while-language,
- Write the property you want to prove in the supported SMTLIB-syntax,
- Pass the file containing the program and the property to RAPID, which generates an SMTLIB-encoding.
- Pass the file containing the SMTLIB-encoding to Vampire

### Building the executable

There are two steps involved in building RAPID.

First, we generate the source-code files for the RAPID-parser using Flex and Bison:
Make sure you have these two tools installed and that the paths are properly set in parser_generator/Makefile.
Then, while being in parser_generator, run make (which produces the necessary files in src/parser/). You might have to change
the paths to flex and bison. (For Windows you can use win_flex/win_bison or Cygwin.)

Secondly, we use CMake to generate the necessary files which are needed while building RAPID. Make sure you have CMake installed.

Starting from the main directory, make a new folder (to do an out-of-source-build) and switch to it by running
```
$ mkdir build; cd build
```
The next step depends on your favourite build tool:

If you want to use make as build-tool, run
```
$ cmake ..
```
and build RAPID by running
```
$ make
```

If you want to use XCode as build-tool, run

```
$ cmake -G Xcode ..
```
and build RAPID from the generated XCode project (which will be generated in /build/)

For other build-tools like ninja, Visual Studio, Eclipse or Sublime2, consult the CMake documentation.

### Which programs and properties may be used as input?
The programs must be given in a dedicated while-like language.
We support integer- and integer-array-variables,
the standard statements (assignments, if-else, while, skip)
and assertions of the program (in SMTLIB-format).

See the example programs on the repository for more details.

### Which first-order theorem prover should I use?
Short answer: Vampire

Long answer:
Any prover that supports SMTLIBv2.6-syntax can in principle be used to
solve problems generated by Rapid. 
In practice the solver should have efficient support for quantifiers, in particular for quantifier-alternations.
The encoding is optimized for superposition-based provers, and in particular for Vampire.
