This document explains how to build Rapid with Vampire as a backend reasoner

# Building Vampire

Checkout the Vampire branch `ahmed-rapid-without-ir`

Run your normal CMake command. It will probably look something similar to:

```
cmake -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=Release -G "Unix Makefiles" ..
```

Now run

```
make -j n
```

where `n` is the number of cores. Once the command completes you should see a file `libvampire.dylib` or `libvampire.lib` within the build folder.

## Building Rapid

Follow, the standard build instructions provided in `README.md`, but set a flag `Vampire_DIR` to the location of the Vampire library when running CMake. For example:

```
cmake .. -DVampire_DIR=../../vampire/build_ahmed_rapid_debug/    
```

if the `.dylib` file is located at relative path `../../vampire/build_ahmed_rapid_debug/ `