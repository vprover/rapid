cmake_minimum_required (VERSION 3.6.3)

add_compile_options(-fsanitize=address)
add_compile_options(-fno-omit-frame-pointer)
add_link_options(-fsanitize=address)

################################################################
project (Rapid)
################################################################

# require the compiler to use C++20
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# message(${Vampire_DIR})

find_library(VAMPIRE_LIB vampire HINTS ${Vampire_DIR} $ENV{HOME}/vampire PATH_SUFFIXES lib bin)

find_path(VAMPIRE_INCLUDE_DIRS Solver.hpp HINTS ${Vampire_DIR}/../Api $ENV{HOME}/vampire PATH_SUFFIXES include)

if(VAMPIRE_LIB STREQUAL "VAMPIRE_LIB-NOTFOUND")
    message(FATAL_ERROR "Could not find libvampire, please check Vampire_DIR")
endif() 

if(VAMPIRE_INCLUDE_DIRS STREQUAL "VAMPIRE_INCLUDE_DIRS-NOTFOUND")
    message(FATAL_ERROR "Could not find vampire include headers, please check Vampire_DIR")
endif()

# add directoy, where we store all custom files for finding libraries which are not build using cmake (i.e. currently nothing), to the search path of cmake
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Set the output folder where the binary will be created (i.e. build/dir)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

add_executable(rapid src/main.cpp)

add_subdirectory(src/analysis)
add_subdirectory(src/declarations)
add_subdirectory(src/solvers)
add_subdirectory(src/logic)
add_subdirectory(src/parser)
add_subdirectory(src/program)
add_subdirectory(src/util)

target_include_directories(rapid PRIVATE ${VAMPIRE_INCLUDE_DIRS})
target_link_libraries(rapid analysis declarations solvers logic parser program util)



