cmake_minimum_required (VERSION 3.6.3)

################################################################
project (Rapid)
################################################################

# require the compiler to use C++17
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# add directory, where we store all custom files for finding libraries which are not build using cmake (i.e. currently nothing), to the search path of cmake
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Set the output folder where the binary will be created (i.e. build/dir)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

add_executable(rapid src/main.cpp)
# TODO test.cpp breaks build on macOS, leave commented until fixed
# add_executable(test src/test.cpp)


add_subdirectory(src/analysis)
add_subdirectory(src/logic)
add_subdirectory(src/parser)
add_subdirectory(src/program)
add_subdirectory(src/util)

target_link_libraries(rapid analysis logic parser program util)
# target_link_libraries(test analysis logic parser program util)

# add_custom_command(TARGET test POST_BUILD
#         COMMAND ${CMAKE_COMMAND} -E copy_directory
#         ${CMAKE_SOURCE_DIR}/examples/ $<TARGET_FILE_DIR:test>/examples)

