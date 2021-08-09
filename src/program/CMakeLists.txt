set(SPECTRE_PROGRAM_SOURCES
    Expression.cpp
    Variable.cpp
    Statements.cpp
    Program.cpp
    ValueType.cpp
)

set(SPECTRE_PROGRAM_HEADERS
    Expression.hpp
    Variable.hpp
    Statements.hpp
    Program.hpp
    ValueType.hpp
)

add_library(program ${SPECTRE_PROGRAM_SOURCES} ${SPECTRE_PROGRAM_HEADERS})
target_include_directories(program PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(program util)
