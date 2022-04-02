set(SPECTRE_ANALYSIS_SOURCES
    Semantics.cpp
    GenerateMemConjectures.cpp
    SemanticsHelper.cpp
    SemanticsInliner.cpp
    AnalysisPreComputation.cpp
    TraceLemmas.cpp
    TheoryAxioms.cpp
    ProgramTraverser.cpp
    LemmasVariableDiffs.cpp
    LemmasVariableValues.cpp
    LemmasIterators.cpp
    LemmasOther.cpp
    LemmasTwoTraces.cpp
)
set(SPECTRE_ANALYSIS_HEADERS
    Semantics.hpp
    GenerateMemConjectures.hpp    
    SemanticsHelper.hpp
    SemanticsInliner.hpp
    AnalysisPreComputation.hpp
    TraceLemmas.hpp
    TheoryAxioms.hpp
    ProgramTraverser.hpp
    LemmasVariableDiffs.hpp    
    LemmasVariableValues.hpp
    LemmasIterators.hpp
    LemmasOther.hpp
    LemmasTwoTraces.hpp
)

add_library(analysis ${SPECTRE_ANALYSIS_SOURCES} ${SPECTRE_ANALYSIS_HEADERS})
target_include_directories(analysis PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(analysis program logic declarations)
target_link_libraries(analysis "${VAMPIRE_LIB}")
target_include_directories(analysis PRIVATE ${VAMPIRE_INCLUDE_DIRS})