set(SPECTRE_SOLVER_INTERFACE_SOURCES
    SolverInterface.cpp
)
set(SPECTRE_SOLVER_INTERFACE_HEADERS
    SolverInterface.hpp
)

add_library(solvers ${SPECTRE_SOLVER_INTERFACE_SOURCES} ${SPECTRE_SOLVER_INTERFACE_HEADERS})
target_include_directories(solvers PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(solvers util logic)
target_link_libraries(solvers "${VAMPIRE_LIB}")
target_include_directories(solvers PRIVATE ${VAMPIRE_INCLUDE_DIRS})