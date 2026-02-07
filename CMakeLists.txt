cmake_minimum_required(VERSION 3.20)
project(whetstone LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(MSVC)
    add_compile_options(/W4)
else()
    add_compile_options(-Wall -Wextra -Wpedantic -O2)
endif()

set(SOLVER_SOURCES
    src/solver.cpp
    src/propagate.cpp
    src/analyze.cpp
    src/vsids.cpp
    src/clause_db.cpp
    src/search.cpp
    src/dimacs.cpp
)

add_executable(whetstone
    src/main.cpp
    ${SOLVER_SOURCES}
)

enable_testing()

add_executable(whetstone_tests
    tests/test_solver.cpp
    ${SOLVER_SOURCES}
)

add_test(NAME solver_tests COMMAND whetstone_tests)
