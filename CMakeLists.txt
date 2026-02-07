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

add_executable(whetstone
    src/main.cpp
    src/solver.cpp
)

enable_testing()

add_executable(whetstone_tests
    tests/test_solver.cpp
    src/solver.cpp
)

add_test(NAME solver_tests COMMAND whetstone_tests)
