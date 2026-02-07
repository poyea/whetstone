#pragma once

#include "solver.hpp"
#include <istream>

bool parse_dimacs(std::istream& in, Solver& solver);
