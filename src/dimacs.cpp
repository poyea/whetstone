#include "dimacs.hpp"
#include <iostream>
#include <sstream>
#include <string>

bool parse_dimacs(std::istream& in, Solver& solver) {
    std::string line;
    int num_vars = 0, num_clauses = 0;
    bool header_seen = false;

    while (std::getline(in, line)) {
        if (line.empty() || line[0] == 'c')
            continue;

        if (line[0] == 'p') {
            std::istringstream iss(line);
            std::string p, cnf;
            iss >> p >> cnf >> num_vars >> num_clauses;
            if (cnf != "cnf") {
                std::cerr << "expected 'cnf' in problem line\n";
                return false;
            }
            for (int i = 0; i < num_vars; i++)
                solver.new_var();
            header_seen = true;
            continue;
        }

        if (!header_seen) {
            std::cerr << "missing problem line\n";
            return false;
        }

        std::istringstream iss(line);
        std::vector<Lit> clause;
        int lit;
        while (iss >> lit) {
            if (lit == 0) {
                if (!solver.add_clause(std::move(clause)))
                    return true;
                clause.clear();
            } else {
                clause.push_back(Lit::from_dimacs(lit));
            }
        }
    }

    return true;
}
