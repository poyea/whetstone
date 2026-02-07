#include "dimacs.hpp"
#include "solver.hpp"
#include <fstream>
#include <iostream>
#include <string>

int main(int argc, char* argv[]) {
    std::string input_file;
    std::string proof_file;
    RestartPolicy restart_policy = RestartPolicy::Glucose;

    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        if (arg == "--proof" && i + 1 < argc) {
            proof_file = argv[++i];
        } else if (arg == "--luby") {
            restart_policy = RestartPolicy::Luby;
        } else if (arg == "--glucose") {
            restart_policy = RestartPolicy::Glucose;
        } else if (input_file.empty()) {
            input_file = arg;
        } else {
            std::cerr << "unknown argument: " << arg << "\n";
            return 1;
        }
    }

    if (input_file.empty()) {
        std::cerr << "usage: whetstone <input.cnf> [--proof <file>] "
                     "[--luby|--glucose]\n";
        return 1;
    }

    std::ifstream file(input_file);
    if (!file.is_open()) {
        std::cerr << "cannot open: " << input_file << "\n";
        return 1;
    }

    ProofLogger proof;
    Solver solver;
    solver.set_restart_policy(restart_policy);

    if (!proof_file.empty()) {
        if (!proof.open(proof_file)) {
            std::cerr << "cannot open proof file: " << proof_file << "\n";
            return 1;
        }
        solver.set_proof_logger(&proof);
    }

    if (!parse_dimacs(file, solver)) {
        std::cerr << "parse error\n";
        return 1;
    }

    bool result = solver.solve();
    auto& s = solver.stats();

    std::cout << (result ? "s SATISFIABLE" : "s UNSATISFIABLE") << "\n";

    if (result) {
        std::cout << "v ";
        for (uint32_t i = 0; i < solver.num_vars(); i++) {
            if (solver.model_value(i) == lbool::True)
                std::cout << (i + 1);
            else
                std::cout << "-" << (i + 1);
            std::cout << " ";
        }
        std::cout << "0\n";
    }

    std::cerr << "c conflicts:    " << s.conflicts << "\n";
    std::cerr << "c decisions:    " << s.decisions << "\n";
    std::cerr << "c propagations: " << s.propagations << "\n";
    std::cerr << "c restarts:     " << s.restarts << "\n";

    return result ? 10 : 20;
}
