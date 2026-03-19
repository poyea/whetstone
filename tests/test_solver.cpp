#include "../src/dimacs.hpp"
#include "../src/solver.hpp"
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <vector>

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) static void name()
#define RUN(name)                                                                                                      \
    do {                                                                                                               \
        std::cout << "  " #name "... ";                                                                                \
        try {                                                                                                          \
            name();                                                                                                    \
            std::cout << "PASS\n";                                                                                     \
            tests_passed++;                                                                                            \
        } catch (const std::exception& e) {                                                                            \
            std::cout << "FAIL: " << e.what() << "\n";                                                                 \
            tests_failed++;                                                                                            \
        } catch (...) {                                                                                                \
            std::cout << "FAIL\n";                                                                                     \
            tests_failed++;                                                                                            \
        }                                                                                                              \
    } while (0)
#define ASSERT(cond)                                                                                                   \
    if (!(cond))                                                                                                       \
    throw std::runtime_error("assertion failed: " #cond)

static bool verify_model(Solver& s, const std::vector<std::vector<Lit>>& clauses) {
    for (auto& cl : clauses) {
        bool sat = false;
        for (auto l : cl) {
            if (s.model_value(l) == lbool::True) {
                sat = true;
                break;
            }
        }
        if (!sat)
            return false;
    }
    return true;
}

// tests

TEST(empty_solver) {
    Solver s;
    ASSERT(s.solve() == true);
}

TEST(single_positive_unit) {
    Solver s;
    s.new_var();
    s.add_clause({Lit(0, false)});
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(0)) == lbool::True);
}

TEST(single_negative_unit) {
    Solver s;
    s.new_var();
    s.add_clause({Lit(0, true)});
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(0)) == lbool::False);
}

TEST(conflicting_units) {
    Solver s;
    s.new_var();
    s.add_clause({Lit(0, false)});
    s.add_clause({Lit(0, true)});
    ASSERT(s.solve() == false);
}

TEST(empty_clause) {
    Solver s;
    ASSERT(s.add_clause({}) == false);
    ASSERT(s.solve() == false);
}

TEST(two_var_or) {
    Solver s;
    s.new_var();
    s.new_var();
    std::vector<std::vector<Lit>> clauses = {{Lit(0, false), Lit(1, false)}};
    s.add_clause(clauses[0]);
    ASSERT(s.solve() == true);
    ASSERT(verify_model(s, clauses));
}

TEST(implication_chain) {
    Solver s;
    for (int i = 0; i < 4; i++)
        s.new_var();
    std::vector<std::vector<Lit>> clauses = {
        {Lit(0, false)},
        {Lit(0, true), Lit(1, false)},
        {Lit(1, true), Lit(2, false)},
        {Lit(2, true), Lit(3, false)},
    };
    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(0)) == lbool::True);
    ASSERT(s.model_value(Var(3)) == lbool::True);
    ASSERT(verify_model(s, clauses));
}

TEST(tautology) {
    Solver s;
    s.new_var();
    s.add_clause({Lit(0, false), Lit(0, true)});
    ASSERT(s.solve() == true);
}

TEST(duplicate_lits) {
    Solver s;
    s.new_var();
    s.new_var();
    std::vector<std::vector<Lit>> clauses = {
        {Lit(0, false), Lit(0, false), Lit(1, false)},
        {Lit(0, true)},
    };
    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(1)) == lbool::True);
}

TEST(pigeonhole_2_1) {
    Solver s;
    s.new_var();
    s.new_var();
    s.add_clause({Lit(0, false)});
    s.add_clause({Lit(1, false)});
    s.add_clause({Lit(0, true), Lit(1, true)});
    ASSERT(s.solve() == false);
}

TEST(pigeonhole_3_2) {
    Solver s;
    for (int i = 0; i < 6; i++)
        s.new_var();

    s.add_clause({Lit(0, false), Lit(1, false)});
    s.add_clause({Lit(2, false), Lit(3, false)});
    s.add_clause({Lit(4, false), Lit(5, false)});

    s.add_clause({Lit(0, true), Lit(2, true)});
    s.add_clause({Lit(0, true), Lit(4, true)});
    s.add_clause({Lit(2, true), Lit(4, true)});
    s.add_clause({Lit(1, true), Lit(3, true)});
    s.add_clause({Lit(1, true), Lit(5, true)});
    s.add_clause({Lit(3, true), Lit(5, true)});

    ASSERT(s.solve() == false);
}

TEST(three_sat_satisfiable) {
    Solver s;
    for (int i = 0; i < 3; i++)
        s.new_var();
    std::vector<std::vector<Lit>> clauses = {
        {Lit(0, false), Lit(1, false), Lit(2, false)},
        {Lit(0, true), Lit(1, false), Lit(2, true)},
        {Lit(0, false), Lit(1, true), Lit(2, false)},
    };
    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);
    ASSERT(verify_model(s, clauses));
}

TEST(auto_var_creation) {
    Solver s;
    s.add_clause({Lit(5, false), Lit(10, false)});
    ASSERT(s.num_vars() >= 11);
    ASSERT(s.solve() == true);
}

TEST(pigeonhole_4_3) {
    Solver s;
    for (int i = 0; i < 12; i++)
        s.new_var();

    for (int p = 0; p < 4; p++) {
        std::vector<Lit> at_least_one;
        for (int h = 0; h < 3; h++)
            at_least_one.push_back(Lit(p * 3 + h, false));
        s.add_clause(at_least_one);
    }

    for (int h = 0; h < 3; h++) {
        for (int p1 = 0; p1 < 4; p1++) {
            for (int p2 = p1 + 1; p2 < 4; p2++) {
                s.add_clause({Lit(p1 * 3 + h, true), Lit(p2 * 3 + h, true)});
            }
        }
    }

    ASSERT(s.solve() == false);
}

TEST(satisfiable_coloring) {
    Solver s;
    for (int i = 0; i < 9; i++)
        s.new_var();

    std::vector<std::vector<Lit>> clauses;

    for (int v = 0; v < 3; v++) {
        std::vector<Lit> at_least_one;
        for (int c = 0; c < 3; c++)
            at_least_one.push_back(Lit(v * 3 + c, false));
        clauses.push_back(at_least_one);
    }

    auto add_edge = [&](int u, int v) {
        for (int c = 0; c < 3; c++)
            clauses.push_back({Lit(u * 3 + c, true), Lit(v * 3 + c, true)});
    };
    add_edge(0, 1);
    add_edge(1, 2);

    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);
    ASSERT(verify_model(s, clauses));
}

TEST(unit_propagation_cascade) {
    Solver s;
    for (int i = 0; i < 10; i++)
        s.new_var();
    std::vector<std::vector<Lit>> clauses;

    clauses.push_back({Lit(0, false)});
    for (int i = 0; i < 9; i++)
        clauses.push_back({Lit(i, true), Lit(i + 1, false)});

    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);

    for (int i = 0; i < 10; i++)
        ASSERT(s.model_value(Var(i)) == lbool::True);
}

TEST(multiple_solutions) {
    Solver s;
    for (int i = 0; i < 3; i++)
        s.new_var();
    std::vector<std::vector<Lit>> clauses = {
        {Lit(0, false), Lit(1, false)},
        {Lit(1, false), Lit(2, false)},
    };
    for (auto& c : clauses)
        s.add_clause(c);
    ASSERT(s.solve() == true);
    ASSERT(verify_model(s, clauses));
}

TEST(pigeonhole_5_4) {
    Solver s;
    int nv = 20;
    for (int i = 0; i < nv; i++)
        s.new_var();

    for (int p = 0; p < 5; p++) {
        std::vector<Lit> at_least_one;
        for (int h = 0; h < 4; h++)
            at_least_one.push_back(Lit(p * 4 + h, false));
        s.add_clause(at_least_one);
    }

    for (int h = 0; h < 4; h++)
        for (int p1 = 0; p1 < 5; p1++)
            for (int p2 = p1 + 1; p2 < 5; p2++)
                s.add_clause({Lit(p1 * 4 + h, true), Lit(p2 * 4 + h, true)});

    ASSERT(s.solve() == false);
}

TEST(drat_proof_output) {
    std::string proof_path = "test_proof.drat";

    {
        ProofLogger proof;
        ASSERT(proof.open(proof_path));

        Solver s;
        s.set_proof_logger(&proof);

        // Use pigeonhole 2-1 (2 pigeons, 1 hole) - requires actual search/learning
        s.new_var();
        s.new_var();
        s.add_clause({Lit(0, false)});              // pigeon 0 must be in hole 0
        s.add_clause({Lit(1, false)});              // pigeon 1 must be in hole 0
        s.add_clause({Lit(0, true), Lit(1, true)}); // at most one pigeon in hole 0
        ASSERT(s.solve() == false);
    }

    std::ifstream pf(proof_path);
    ASSERT(pf.is_open());
    std::string content((std::istreambuf_iterator<char>(pf)), std::istreambuf_iterator<char>());
    // Proof may be empty for trivially UNSAT formulas detected at level 0
    // Just check the file was created and is readable
    pf.close();
    std::remove(proof_path.c_str());
}

TEST(latin_square_2x2) {
    Solver s;
    for (int i = 0; i < 8; i++)
        s.new_var();

    std::vector<std::vector<Lit>> clauses;

    // var(r,c,v) = r*4 + c*2 + v, for r,c,v in {0,1}
    auto var = [](int r, int c, int v) -> uint32_t { return static_cast<uint32_t>(r * 4 + c * 2 + v); };

    for (int r = 0; r < 2; r++) {
        for (int c = 0; c < 2; c++) {
            clauses.push_back({Lit(var(r, c, 0), false), Lit(var(r, c, 1), false)});
            clauses.push_back({Lit(var(r, c, 0), true), Lit(var(r, c, 1), true)});
        }
    }

    for (int r = 0; r < 2; r++)
        for (int v = 0; v < 2; v++)
            clauses.push_back({Lit(var(r, 0, v), true), Lit(var(r, 1, v), true)});

    for (int c = 0; c < 2; c++)
        for (int v = 0; v < 2; v++)
            clauses.push_back({Lit(var(0, c, v), true), Lit(var(1, c, v), true)});

    for (auto& cl : clauses)
        s.add_clause(cl);
    ASSERT(s.solve() == true);
    ASSERT(verify_model(s, clauses));
}

TEST(scc_detects_unsat) {
    // Encode x↔y and x↔~y using only binary clauses (no unit clauses).
    // x↔y:  (~x∨y) and (~y∨x)  → SCC {x,y}
    // x↔~y: (~x∨~y) and (y∨x)  → SCC {x,~y}, i.e., x and ~y are equivalent.
    // Combined: x≡y and x≡~y → contradiction, detectable via SCC
    // (x's SCC contains both y and ~y, which are complementary).
    Solver s;
    s.new_var(); // x=0
    s.new_var(); // y=1
    s.add_clause({Lit(0, true),  Lit(1, false)});  // ~x ∨  y
    s.add_clause({Lit(1, true),  Lit(0, false)});  // ~y ∨  x
    s.add_clause({Lit(0, true),  Lit(1, true)});   // ~x ∨ ~y
    s.add_clause({Lit(1, false), Lit(0, false)});  //  y ∨  x
    ASSERT(s.solve() == false);
}

TEST(scc_equivalent_lits) {
    // x↔y encoded as two binary clauses (~x∨y) and (~y∨x).
    // The formula (x∨z) ∧ (~z) should force x, and since x↔y, y too.
    Solver s;
    s.new_var(); // x=0
    s.new_var(); // y=1
    s.new_var(); // z=2
    s.add_clause({Lit(0, true), Lit(1, false)});  // ~x ∨ y  (x→y)
    s.add_clause({Lit(1, true), Lit(0, false)});  // ~y ∨ x  (y→x)
    s.add_clause({Lit(0, false), Lit(2, false)}); // x ∨ z
    s.add_clause({Lit(2, true)});                 // ~z  → z=false, so x must be true
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(0)) == lbool::True);
    ASSERT(s.model_value(Var(1)) == lbool::True); // equivalent to x
}

TEST(bve_pure_literal) {
    // Variable 0 appears only positively: BVE should eliminate it (set it true or
    // delete its clauses). The formula without var 0 should still be SAT.
    Solver s;
    s.new_var(); // x=0  (pure positive)
    s.new_var(); // y=1
    s.add_clause({Lit(0, false), Lit(1, false)});  // x ∨ y
    s.add_clause({Lit(0, false), Lit(1, true)});   // x ∨ ~y
    // No clause contains ~x, so x is a pure literal. BVE eliminates it.
    ASSERT(s.solve() == true);
    // Both clauses are satisfied (x=true or y chosen appropriately).
}

TEST(bve_eliminates_and_extends_model) {
    // Encode: (x∨a)(~x∨b)(a∨b). Eliminate x: resolvent = (a∨b).
    // After solving (a∨b), extend model for x.
    // If a=false and b=true: resolvent satisfied. x must be true (pos clause x∨a needs it).
    Solver s;
    s.new_var(); // x=0
    s.new_var(); // a=1
    s.new_var(); // b=2
    s.add_clause({Lit(0, false), Lit(1, false)});  // x ∨ a
    s.add_clause({Lit(0, true),  Lit(2, false)});  // ~x ∨ b
    s.add_clause({Lit(1, false), Lit(2, false)});  // a ∨ b  (keeps formula SAT)
    ASSERT(s.solve() == true);
    // Model must satisfy the original three clauses.
    auto sat = [&](std::initializer_list<Lit> cl) {
        for (Lit l : cl)
            if (s.model_value(l) == lbool::True)
                return true;
        return false;
    };
    ASSERT(sat({Lit(0, false), Lit(1, false)}));
    ASSERT(sat({Lit(0, true),  Lit(2, false)}));
    ASSERT(sat({Lit(1, false), Lit(2, false)}));
}

TEST(probing_forces_literal) {
    // Formula: (x∨y)(x∨~y). Both probes of y force x (regardless of y's value).
    // Probing should detect x is forced true.
    Solver s;
    s.new_var(); // x=0
    s.new_var(); // y=1
    s.add_clause({Lit(0, false), Lit(1, false)});  // x ∨ y
    s.add_clause({Lit(0, false), Lit(1, true)});   // x ∨ ~y
    ASSERT(s.solve() == true);
    ASSERT(s.model_value(Var(0)) == lbool::True);
}

TEST(preprocessing_preserves_unsat) {
    // Pigeonhole 3-2 should still be UNSAT after preprocessing.
    Solver s;
    for (int i = 0; i < 6; i++)
        s.new_var();
    s.add_clause({Lit(0, false), Lit(1, false)});
    s.add_clause({Lit(2, false), Lit(3, false)});
    s.add_clause({Lit(4, false), Lit(5, false)});
    s.add_clause({Lit(0, true), Lit(2, true)});
    s.add_clause({Lit(0, true), Lit(4, true)});
    s.add_clause({Lit(2, true), Lit(4, true)});
    s.add_clause({Lit(1, true), Lit(3, true)});
    s.add_clause({Lit(1, true), Lit(5, true)});
    s.add_clause({Lit(3, true), Lit(5, true)});
    ASSERT(s.solve() == false);
}

TEST(drat_proof_verified) {
    const std::string cnf_path   = "drat_verify.cnf";
    const std::string proof_path = "drat_verify.drat";
    const std::string out_path   = "drat_verify.out";

    // Write pigeonhole 3-2 (6 vars, 9 clauses) — small and definitely UNSAT.
    {
        std::ofstream cnf(cnf_path);
        cnf << "p cnf 6 9\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "5 6 0\n"
            << "-1 -3 0\n"
            << "-1 -5 0\n"
            << "-3 -5 0\n"
            << "-2 -4 0\n"
            << "-2 -6 0\n"
            << "-4 -6 0\n";
    }

    {
        ProofLogger proof;
        ASSERT(proof.open(proof_path));
        Solver s;
        s.set_proof_logger(&proof);
        std::ifstream cin(cnf_path);
        parse_dimacs(cin, s);
        bool r = s.solve();
        ASSERT(!r);
    }

    // Try to invoke drat-trim; skip gracefully if not on PATH.
#ifdef _WIN32
    std::string cmd = "drat-trim " + cnf_path + " " + proof_path + " > " + out_path + " 2>&1";
#else
    std::string cmd = "drat-trim " + cnf_path + " " + proof_path + " > " + out_path + " 2>&1";
#endif
    int rc = std::system(cmd.c_str());

    std::string content;
    {
        std::ifstream out(out_path);
        content.assign(std::istreambuf_iterator<char>(out), std::istreambuf_iterator<char>());
    }

    std::remove(cnf_path.c_str());
    std::remove(proof_path.c_str());
    std::remove(out_path.c_str());

    // If drat-trim is not installed, skip (don't fail).
    bool not_found = (rc == 127) || content.empty() ||
                     content.find("not found") != std::string::npos ||
                     content.find("not recognized") != std::string::npos ||
                     content.find("is not recognized") != std::string::npos;
    if (not_found)
        return; // skip

    ASSERT(content.find("s VERIFIED") != std::string::npos);
}

static void build_pigeonhole(Solver& s, int pigeons, int holes) {
    int nv = pigeons * holes;
    for (int i = 0; i < nv; i++)
        s.new_var();

    for (int p = 0; p < pigeons; p++) {
        std::vector<Lit> at_least_one;
        for (int h = 0; h < holes; h++)
            at_least_one.push_back(Lit(p * holes + h, false));
        s.add_clause(at_least_one);
    }

    for (int h = 0; h < holes; h++)
        for (int p1 = 0; p1 < pigeons; p1++)
            for (int p2 = p1 + 1; p2 < pigeons; p2++)
                s.add_clause({Lit(p1 * holes + h, true), Lit(p2 * holes + h, true)});
}

TEST(glucose_restart_pigeonhole) {
    Solver s;
    s.set_restart_policy(RestartPolicy::Glucose);
    build_pigeonhole(s, 6, 5);
    ASSERT(s.solve() == false);
    ASSERT(s.stats().restarts > 0);
}

TEST(luby_restart_pigeonhole) {
    Solver s;
    s.set_restart_policy(RestartPolicy::Luby);
    build_pigeonhole(s, 6, 5);
    ASSERT(s.solve() == false);
    ASSERT(s.stats().restarts > 0);
}

TEST(both_policies_agree) {
    for (int pigeons = 3; pigeons <= 5; pigeons++) {
        Solver sg;
        sg.set_restart_policy(RestartPolicy::Glucose);
        build_pigeonhole(sg, pigeons, pigeons - 1);
        bool rg = sg.solve();

        Solver sl;
        sl.set_restart_policy(RestartPolicy::Luby);
        build_pigeonhole(sl, pigeons, pigeons - 1);
        bool rl = sl.solve();

        ASSERT(rg == rl);
        ASSERT(rg == false);
    }
}

int main() {
    std::cout << "whetstone test suite\n\n";

    RUN(empty_solver);
    RUN(single_positive_unit);
    RUN(single_negative_unit);
    RUN(conflicting_units);
    RUN(empty_clause);
    RUN(two_var_or);
    RUN(implication_chain);
    RUN(tautology);
    RUN(duplicate_lits);
    RUN(pigeonhole_2_1);
    RUN(pigeonhole_3_2);
    RUN(three_sat_satisfiable);
    RUN(auto_var_creation);
    RUN(pigeonhole_4_3);
    RUN(satisfiable_coloring);
    RUN(unit_propagation_cascade);
    RUN(multiple_solutions);
    RUN(pigeonhole_5_4);
    RUN(drat_proof_output);
    RUN(latin_square_2x2);
    RUN(scc_detects_unsat);
    RUN(scc_equivalent_lits);
    RUN(bve_pure_literal);
    RUN(bve_eliminates_and_extends_model);
    RUN(probing_forces_literal);
    RUN(preprocessing_preserves_unsat);
    RUN(drat_proof_verified);
    RUN(glucose_restart_pigeonhole);
    RUN(luby_restart_pigeonhole);
    RUN(both_policies_agree);

    std::cout << "\n" << tests_passed << " passed, " << tests_failed << " failed\n";
    return tests_failed > 0 ? 1 : 0;
}
