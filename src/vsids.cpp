#include "solver.hpp"

// Solver: VSIDS

Lit Solver::pick_branch_lit() {
    Var next = Var_Undef;
    while (!m_order_heap.empty()) {
        next = m_order_heap.remove_min();
        if (value(next) == lbool::Undef)
            break;
        next = Var_Undef;
    }

    if (next == Var_Undef)
        return Lit_Undef;

    m_stats.decisions++;
    return Lit(next, m_polarity[next]);
}

void Solver::var_bump_activity(Var v) {
    m_activity[v] += m_var_inc;
    if (m_activity[v] > 1e100) {
        for (auto& a : m_activity)
            a *= 1e-100;
        m_var_inc *= 1e-100;
    }
    m_order_heap.update(v);
}

void Solver::var_decay_activity() {
    m_var_inc /= m_var_decay;
}

void Solver::clause_bump_activity(Clause& c) {
    c.activity += static_cast<float>(m_clause_inc);
    if (c.activity > 1e20f) {
        for (auto& cr : m_learnts)
            m_ca[cr].activity *= 1e-20f;
        m_clause_inc *= 1e-20;
    }
}

void Solver::clause_decay_activity() {
    m_clause_inc /= m_clause_decay;
}

uint32_t Solver::compute_lbd(const std::vector<Lit>& lits) {
    std::set<uint32_t> levels;
    for (auto l : lits)
        levels.insert(level(l.var()));
    return static_cast<uint32_t>(levels.size());
}
