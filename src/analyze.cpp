#include "solver.hpp"

// Solver: clause minimization

bool Solver::lit_redundant(Lit p, uint32_t abs_levels) {
    m_minimize_stack.clear();
    m_minimize_stack.push_back(p);

    size_t top = m_minimize_toclear.size();

    while (!m_minimize_stack.empty()) {
        Lit q = m_minimize_stack.back();
        m_minimize_stack.pop_back();

        CRef r = reason(q.var());
        Clause& c = m_ca[r];

        for (uint32_t i = 1; i < c.size(); i++) {
            Lit l = c[i];
            Var v = l.var();

            if (m_seen[v] || level(v) == 0)
                continue;

            if (reason(v) == CRef_Undef || (abstract_level(level(v)) & abs_levels) == 0) {
                for (size_t k = top; k < m_minimize_toclear.size(); k++)
                    m_seen[m_minimize_toclear[k].var()] = 0;
                m_minimize_toclear.resize(top);
                return false;
            }

            m_seen[v] = 1;
            m_minimize_stack.push_back(l);
            m_minimize_toclear.push_back(l);
        }
    }

    return true;
}

// Solver: conflict analysis (1-UIP + minimization)

void Solver::analyze(CRef conflict, std::vector<Lit>& out_learnt, uint32_t& out_bt_level) {
    int path_count = 0;
    Lit p = Lit_Undef;
    int index = static_cast<int>(m_trail.size()) - 1;

    out_learnt.clear();
    out_learnt.push_back(Lit_Undef);

    do {
        Clause& c = m_ca[conflict];

        if (c.learnt()) {
            clause_bump_activity(c);
            // LBD can only decrease over the life of a clause. Recomputing it
            // here (while all literals are still assigned) promotes the clause
            // to a better protection tier if the current search context is
            // tighter than when it was first learned.
            uint32_t new_lbd = compute_lbd(c);
            if (new_lbd < c.lbd)
                c.lbd = new_lbd;
            // Record when this clause was last useful. reduce_db uses this to
            // protect recently-active clauses independently of their activity score.
            c.used_at = m_stats.conflicts;
        }

        // On-the-fly self-subsuming resolution: any literal at position >= 2
        // that is already in the partial learnt clause (m_seen != 0) would be
        // skipped by the processing loop below anyway, so it can be permanently
        // removed from this reason clause right now. Positions 0 and 1 are left
        // untouched to preserve the two-watched-literal invariant.
        if (p != Lit_Undef) {
            bool any = false;
            for (uint32_t j = 2; j < c.size() && !any; j++)
                any = (m_seen[c[j].var()] != 0);
            if (any) {
                if (m_proof) {
                    // DRAT order: log the shortened clause (add) before deleting
                    // the original. The shortened clause is RUP-implied by the
                    // existing formula and the partial learnt clause.
                    std::vector<Lit> shortened;
                    for (uint32_t j = 0; j < c.size(); j++)
                        if (j < 2 || !m_seen[c[j].var()])
                            shortened.push_back(c[j]);
                    m_proof->add_clause(shortened);
                    m_proof->delete_clause(c);
                }
                uint32_t new_sz = c.size();
                for (uint32_t j = 2; j < new_sz; ) {
                    if (m_seen[c[j].var()])
                        c[j] = c[--new_sz];
                    else
                        j++;
                }
                c.header = (new_sz << 2) | (c.header & 3);
            }
        }

        uint32_t start = (p == Lit_Undef) ? 0 : 1;
        for (uint32_t j = start; j < c.size(); j++) {
            Lit q = c[j];
            Var v = q.var();

            if (m_seen[v] || level(v) == 0)
                continue;

            m_seen[v] = 1;
            var_bump_activity(v);

            if (level(v) >= decision_level())
                path_count++;
            else
                out_learnt.push_back(q);
        }

        // Find the next seen variable at the CURRENT decision level
        while (index >= 0) {
            Var v = m_trail[index].var();
            if (m_seen[v] && level(v) >= decision_level())
                break;
            index--;
        }

        if (index < 0)
            break;

        p = m_trail[index--];
        m_seen[p.var()] = 0;
        path_count--;

        if (path_count <= 0)
            break;

        conflict = reason(p.var());
    } while (conflict != CRef_Undef);

    out_learnt[0] = ~p;

    m_minimize_toclear.assign(out_learnt.begin(), out_learnt.end());

    uint32_t abs_levels = 0;
    for (size_t i = 1; i < out_learnt.size(); i++)
        abs_levels |= abstract_level(level(out_learnt[i].var()));

    size_t j = 1;
    for (size_t i = 1; i < out_learnt.size(); i++) {
        if (reason(out_learnt[i].var()) == CRef_Undef || !lit_redundant(out_learnt[i], abs_levels))
            out_learnt[j++] = out_learnt[i];
    }
    out_learnt.resize(j);

    // Clear seen flags for all variables (both minimize_toclear and any left from early
    // loop exit)
    for (auto l : m_minimize_toclear)
        m_seen[l.var()] = 0;
    for (auto l : m_trail)
        m_seen[l.var()] = 0;

    if (out_learnt.size() == 1) {
        out_bt_level = 0;
    } else {
        uint32_t max_i = 1;
        for (uint32_t i = 2; i < static_cast<uint32_t>(out_learnt.size()); i++) {
            if (level(out_learnt[i].var()) > level(out_learnt[max_i].var()))
                max_i = i;
        }
        std::swap(out_learnt[1], out_learnt[max_i]);
        out_bt_level = level(out_learnt[1].var());
    }
}
