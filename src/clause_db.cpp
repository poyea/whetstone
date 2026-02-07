#include "solver.hpp"

// Solver: clause allocation and watch management

CRef Solver::alloc_clause(const std::vector<Lit>& lits, bool learnt) {
    return m_ca.alloc(lits, learnt);
}

void Solver::attach_clause(CRef cr) {
    Clause& c = m_ca[cr];
    assert(c.size() >= 2);
    bool bin = (c.size() == 2);
    m_watches[(~c[0]).index()].push_back({cr, c[1], bin});
    m_watches[(~c[1]).index()].push_back({cr, c[0], bin});
}

void Solver::detach_clause(CRef cr) {
    Clause& c = m_ca[cr];
    auto remove = [](std::vector<Watcher>& ws, CRef target) {
        for (size_t i = 0; i < ws.size(); i++) {
            if (ws[i].cref == target) {
                ws[i] = ws.back();
                ws.pop_back();
                return;
            }
        }
    };
    remove(m_watches[(~c[0]).index()], cr);
    remove(m_watches[(~c[1]).index()], cr);
}

bool Solver::add_clause(std::vector<Lit> lits) {
    if (!m_ok)
        return false;

    for (auto l : lits) {
        while (l.var() >= m_num_vars)
            new_var();
    }

    std::sort(lits.begin(), lits.end());

    size_t j = 0;
    for (size_t i = 0; i < lits.size(); i++) {
        if (i > 0 && lits[i] == lits[i - 1])
            continue;
        if (i > 0 && lits[i] == ~lits[i - 1])
            return true;
        if (value(lits[i]) == lbool::True)
            return true;
        if (value(lits[i]) == lbool::False)
            continue;
        lits[j++] = lits[i];
    }
    lits.resize(j);

    if (lits.empty()) {
        m_ok = false;
        return false;
    }

    if (lits.size() == 1) {
        unchecked_enqueue(lits[0]);
        m_ok = (propagate() == CRef_Undef);
        return m_ok;
    }

    CRef cr = alloc_clause(lits, false);
    m_original.push_back(cr);
    attach_clause(cr);
    return true;
}

// Solver: clause database reduction

void Solver::reduce_db() {
    std::sort(m_learnts.begin(), m_learnts.end(),
              [this](CRef a, CRef b) { return m_ca[a].activity < m_ca[b].activity; });

    size_t limit = m_learnts.size() / 2;
    size_t j = 0;
    for (size_t i = 0; i < m_learnts.size(); i++) {
        Clause& c = m_ca[m_learnts[i]];
        if (i < limit && c.size() > 2 && c.lbd > 2) {
            if (m_proof)
                m_proof->delete_clause(c);
            c.mark_deleted();
            detach_clause(m_learnts[i]);
        } else {
            m_learnts[j++] = m_learnts[i];
        }
    }
    m_learnts.resize(j);
}
