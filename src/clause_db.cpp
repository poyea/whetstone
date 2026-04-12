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
    // Sort worst-first so the bottom half contains the best deletion candidates.
    // Primary key: LBD tier (higher tier = worse quality = sort to the front):
    //   tier 2: LBD >= 4  -- main deletion pool
    //   tier 1: LBD == 3  -- near-glue, protected below but sorted after tier 2
    //   tier 0: LBD <= 2  -- glue clauses, always kept
    // Secondary key: activity ascending (least recently useful first).
    std::sort(m_learnts.begin(), m_learnts.end(),
              [this](CRef a, CRef b) {
                  const Clause& ca = m_ca[a];
                  const Clause& cb = m_ca[b];
                  auto tier = [](uint32_t lbd) -> uint32_t {
                      return lbd <= 2 ? 0 : lbd == 3 ? 1 : 2;
                  };
                  uint32_t ta = tier(ca.lbd), tb = tier(cb.lbd);
                  if (ta != tb)
                      return ta > tb;
                  return ca.activity < cb.activity;
              });

    // Delete the bottom (worst) half, subject to hard protection rules:
    //   LBD <= 2  glue clauses:   never delete -- they behave like original clauses
    //   LBD == 3  near-glue:      never delete -- kept "longer" via full tier protection
    //   size <= 2 binary:         never delete -- binary propagation handles these separately
    //   recently used:            never delete -- active in last 10k conflicts regardless of score
    //   i >= limit                in the better half of the sort: never delete
    static constexpr uint64_t recency_window = 10000;
    size_t limit = m_learnts.size() / 2;
    size_t j = 0;
    for (size_t i = 0; i < m_learnts.size(); i++) {
        Clause& c = m_ca[m_learnts[i]];
        bool recently_used = c.used_at > 0 && (m_stats.conflicts - c.used_at) < recency_window;
        bool keep = c.lbd <= 3 || c.size() <= 2 || recently_used || i >= limit;
        if (!keep) {
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

// Solver: clause vivification
// For each learnt clause, negate its literals one-by-one at level 0 and
// propagate. A conflict before the end means the clause is subsumed and can
// be deleted. A unit propagation before the end means the prefix so far
// implies the last enqueued literal -- shorten the clause to that prefix.
void Solver::vivify() {
    if (!m_ok || decision_level() != 0)
        return;
    if (propagate() != CRef_Undef) {
        m_ok = false;
        return;
    }

    // Snapshot so that newly-added shortened clauses are not re-vivified.
    const std::vector<CRef> candidates = m_learnts;

    for (CRef cr : candidates) {
        if (!m_ok)
            break;
        Clause& c = m_ca[cr];
        if (c.deleted() || c.size() <= 2)
            continue;

        new_decision_level();

        std::vector<Lit> prefix;
        bool conflict_found = false;
        bool sat_at_zero    = false;

        for (uint32_t i = 0; i < c.size() && !conflict_found && !sat_at_zero; i++) {
            Lit   l   = c[i];
            lbool val = value(l);
            if (val == lbool::True) {
                // Clause is satisfied by a level-0 unit -- delete it outright.
                if (level(l.var()) == 0)
                    sat_at_zero = true;
                break;
            }
            if (val == lbool::False)
                continue; // Already falsified at level 0; skip literal.
            prefix.push_back(l);
            unchecked_enqueue(~l);
            if (propagate() != CRef_Undef)
                conflict_found = true;
        }

        cancel_until(0);

        // No shortening possible -- leave the clause unchanged.
        if (!sat_at_zero && !conflict_found && prefix.size() == c.size())
            continue;

        uint32_t old_lbd = c.lbd;

        // Log the shortened clause before deleting the original (DRAT ordering).
        if (!sat_at_zero && prefix.size() >= 2 && m_proof)
            m_proof->add_clause(prefix);

        if (m_proof)
            m_proof->delete_clause(c);
        detach_clause(cr);
        c.mark_deleted();

        if (sat_at_zero)
            continue; // Nothing to replace -- subsumed by level-0 truth.

        if (prefix.empty()) {
            // All literals were falsified at level 0 -- contradiction.
            m_ok = false;
        } else if (prefix.size() == 1) {
            if (m_proof)
                m_proof->add_unit(prefix[0]);
            if (value(prefix[0]) == lbool::Undef) {
                unchecked_enqueue(prefix[0]);
                if (propagate() != CRef_Undef)
                    m_ok = false;
            }
        } else {
            CRef new_cr = alloc_clause(prefix, /*learnt=*/true);
            m_ca[new_cr].lbd = old_lbd; // LBD-on-reuse will refine this later.
            m_learnts.push_back(new_cr);
            attach_clause(new_cr);
        }
    }

    // Compact m_learnts: remove entries that were deleted above.
    m_learnts.erase(
        std::remove_if(m_learnts.begin(), m_learnts.end(),
                       [&](CRef r) { return m_ca[r].deleted(); }),
        m_learnts.end());
}
