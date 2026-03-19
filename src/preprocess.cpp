#include "solver.hpp"
#include <algorithm>
#include <numeric>

bool Solver::preprocess() {
    if (!m_ok || m_num_vars == 0)
        return true;
    if (!run_scc())
        return false;
    if (!run_probing())
        return false;
    if (!run_bve())
        return false;
    return m_ok;
}

void Solver::extend_model() {
    // Process elimination records in reverse order: later-eliminated vars first.
    // For each var v eliminated by BVE: set v=true iff some positive occurrence
    // clause has all its other literals false (i.e., v is needed to satisfy it).
    for (int i = static_cast<int>(m_elim_stack.size()) - 1; i >= 0; i--) {
        const auto& rec = m_elim_stack[i];
        bool need_true = false;
        for (const auto& witnesses : rec.pos_witnesses) {
            bool sat = false;
            for (Lit l : witnesses) {
                if (value(l) == lbool::True) {
                    sat = true;
                    break;
                }
            }
            if (!sat) {
                need_true = true;
                break;
            }
        }
        m_assigns[rec.v] = need_true ? lbool::True : lbool::False;
    }
}

// Tarjan's SCC on the binary implication graph.
// Binary clause (a ∨ b) adds edges ~a→b and ~b→a.

namespace {

struct TarjanSCC {
    uint32_t n;
    const std::vector<std::vector<uint32_t>>& g;
    std::vector<int> idx, low;
    std::vector<bool> on_stk;
    std::vector<uint32_t> stk, comp;
    int ctr = 0;
    uint32_t ncomp = 0;

    TarjanSCC(uint32_t n, const std::vector<std::vector<uint32_t>>& g)
        : n(n), g(g), idx(n, -1), low(n, 0), on_stk(n, false), comp(n, UINT32_MAX) {}

    void dfs(uint32_t v) {
        idx[v] = low[v] = ctr++;
        stk.push_back(v);
        on_stk[v] = true;
        for (uint32_t w : g[v]) {
            if (idx[w] == -1) {
                dfs(w);
                low[v] = std::min(low[v], low[w]);
            } else if (on_stk[w]) {
                low[v] = std::min(low[v], idx[w]);
            }
        }
        if (low[v] == idx[v]) {
            uint32_t id = ncomp++;
            uint32_t w;
            do {
                w = stk.back();
                stk.pop_back();
                on_stk[w] = false;
                comp[w] = id;
            } while (w != v);
        }
    }

    void run() {
        for (uint32_t i = 0; i < n; i++)
            if (idx[i] == -1)
                dfs(i);
    }
};

} // namespace

bool Solver::run_scc() {
    if (!m_ok)
        return false;

    uint32_t n = 2 * m_num_vars;
    std::vector<std::vector<uint32_t>> graph(n);

    // Build implication graph from binary clauses only.
    for (CRef cr : m_original) {
        const Clause& c = m_ca[cr];
        if (c.deleted() || c.size() != 2)
            continue;
        Lit a = c[0], b = c[1];
        graph[(~a).index()].push_back(b.index());
        graph[(~b).index()].push_back(a.index());
    }

    TarjanSCC ts(n, graph);
    ts.run();

    // Contradiction: literal and its negation in the same SCC.
    for (Var v = 0; v < m_num_vars; v++) {
        if (ts.comp[Lit(v, false).index()] == ts.comp[Lit(v, true).index()]) {
            m_ok = false;
            return false;
        }
    }

    // Build representative map: for each SCC, pick the minimum literal index.
    std::vector<uint32_t> scc_min(ts.ncomp, UINT32_MAX);
    for (uint32_t i = 0; i < n; i++)
        scc_min[ts.comp[i]] = std::min(scc_min[ts.comp[i]], i);

    // rep[lit_idx] = canonical literal index for that equivalence class.
    std::vector<uint32_t> rep(n);
    for (uint32_t i = 0; i < n; i++)
        rep[i] = scc_min[ts.comp[i]];

    // Check if any substitution is needed.
    bool any_subst = false;
    for (uint32_t i = 0; i < n; i++)
        if (rep[i] != i) {
            any_subst = true;
            break;
        }
    if (!any_subst)
        return true;

    // Also check: if rep[l] == (~l).index() for any l, that's a contradiction.
    // (the representative of l is ~l, which only happens if l and ~l share an SCC —
    // already caught above, but double-check via rep.)
    for (uint32_t i = 0; i < n; i++) {
        Lit l;
        l.x = i;
        if (rep[i] == (~l).index()) {
            m_ok = false;
            return false;
        }
    }

    // Apply substitution: rewrite every non-deleted clause in m_original.
    // Collect new clauses separately, then clean up.
    std::vector<std::vector<Lit>> new_clauses;
    std::vector<CRef> to_delete;

    uint32_t orig_size = static_cast<uint32_t>(m_original.size());
    for (uint32_t ci = 0; ci < orig_size; ci++) {
        CRef cr = m_original[ci];
        Clause& c = m_ca[cr];
        if (c.deleted())
            continue;

        // Build rewritten clause.
        std::vector<Lit> rewritten;
        bool tautology = false;
        for (uint32_t i = 0; i < c.size(); i++) {
            Lit l = c[i];
            // Skip already-false literals at level 0.
            if (value(l) == lbool::False)
                continue;
            // Already-true literal → clause satisfied, discard.
            if (value(l) == lbool::True) {
                tautology = true;
                break;
            }
            Lit rl;
            rl.x = rep[l.index()];
            // Check if ~rl already in rewritten → tautology.
            if (std::find(rewritten.begin(), rewritten.end(), ~rl) != rewritten.end()) {
                tautology = true;
                break;
            }
            if (std::find(rewritten.begin(), rewritten.end(), rl) == rewritten.end())
                rewritten.push_back(rl);
        }

        // Check if clause actually changed.
        bool changed = tautology || (rewritten.size() != c.size());
        if (!changed) {
            for (uint32_t i = 0; i < c.size(); i++)
                if (c[i] != rewritten[i]) {
                    changed = true;
                    break;
                }
        }
        if (!changed)
            continue;

        // Queue for deletion; proof logging happens after additions (DRAT order).
        to_delete.push_back(cr);

        if (!tautology && !rewritten.empty())
            new_clauses.push_back(std::move(rewritten));
    }

    // DRAT order: log all additions BEFORE any deletions.
    for (const auto& lits : new_clauses)
        if (m_proof)
            m_proof->add_clause(lits);

    // Detach, log deletion, and mark deleted.
    for (CRef cr : to_delete) {
        if (m_proof)
            m_proof->delete_clause(m_ca[cr]);
        detach_clause(cr);
        m_ca[cr].mark_deleted();
    }

    // Remove deleted CRefs from m_original.
    m_original.erase(
        std::remove_if(m_original.begin(), m_original.end(),
                       [&](CRef cr) { return m_ca[cr].deleted(); }),
        m_original.end());

    // Add rewritten clauses to the solver (may trigger BCP for units).
    for (auto& lits : new_clauses) {
        if (!m_ok)
            break;
        add_clause(lits);
    }

    return m_ok;
}

bool Solver::run_probing() {
    if (!m_ok)
        return false;

    // We need to be at level 0 and have a clean propagation queue.
    if (decision_level() != 0 || propagate() != CRef_Undef)
        return m_ok;

    std::vector<Lit> forced;

    for (Var v = 0; v < m_num_vars; v++) {
        if (!m_ok)
            break;
        if (value(v) != lbool::Undef || m_eliminated[v])
            continue;

        // --- Probe Lit(v, false) ---
        uint32_t save = static_cast<uint32_t>(m_trail.size());
        new_decision_level();
        unchecked_enqueue(Lit(v, false));
        CRef conflict = propagate();

        if (conflict != CRef_Undef) {
            // Lit(v, false) leads to conflict → force Lit(v, true).
            cancel_until(0);
            forced.push_back(Lit(v, true));
            continue;
        }

        // Collect literals implied under positive probe.
        // m_seen[var] = 1 → Lit(var,false) implied; 2 → Lit(var,true) implied.
        std::vector<Var> seen_vars;
        for (uint32_t i = save; i < m_trail.size(); i++) {
            Lit l = m_trail[i];
            if (l.var() == v)
                continue;
            uint8_t mark = l.sign() ? 2 : 1;
            if (m_seen[l.var()] == 0) {
                seen_vars.push_back(l.var());
            }
            m_seen[l.var()] = mark;
        }
        cancel_until(0);

        // --- Probe Lit(v, true) ---
        new_decision_level();
        unchecked_enqueue(Lit(v, true));
        conflict = propagate();

        if (conflict != CRef_Undef) {
            // Lit(v, true) leads to conflict → force Lit(v, false).
            cancel_until(0);
            for (Var sv : seen_vars)
                m_seen[sv] = 0;
            forced.push_back(Lit(v, false));
            continue;
        }

        // Collect intersection: literals implied under both probes.
        for (uint32_t i = save; i < m_trail.size(); i++) {
            Lit l = m_trail[i];
            if (l.var() == v)
                continue;
            uint8_t mark = l.sign() ? 2 : 1;
            if (m_seen[l.var()] == mark) {
                // Same polarity implied under both → forced.
                if (value(l) == lbool::Undef)
                    forced.push_back(l);
            }
        }

        cancel_until(0);
        for (Var sv : seen_vars)
            m_seen[sv] = 0;
    }

    // Apply forced literals at level 0.
    for (Lit l : forced) {
        if (!m_ok)
            break;
        if (value(l) == lbool::True)
            continue;
        if (value(l) == lbool::False) {
            m_ok = false;
            break;
        }
        if (m_proof)
            m_proof->add_unit(l);
        unchecked_enqueue(l);
    }

    if (m_ok && propagate() != CRef_Undef)
        m_ok = false;

    return m_ok;
}

bool Solver::run_bve() {
    if (!m_ok)
        return false;

    // Propagate any pending units before building occurrence lists.
    if (propagate() != CRef_Undef) {
        m_ok = false;
        return false;
    }

    // Build occurrence lists: pos_occ[v] = CRefs of clauses containing Lit(v,false).
    std::vector<std::vector<CRef>> pos_occ(m_num_vars), neg_occ(m_num_vars);
    for (CRef cr : m_original) {
        const Clause& c = m_ca[cr];
        if (c.deleted())
            continue;
        for (uint32_t i = 0; i < c.size(); i++) {
            Lit l = c[i];
            if (l.sign())
                neg_occ[l.var()].push_back(cr);
            else
                pos_occ[l.var()].push_back(cr);
        }
    }

    // Single-pass elimination: try each variable in order.
    for (Var v = 0; v < m_num_vars; v++) {
        if (!m_ok)
            break;
        if (value(v) != lbool::Undef || m_eliminated[v])
            continue;

        // Count live (non-deleted) occurrences.
        auto count_live = [&](const std::vector<CRef>& occ) -> size_t {
            size_t cnt = 0;
            for (CRef cr : occ)
                if (!m_ca[cr].deleted())
                    cnt++;
            return cnt;
        };
        size_t np = count_live(pos_occ[v]);
        size_t nn = count_live(neg_occ[v]);

        // Pure literal: appears in only one polarity → can be eliminated.
        // Do NOT log these deletions to the proof: pure literal elimination is not
        // directly DRAT-provable without a witness clause, and omitting the deletion
        // from the proof is safe (the checker keeps the clauses, which only helps RUP).
        if (np == 0 && nn > 0) {
            // v=false satisfies all neg clauses; set witness to no positive occurrences.
            m_elim_stack.push_back({v, {}});
            m_eliminated[v] = true;
            for (CRef cr : neg_occ[v]) {
                if (m_ca[cr].deleted())
                    continue;
                detach_clause(cr);
                m_ca[cr].mark_deleted();
            }
            continue;
        }
        if (nn == 0 && np > 0) {
            // v=true satisfies all pos clauses.
            m_elim_stack.push_back({v, {}});
            m_eliminated[v] = true;
            for (CRef cr : pos_occ[v]) {
                if (m_ca[cr].deleted())
                    continue;
                detach_clause(cr);
                m_ca[cr].mark_deleted();
            }
            continue;
        }
        if (np == 0 && nn == 0) {
            m_elim_stack.push_back({v, {}});
            m_eliminated[v] = true;
            continue;
        }

        // Check elimination cost: |pos|×|neg| ≤ |pos|+|neg| (net clause count won't grow).
        if (np * nn > np + nn)
            continue;

        // Gather live positive and negative clauses.
        std::vector<CRef> live_pos, live_neg;
        for (CRef cr : pos_occ[v])
            if (!m_ca[cr].deleted())
                live_pos.push_back(cr);
        for (CRef cr : neg_occ[v])
            if (!m_ca[cr].deleted())
                live_neg.push_back(cr);

        // Generate all non-tautological resolvents.
        std::vector<std::vector<Lit>> resolvents;
        bool unsat_found = false;

        for (CRef cp : live_pos) {
            const Clause& pos_c = m_ca[cp];
            for (CRef cn : live_neg) {
                const Clause& neg_c = m_ca[cn];

                // Build resolvent: (pos_c \ {v}) ∪ (neg_c \ {~v}).
                std::vector<Lit> res;
                res.reserve(pos_c.size() + neg_c.size() - 2);
                for (uint32_t i = 0; i < pos_c.size(); i++)
                    if (pos_c[i] != Lit(v, false))
                        res.push_back(pos_c[i]);
                for (uint32_t i = 0; i < neg_c.size(); i++)
                    if (neg_c[i] != Lit(v, true))
                        res.push_back(neg_c[i]);

                // Sort and deduplicate.
                std::sort(res.begin(), res.end());
                res.erase(std::unique(res.begin(), res.end()), res.end());

                // Check for tautology (l and ~l both present).
                bool tauto = false;
                for (size_t i = 1; i < res.size(); i++) {
                    if (res[i] == ~res[i - 1]) {
                        tauto = true;
                        break;
                    }
                }
                if (tauto)
                    continue;

                if (res.empty()) {
                    unsat_found = true;
                    break;
                }
                resolvents.push_back(std::move(res));
            }
            if (unsat_found)
                break;
        }

        if (unsat_found) {
            m_ok = false;
            return false;
        }

        // Build witness for model extension: store pos clause contents minus v.
        std::vector<std::vector<Lit>> pos_witnesses;
        for (CRef cp : live_pos) {
            const Clause& c = m_ca[cp];
            std::vector<Lit> others;
            for (uint32_t i = 0; i < c.size(); i++)
                if (c[i] != Lit(v, false))
                    others.push_back(c[i]);
            pos_witnesses.push_back(std::move(others));
        }

        // DRAT order: log all resolvents added BEFORE deleting originals.
        for (const auto& res : resolvents)
            if (m_proof)
                m_proof->add_clause(res);

        // Delete original clauses containing v or ~v.
        for (CRef cr : live_pos) {
            if (m_proof)
                m_proof->delete_clause(m_ca[cr]);
            detach_clause(cr);
            m_ca[cr].mark_deleted();
        }
        for (CRef cr : live_neg) {
            if (m_proof)
                m_proof->delete_clause(m_ca[cr]);
            detach_clause(cr);
            m_ca[cr].mark_deleted();
        }

        m_eliminated[v] = true;
        m_elim_stack.push_back({v, std::move(pos_witnesses)});

        // Add resolvents (may trigger BCP; propagate() is called by add_clause for units).
        for (const auto& res : resolvents) {
            if (!m_ok)
                break;
            add_clause(res);
        }
    }

    // Compact m_original: remove deleted CRefs.
    m_original.erase(
        std::remove_if(m_original.begin(), m_original.end(),
                       [&](CRef cr) { return m_ca[cr].deleted(); }),
        m_original.end());

    return m_ok;
}
