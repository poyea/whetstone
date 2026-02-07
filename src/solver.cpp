#include "solver.hpp"

// VarOrderHeap

void Solver::VarOrderHeap::percolate_up(int i) {
    Var x = m_heap[i];
    while (i > 0) {
        int parent = (i - 1) / 2;
        if (!lt(x, m_heap[parent]))
            break;
        m_heap[i] = m_heap[parent];
        m_pos[m_heap[i]] = i;
        i = parent;
    }
    m_heap[i] = x;
    m_pos[x] = i;
}

void Solver::VarOrderHeap::percolate_down(int i) {
    Var x = m_heap[i];
    int size = static_cast<int>(m_heap.size());
    while (true) {
        int child = 2 * i + 1;
        if (child >= size)
            break;
        if (child + 1 < size && lt(m_heap[child + 1], m_heap[child]))
            child++;
        if (!lt(m_heap[child], x))
            break;
        m_heap[i] = m_heap[child];
        m_pos[m_heap[i]] = i;
        i = child;
    }
    m_heap[i] = x;
    m_pos[x] = i;
}

void Solver::VarOrderHeap::insert(Var v) {
    if (v >= static_cast<Var>(m_pos.size()))
        m_pos.resize(v + 1, -1);
    if (m_pos[v] >= 0)
        return;
    m_pos[v] = static_cast<int>(m_heap.size());
    m_heap.push_back(v);
    percolate_up(static_cast<int>(m_heap.size()) - 1);
}

Var Solver::VarOrderHeap::remove_min() {
    Var x = m_heap[0];
    m_pos[x] = -1;
    if (m_heap.size() > 1) {
        m_heap[0] = m_heap.back();
        m_pos[m_heap[0]] = 0;
        m_heap.pop_back();
        percolate_down(0);
    } else {
        m_heap.pop_back();
    }
    return x;
}

void Solver::VarOrderHeap::update(Var v) {
    if (contains(v))
        percolate_up(m_pos[v]);
}

// Solver: variable and clause management

Var Solver::new_var() {
    Var v = m_num_vars++;
    m_assigns.push_back(lbool::Undef);
    m_vardata.push_back({CRef_Undef, 0});
    m_activity.push_back(0.0);
    m_polarity.push_back(false);
    m_seen.push_back(0);
    m_watches.emplace_back();
    m_watches.emplace_back();
    m_order_heap.insert(v);
    return v;
}

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

// Solver: assignment

void Solver::unchecked_enqueue(Lit p, CRef from) {
    assert(value(p) == lbool::Undef);
    m_assigns[p.var()] = p.sign() ? lbool::False : lbool::True;
    m_vardata[p.var()] = {from, decision_level()};
    m_trail.push_back(p);
}

void Solver::cancel_until(uint32_t lvl) {
    if (decision_level() <= lvl)
        return;

    for (int i = static_cast<int>(m_trail.size()) - 1; i >= static_cast<int>(m_trail_lim[lvl]); i--) {
        Var v = m_trail[i].var();
        m_assigns[v] = lbool::Undef;
        m_polarity[v] = m_trail[i].sign();
        if (!m_order_heap.contains(v))
            m_order_heap.insert(v);
    }

    m_trail.resize(m_trail_lim[lvl]);
    m_trail_lim.resize(lvl);
    m_qhead = static_cast<uint32_t>(m_trail.size());
}

// Solver: propagation (2-watched literals + binary fast path)

CRef Solver::propagate() {
    CRef conflict = CRef_Undef;

    while (m_qhead < m_trail.size()) {
        Lit p = m_trail[m_qhead++];
        m_stats.propagations++;

        std::vector<Watcher>& ws = m_watches[p.index()];

        size_t i = 0, j = 0;
        while (i < ws.size()) {
            if (ws[i].binary) {
                Lit implied = ws[i].blocker;
                ws[j++] = ws[i++];

                if (value(implied) == lbool::True)
                    continue;

                if (value(implied) == lbool::False) {
                    conflict = ws[j - 1].cref;
                    while (i < ws.size())
                        ws[j++] = ws[i++];
                    break;
                }

                unchecked_enqueue(implied, ws[j - 1].cref);
                continue;
            }

            Lit blocker = ws[i].blocker;
            if (value(blocker) == lbool::True) {
                ws[j++] = ws[i++];
                continue;
            }

            CRef cr = ws[i].cref;
            Clause& c = m_ca[cr];

            Lit false_lit = ~p;
            if (c[0] == false_lit)
                std::swap(c[0], c[1]);
            assert(c[1] == false_lit);

            Lit first = c[0];
            Watcher w = {cr, first, false};

            if (first != blocker && value(first) == lbool::True) {
                ws[j++] = w;
                i++;
                continue;
            }

            bool found = false;
            for (uint32_t k = 2; k < c.size(); k++) {
                if (value(c[k]) != lbool::False) {
                    std::swap(c[1], c[k]);
                    m_watches[(~c[1]).index()].push_back({cr, first, false});
                    i++;
                    found = true;
                    break;
                }
            }
            if (found)
                continue;

            ws[j++] = w;
            i++;

            if (value(first) == lbool::False) {
                conflict = cr;
                while (i < ws.size())
                    ws[j++] = ws[i++];
            } else {
                unchecked_enqueue(first, cr);
            }
        }
        ws.resize(j);

        if (conflict != CRef_Undef)
            break;
    }

    return conflict;
}

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

        if (c.learnt())
            clause_bump_activity(c);

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

// Solver: search

double Solver::luby(double y, int x) {
    int size = 1, seq = 0;
    while (size < x + 1) {
        size = 2 * size + 1;
        seq++;
    }
    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }
    return std::pow(y, seq);
}

lbool Solver::search(int nof_conflicts) {
    int conflict_count = 0;
    std::vector<Lit> learnt_clause;

    for (;;) {
        CRef conflict = propagate();

        if (conflict != CRef_Undef) {
            m_stats.conflicts++;
            conflict_count++;
            m_conflicts_since_restart++;

            if (decision_level() == 0)
                return lbool::False;

            uint32_t bt_level;
            analyze(conflict, learnt_clause, bt_level);
            cancel_until(bt_level);

            uint32_t lbd = 0;

            if (learnt_clause.size() == 1) {
                unchecked_enqueue(learnt_clause[0]);
                if (m_proof)
                    m_proof->add_unit(learnt_clause[0]);
                lbd = 1;
            } else {
                if (m_proof)
                    m_proof->add_clause(learnt_clause);
                lbd = compute_lbd(learnt_clause);
                CRef cr = alloc_clause(learnt_clause, true);
                m_learnts.push_back(cr);
                attach_clause(cr);
                clause_bump_activity(m_ca[cr]);
                m_ca[cr].lbd = lbd;
                unchecked_enqueue(learnt_clause[0], cr);
            }

            m_ema_lbd_fast.update(static_cast<double>(lbd));
            m_ema_lbd_slow.update(static_cast<double>(lbd));

            var_decay_activity();
            clause_decay_activity();

            if (m_restart_policy == RestartPolicy::Glucose && m_ema_lbd_slow.ready() &&
                m_conflicts_since_restart > m_glucose_min_conflicts &&
                m_ema_lbd_fast.value * m_glucose_margin > m_ema_lbd_slow.value) {
                cancel_until(0);
                m_conflicts_since_restart = 0;
                return lbool::Undef;
            }
        } else {
            if (m_restart_policy == RestartPolicy::Luby && nof_conflicts >= 0 && conflict_count >= nof_conflicts) {
                cancel_until(0);
                m_conflicts_since_restart = 0;
                return lbool::Undef;
            }

            if (m_learnts.size() >= m_original.size() + m_trail.size())
                reduce_db();

            Lit next = pick_branch_lit();
            if (next == Lit_Undef)
                return lbool::True;

            new_decision_level();
            unchecked_enqueue(next);
        }
    }
}

bool Solver::solve() {
    if (!m_ok)
        return false;

    lbool status = lbool::Undef;

    while (status == lbool::Undef) {
        if (m_restart_policy == RestartPolicy::Luby) {
            double rest = luby(2.0, m_luby_restart_count) * 100;
            status = search(static_cast<int>(rest));
            m_luby_restart_count++;
        } else {
            status = search(-1);
        }
        m_stats.restarts++;
    }

    return status == lbool::True;
}

lbool Solver::model_value(Var v) const {
    return m_assigns[v];
}

lbool Solver::model_value(Lit l) const {
    return m_assigns[l.var()] ^ l.sign();
}
