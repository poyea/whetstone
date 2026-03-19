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

// Solver: variable management

Var Solver::new_var() {
    Var v = m_num_vars++;
    m_assigns.push_back(lbool::Undef);
    m_vardata.push_back({CRef_Undef, 0});
    m_activity.push_back(0.0);
    m_polarity.push_back(false);
    m_seen.push_back(0);
    m_watches.emplace_back();
    m_watches.emplace_back();
    m_eliminated.push_back(false);
    m_scc_subst.push_back(Lit_Undef);
    m_order_heap.insert(v);
    return v;
}

// Solver: assignment and backtracking

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
