#include "solver.hpp"

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
