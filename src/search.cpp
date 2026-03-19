#include "solver.hpp"

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

    if (!preprocess())
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

    if (status == lbool::True)
        extend_model();

    return status == lbool::True;
}

lbool Solver::model_value(Var v) const {
    return m_assigns[v];
}

lbool Solver::model_value(Lit l) const {
    return m_assigns[l.var()] ^ l.sign();
}
