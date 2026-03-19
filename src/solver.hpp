#pragma once

#include "clause.hpp"
#include "ema.hpp"
#include "proof.hpp"
#include "types.hpp"
#include <algorithm>
#include <cassert>
#include <cmath>
#include <set>
#include <vector>

/// @brief CDCL SAT solver with 2-watched literals, VSIDS, and proof logging.
class Solver {
  public:
    Var new_var();
    bool add_clause(std::vector<Lit> lits);
    bool solve();

    lbool model_value(Var v) const;
    lbool model_value(Lit l) const;
    uint32_t num_vars() const { return m_num_vars; }
    uint32_t num_clauses() const { return static_cast<uint32_t>(m_original.size()); }

    void set_proof_logger(ProofLogger* p) { m_proof = p; }
    void set_restart_policy(RestartPolicy p) { m_restart_policy = p; }

    struct Stats {
        uint64_t conflicts = 0;
        uint64_t decisions = 0;
        uint64_t propagations = 0;
        uint64_t restarts = 0;
    };
    const Stats& stats() const { return m_stats; }

  private:
    uint32_t m_num_vars = 0;
    bool m_ok = true;

    ClauseAllocator m_ca;
    std::vector<CRef> m_original;
    std::vector<CRef> m_learnts;

    /// @brief Entry in a watch list that tracks one clause watching a literal.
    struct Watcher {
        CRef cref;
        Lit blocker;
        bool binary;
    };
    std::vector<std::vector<Watcher>> m_watches;

    std::vector<lbool> m_assigns;
    std::vector<Lit> m_trail;
    std::vector<uint32_t> m_trail_lim;
    uint32_t m_qhead = 0;

    /// @brief Per-variable metadata: the reason clause and decision level.
    struct VarData {
        CRef reason = CRef_Undef;
        uint32_t level = 0;
    };
    std::vector<VarData> m_vardata;

    std::vector<double> m_activity;
    double m_var_inc = 1.0;
    static constexpr double m_var_decay = 0.95;

    double m_clause_inc = 1.0;
    static constexpr double m_clause_decay = 0.999;

    std::vector<bool> m_polarity;
    std::vector<uint8_t> m_seen;
    Stats m_stats;
    ProofLogger* m_proof = nullptr;

    RestartPolicy m_restart_policy = RestartPolicy::Glucose;
    EMA m_ema_lbd_fast{1.0 / 32};
    EMA m_ema_lbd_slow{1.0 / 4096};
    uint64_t m_conflicts_since_restart = 0;
    int m_luby_restart_count = 0;
    static constexpr double m_glucose_margin = 1.25;
    static constexpr uint64_t m_glucose_min_conflicts = 50;

    std::vector<Lit> m_minimize_stack;
    std::vector<Lit> m_minimize_toclear;

    std::vector<bool> m_eliminated;

    /// @brief SCC model extension: m_scc_subst[v] = canonical literal c such that v+ ≡ c.
    /// Lit_Undef means v was not substituted by SCC.
    std::vector<Lit> m_scc_subst;

    /// @brief Per-variable witness for model extension after BVE.
    /// pos_witnesses[i] = other literals in one positive occurrence of v[i].
    /// During extend_model(), if any witness clause has no true literal, v is set true.
    struct ElimRecord {
        Var v;
        std::vector<std::vector<Lit>> pos_witnesses;
    };
    std::vector<ElimRecord> m_elim_stack;

    bool preprocess();
    bool run_scc();
    bool run_bve();
    bool run_probing();
    void extend_model();

    /// @brief Binary min-heap ordered by VSIDS activity scores.
    class VarOrderHeap {
        std::vector<Var> m_heap;
        std::vector<int> m_pos;
        const std::vector<double>& m_activity;

        bool lt(Var a, Var b) const { return m_activity[a] > m_activity[b]; }
        void percolate_up(int i);
        void percolate_down(int i);

      public:
        explicit VarOrderHeap(const std::vector<double>& act) : m_activity(act) {}
        bool empty() const { return m_heap.empty(); }
        bool contains(Var v) const { return v < static_cast<Var>(m_pos.size()) && m_pos[v] >= 0; }
        void insert(Var v);
        Var remove_min();
        void update(Var v);
    };
    VarOrderHeap m_order_heap{m_activity};

    CRef alloc_clause(const std::vector<Lit>& lits, bool learnt);
    void attach_clause(CRef cr);
    void detach_clause(CRef cr);

    lbool value(Var v) const { return m_assigns[v]; }
    lbool value(Lit p) const { return m_assigns[p.var()] ^ p.sign(); }
    uint32_t level(Var v) const { return m_vardata[v].level; }
    CRef reason(Var v) const { return m_vardata[v].reason; }
    uint32_t decision_level() const { return static_cast<uint32_t>(m_trail_lim.size()); }

    static uint32_t abstract_level(uint32_t lvl) { return 1u << (lvl & 31); }

    void new_decision_level() { m_trail_lim.push_back(static_cast<uint32_t>(m_trail.size())); }
    void unchecked_enqueue(Lit p, CRef from = CRef_Undef);
    CRef propagate();
    void analyze(CRef conflict, std::vector<Lit>& out_learnt, uint32_t& out_bt_level);
    bool lit_redundant(Lit p, uint32_t abs_levels);
    void cancel_until(uint32_t level);
    Lit pick_branch_lit();

    void var_bump_activity(Var v);
    void var_decay_activity();
    void clause_bump_activity(Clause& c);
    void clause_decay_activity();
    void reduce_db();
    uint32_t compute_lbd(const std::vector<Lit>& lits);

    lbool search(int nof_conflicts);
    static double luby(double y, int x);
};
