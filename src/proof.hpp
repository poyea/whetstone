#pragma once

#include "types.hpp"
#include <fstream>
#include <vector>

class ProofLogger {
    std::ofstream m_out;

  public:
    bool open(const std::string& path) {
        m_out.open(path);
        return m_out.is_open();
    }

    bool active() const { return m_out.is_open(); }

    void add_clause(const std::vector<Lit>& lits) {
        if (!active())
            return;
        for (auto l : lits)
            m_out << l.to_dimacs() << " ";
        m_out << "0\n";
    }

    void add_unit(Lit l) {
        if (!active())
            return;
        m_out << l.to_dimacs() << " 0\n";
    }

    template <typename ClauseT> void delete_clause(const ClauseT& c) {
        if (!active())
            return;
        m_out << "d ";
        for (uint32_t i = 0; i < c.size(); i++)
            m_out << c[i].to_dimacs() << " ";
        m_out << "0\n";
    }
};
