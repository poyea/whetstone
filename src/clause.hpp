#pragma once

#include "types.hpp"
#include <cassert>
#include <cstddef>
#include <vector>

/// @brief A disjunction (OR) of literals, stored inline in the clause arena.
///
/// Header packs size, learnt flag, and deleted flag into one word.
/// The flexible array `lits` is allocated contiguously after the header
/// by ClauseAllocator.
struct Clause {
    uint32_t header; // [31:2] size, [1] deleted, [0] learnt
    float activity;
    uint32_t lbd;
    Lit lits[1];

    uint32_t size() const { return header >> 2; }
    bool learnt() const { return header & 1; }
    bool deleted() const { return (header >> 1) & 1; }
    void mark_deleted() { header |= 2; }

    Lit& operator[](uint32_t i) { return lits[i]; }
    Lit operator[](uint32_t i) const { return lits[i]; }
};

/// @brief Arena allocator for clauses. A flat vector<uint32_t> region.
///
/// Clauses are laid out contiguously in memory for cache efficiency.
/// A CRef is simply an offset into this arena.
class ClauseAllocator {
    std::vector<uint32_t> m_mem;

    static constexpr uint32_t header_words() { return offsetof(Clause, lits) / sizeof(uint32_t); }

  public:
    CRef alloc(const std::vector<Lit>& lits, bool learnt) {
        uint32_t n = static_cast<uint32_t>(lits.size());
        CRef cr = static_cast<CRef>(m_mem.size());
        m_mem.resize(m_mem.size() + header_words() + n);

        Clause& c = (*this)[cr];
        c.header = (n << 2) | (learnt ? 1u : 0u);
        c.activity = 0.0f;
        c.lbd = 0;
        for (uint32_t i = 0; i < n; i++)
            c.lits[i] = lits[i];

        return cr;
    }

    Clause& operator[](CRef cr) { return *reinterpret_cast<Clause*>(&m_mem[cr]); }

    const Clause& operator[](CRef cr) const { return *reinterpret_cast<const Clause*>(&m_mem[cr]); }

    uint32_t capacity() const { return static_cast<uint32_t>(m_mem.size()); }
};
