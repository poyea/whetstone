#pragma once

#include <cstdint>
#include <cstdlib>
#include <functional>

/// @brief Propositional variable, identified by a zero-based index.
using Var = uint32_t;
constexpr Var Var_Undef = UINT32_MAX;

/// @brief A literal which is a variable with a polarity (positive or negative).
///
/// Encoded as `2*var + sign`, where sign=1 means negated.
/// `~lit` flips the polarity. Two literals per variable.
struct Lit {
    uint32_t x;

    constexpr Lit() : x(UINT32_MAX) {}
    constexpr Lit(Var v, bool sign) : x(v + v + static_cast<uint32_t>(sign)) {}

    Var var() const { return x >> 1; }
    bool sign() const { return x & 1; }
    uint32_t index() const { return x; }

    Lit operator~() const {
        Lit p;
        p.x = x ^ 1;
        return p;
    }

    bool operator==(Lit o) const { return x == o.x; }
    bool operator!=(Lit o) const { return x != o.x; }
    bool operator<(Lit o) const { return x < o.x; }

    static Lit from_dimacs(int32_t d) { return Lit(static_cast<Var>(std::abs(d)) - 1, d < 0); }

    int32_t to_dimacs() const {
        int32_t d = static_cast<int32_t>(var()) + 1;
        return sign() ? -d : d;
    }
};

constexpr Lit Lit_Undef{};

template <> struct std::hash<Lit> {
    size_t operator()(Lit l) const noexcept { return std::hash<uint32_t>{}(l.x); }
};

/// @brief Three-valued logic: True, False, or Undef (unassigned).
///
/// During search, variables start as Undef and are assigned True/False.
/// On backtracking they revert to Undef.
enum class lbool : uint8_t { True = 0, False = 1, Undef = 2 };

inline lbool operator^(lbool a, bool b) {
    if (a == lbool::Undef)
        return lbool::Undef;
    return static_cast<lbool>(static_cast<uint8_t>(a) ^ static_cast<uint8_t>(b));
}

/// @brief Clause reference. An offset into the clause arena allocator.
///
/// Acts as a stable handle to a clause. Cheaper than a pointer and
/// remains valid across arena growth (indices don't change).
using CRef = uint32_t;
constexpr CRef CRef_Undef = UINT32_MAX;
