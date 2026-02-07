#!/usr/bin/env python3
"""Generate standard SAT benchmark CNF files."""

import os
import random
import sys

OUT_DIR = os.path.dirname(os.path.abspath(__file__))


def write_cnf(filename, num_vars, clauses):
    path = os.path.join(OUT_DIR, filename)
    with open(path, "w") as f:
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(str(l) for l in clause) + " 0\n")
    print(f"  {filename}: {num_vars} vars, {len(clauses)} clauses")


def pigeonhole(pigeons, holes):
    """PHP(n+1, n) is UNSAT. More pigeons than holes."""
    num_vars = pigeons * holes
    clauses = []

    def var(p, h):
        return p * holes + h + 1

    for p in range(pigeons):
        clauses.append([var(p, h) for h in range(holes)])

    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([-var(p1, h), -var(p2, h)])

    write_cnf(f"php-{pigeons}-{holes}.cnf", num_vars, clauses)


def random_3sat(num_vars, ratio, seed=42):
    """Random 3-SAT at given clause/variable ratio. Phase transition at ~4.267."""
    num_clauses = int(num_vars * ratio)
    rng = random.Random(seed)
    clauses = []

    for _ in range(num_clauses):
        vs = rng.sample(range(1, num_vars + 1), 3)
        clause = [v if rng.random() < 0.5 else -v for v in vs]
        clauses.append(clause)

    tag = "sat" if ratio < 4.267 else "thresh"
    write_cnf(f"random-3sat-{tag}-{num_vars}.cnf", num_vars, clauses)


def graph_coloring(num_vertices, edges, num_colors):
    """Graph k-coloring as SAT."""
    num_vars = num_vertices * num_colors
    clauses = []

    def var(v, c):
        return v * num_colors + c + 1

    for v in range(num_vertices):
        clauses.append([var(v, c) for c in range(num_colors)])

    for v in range(num_vertices):
        for c1 in range(num_colors):
            for c2 in range(c1 + 1, num_colors):
                clauses.append([-var(v, c1), -var(v, c2)])

    for u, v in edges:
        for c in range(num_colors):
            clauses.append([-var(u, c), -var(v, c)])

    write_cnf(
        f"color-v{num_vertices}-e{len(edges)}-k{num_colors}.cnf",
        num_vars,
        clauses,
    )


def queens(n):
    """N-queens as SAT."""
    num_vars = n * n
    clauses = []

    def var(r, c):
        return r * n + c + 1

    for r in range(n):
        clauses.append([var(r, c) for c in range(n)])

    for c in range(n):
        clauses.append([var(r, c) for r in range(n)])

    for r in range(n):
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-var(r, c1), -var(r, c2)])

    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append([-var(r1, c), -var(r2, c)])

    for r in range(n):
        for c in range(n):
            for k in range(1, n):
                if r + k < n and c + k < n:
                    clauses.append([-var(r, c), -var(r + k, c + k)])
                if r + k < n and c - k >= 0:
                    clauses.append([-var(r, c), -var(r + k, c - k)])

    write_cnf(f"queens-{n}.cnf", num_vars, clauses)


def petersen_coloring():
    """Petersen graph 3-coloring (SAT)."""
    edges = [
        (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
        (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
        (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    ]
    graph_coloring(10, edges, 3)


def main():
    print("generating benchmarks...\n")

    print("pigeonhole (UNSAT):")
    for n in [5, 6, 7, 8, 9]:
        pigeonhole(n + 1, n)

    print("\nrandom 3-SAT (under-constrained, likely SAT):")
    for nv in [50, 100, 200]:
        random_3sat(nv, 3.0, seed=nv)

    print("\nrandom 3-SAT (phase transition, hard):")
    for nv in [50, 100, 150, 200]:
        random_3sat(nv, 4.267, seed=nv + 1000)

    print("\nn-queens (SAT for n >= 4):")
    for n in [8, 10, 12]:
        queens(n)

    print("\ngraph coloring:")
    petersen_coloring()

    print("\ndone.")


if __name__ == "__main__":
    main()
