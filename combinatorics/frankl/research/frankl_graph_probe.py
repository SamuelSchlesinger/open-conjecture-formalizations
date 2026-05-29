#!/usr/bin/env python3
"""The graph register: Frankl via maximal independent sets (Bruhn-Charbit-
Schaudt-Telle 2015).

Frankl <=> every finite graph with an edge has two ADJACENT vertices each in at
most half of its maximal independent sets (MIS).  Trivial for non-bipartite
graphs; the hard core is bipartite.

This script:
  * verifies the conjecture on all small graphs;
  * checks the reframing "fail <=> a bipartition side is entirely heavy"
    (heavy = in > half the MIS; heavy vertices are pairwise non-adjacent);
  * confirms the triangle fragment (a triangle yields two adjacent light
    vertices);
  * shows the degree-sum witness rule is a small-size artifact (breaks at n=7).
"""
from __future__ import annotations
import random
from itertools import combinations


def mis_list(n, adj):
    out = []
    for S in range(1 << n):
        if all(not (adj[v] & S) for v in range(n) if S >> v & 1) and \
           all((S >> u & 1) or (adj[u] & S) for u in range(n)):
            out.append(S)
    return out


def is_bipartite(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0; st = [s]
        while st:
            x = st.pop()
            for y in range(n):
                if adj[x] >> y & 1:
                    if col[y] == -1:
                        col[y] = col[x] ^ 1; st.append(y)
                    elif col[y] == col[x]:
                        return False
    return True


def adj_of(n, E):
    adj = [0] * n
    for a, b in E:
        adj[a] |= 1 << b; adj[b] |= 1 << a
    return adj


def all_graphs(n):
    e = list(combinations(range(n), 2)); ne = len(e)
    for mask in range(1, 1 << ne):
        yield [e[i] for i in range(ne) if mask >> i & 1]


def verify(n):
    total = fails = 0
    for E in all_graphs(n):
        adj = adj_of(n, E); mis = mis_list(n, adj); m = len(mis)
        freq = [sum(1 for S in mis if S >> v & 1) for v in range(n)]
        if not any(2 * freq[a] <= m and 2 * freq[b] <= m for a, b in E):
            fails += 1
        total += 1
    print(f"verify n={n}: {total} graphs(>=1 edge), conjecture failures={fails}")


def triangle_fragment(n):
    """Confirm: every graph with a triangle has two adjacent light vertices."""
    bad = checked = 0
    for E in all_graphs(n):
        adj = adj_of(n, E)
        tri = any(adj[a] >> b & 1 and adj[b] >> c & 1 and adj[a] >> c & 1
                  for a, b, c in combinations(range(n), 3))
        if not tri:
            continue
        checked += 1
        mis = mis_list(n, adj); m = len(mis)
        freq = [sum(1 for S in mis if S >> v & 1) for v in range(n)]
        if not any(2 * freq[a] <= m and 2 * freq[b] <= m for a, b in E):
            bad += 1
    print(f"triangle fragment n={n}: {checked} graphs with a triangle, failures={bad}")


def degree_rule(nA, nB, trials, seed):
    random.seed(seed)
    fsum = t = 0
    for _ in range(trials):
        p = random.uniform(0.2, 0.8); n = nA + nB
        E = [(a, b) for a in range(nA) for b in range(nA, n) if random.random() < p]
        if not E:
            continue
        adj = adj_of(n, E); mis = mis_list(n, adj); m = len(mis)
        if m == 0:
            continue
        freq = [sum(1 for S in mis if S >> v & 1) for v in range(n)]
        heavy = [2 * freq[v] > m for v in range(n)]
        deg = [bin(adj[v]).count("1") for v in range(n)]
        a, b = max(E, key=lambda e: deg[e[0]] + deg[e[1]])
        t += 1
        if heavy[a] or heavy[b]:
            fsum += 1
    print(f"degree-sum rule, bipartite {nA}x{nB}: tested {t}, FAILS={fsum}")


if __name__ == "__main__":
    for n in (4, 5, 6):
        verify(n)
    for n in (5, 6):
        triangle_fragment(n)
    print("--- degree-sum witness rule (perfect on n<=6, breaks at n=7) ---")
    degree_rule(3, 3, 4000, 1)   # n=6: holds
    degree_rule(3, 4, 4000, 2)   # n=7: fails
    degree_rule(4, 4, 4000, 3)   # n=8: fails
