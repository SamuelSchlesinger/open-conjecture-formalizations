#!/usr/bin/env python3
"""
Computational exploration of Tuza's conjecture  τ(G) ≤ 2·ν(G).

  ν(G) = max number of pairwise edge-disjoint triangles (a packing)
  τ(G) = min number of edges meeting every triangle (a cover)

For each graph we compute ν by brute force over subsets of triangles and τ by
searching covers in increasing size.  We:
  1. verify τ ≤ 2ν on all labelled graphs with n ≤ 5 (and the easy bounds
     ν ≤ τ ≤ 3ν), and on random graphs for n = 6, 7;
  2. record the distribution of the "slack" 2ν − τ and find the TIGHT graphs
     (τ = 2ν), confirming K₄ is the smallest.
"""
from itertools import combinations, product

def triangles_of(n, adj):
    return [frozenset(c) for c in combinations(range(n), 3)
            if adj[c[0]][c[1]] and adj[c[0]][c[2]] and adj[c[1]][c[2]]]

def edges_of(n, adj):
    return [frozenset(e) for e in combinations(range(n), 2) if adj[e[0]][e[1]]]

def tri_edges(t):
    return [frozenset(e) for e in combinations(sorted(t), 2)]

def nu(tris):
    """max edge-disjoint triangle packing (brute force)."""
    m = len(tris)
    te = [set(tri_edges(t)) for t in tris]
    best = 0
    # branch and bound over triangles
    def rec(i, used, count):
        nonlocal best
        if count + (m - i) <= best:
            return
        if i == m:
            best = max(best, count); return
        # skip triangle i
        rec(i + 1, used, count)
        # take triangle i if edge-disjoint from used
        if te[i].isdisjoint(used):
            rec(i + 1, used | te[i], count + 1)
    rec(0, set(), 0)
    return best

def tau(tris, edges):
    """min edges hitting every triangle (search by increasing size)."""
    if not tris:
        return 0
    tes = [set(tri_edges(t)) for t in tris]
    for k in range(0, len(edges) + 1):
        for F in combinations(edges, k):
            Fs = set(F)
            if all(te & Fs for te in tes):
                return k
    return len(edges)

def stats(n, adj):
    tris = triangles_of(n, adj)
    if not tris:
        return None
    edges = edges_of(n, adj)
    v = nu(tris); t = tau(tris, edges)
    return v, t

def all_graphs(n):
    pairs = list(combinations(range(n), 2))
    for bits in product((0, 1), repeat=len(pairs)):
        adj = [[False] * n for _ in range(n)]
        for (i, j), b in zip(pairs, bits):
            if b:
                adj[i][j] = adj[j][i] = True
        yield adj

def exhaustive(nmax=5):
    print("=" * 60)
    print(f"EXHAUSTIVE: τ ≤ 2ν on all labelled graphs, n ≤ {nmax}")
    print("=" * 60)
    for n in range(3, nmax + 1):
        worst_ratio = (0, 1)  # τ/ν as (num,den)
        tight = []
        viol = 0; cnt = 0
        for adj in all_graphs(n):
            s = stats(n, adj)
            if s is None:
                continue
            v, t = s
            cnt += 1
            assert v <= t <= 3 * v, f"sandwich fails n={n}: ν={v} τ={t}"
            if t > 2 * v:
                viol += 1
            if t * worst_ratio[1] > worst_ratio[0] * v:   # t/v > worst
                worst_ratio = (t, v)
            if t == 2 * v and v >= 1:
                tight.append(adj)
        print(f"n={n}: {cnt} graphs with triangles, violations(τ>2ν)={viol}, "
              f"max τ/ν = {worst_ratio[0]}/{worst_ratio[1]}, #tight(τ=2ν)={len(tight)}")
        if tight and n == 4:
            # show the tight graph on 4 vertices (should be K4)
            adj = tight[0]
            e = [ (i,j) for i,j in combinations(range(n),2) if adj[i][j] ]
            print(f"      smallest tight example (n=4): edges={e}  (K4 has 6 edges)")

import random
def random_check(n, trials, seed):
    random.seed(seed)
    worst = (0, 1); viol = 0; tested = 0; tightcount = 0
    pairs = list(combinations(range(n), 2))
    for _ in range(trials):
        adj = [[False] * n for _ in range(n)]
        for (i, j) in pairs:
            if random.random() < random.choice([0.4, 0.6, 0.8]):
                adj[i][j] = adj[j][i] = True
        s = stats(n, adj)
        if s is None:
            continue
        v, t = s
        tested += 1
        assert v <= t <= 3 * v
        if t > 2 * v:
            viol += 1
            print(f"  !!! VIOLATION n={n}: ν={v} τ={t}")
        if t == 2 * v and v >= 1:
            tightcount += 1
        if t * worst[1] > worst[0] * v:
            worst = (t, v)
    print(f"n={n}: {tested} sampled graphs, violations={viol}, "
          f"max τ/ν={worst[0]}/{worst[1]}, #tight={tightcount}")

if __name__ == "__main__":
    exhaustive(5)
    print("=" * 60)
    print("RANDOM: τ ≤ 2ν on sampled graphs, n = 6, 7")
    print("=" * 60)
    random_check(6, 3000, 1)
    random_check(7, 1500, 2)
    print("\nDONE.")
