#!/usr/bin/env python3
"""Adversarial search to break condition (★) for the lattice form of Frankl.

(★): ∃ join-irreducible x with |⋃_{coatoms m ⊉ x} ↓m| ≥ |↑x|  (a sound
sufficient condition for the lattice Frankl conjecture; see
`lattice_frankl_attack.md`).

`lattice_frankl_attack.py` found zero failures on "nice" lattices (closure
systems, partition/subspace lattices).  This script targets the structures where
the trapped-element gap should be largest:

  * subgroup lattices of small groups (Woodroofe's hard class),
  * height-3 lattices from random/engineered bipartite atom–coatom incidences,

and reports the SLACK of (★)  =  max_{join-irred x} (|⋃ ↓m| − |↑x|).
slack < 0  ⟺  (★) FAILS  ⟺  a genuine counterexample to (★) (still Frankl-true).
"""

from __future__ import annotations
import random
from itertools import combinations, permutations, product


# --------------------------------------------------------------------------
# General finite-lattice analyzer:  elems is a list, leq(a,b) a relation.
# --------------------------------------------------------------------------

def analyze(elems, leq):
    n = len(elems)
    bot = next(e for e in elems if all(leq(e, f) for f in elems))
    top = next(e for e in elems if all(leq(f, e) for f in elems))
    dnc = {e: [f for f in elems if leq(f, e)] for e in elems}
    upc = {e: [f for f in elems if leq(e, f)] for e in elems}
    jm = {}

    def join(a, b):
        if (a, b) in jm:
            return jm[(a, b)]
        ub = [c for c in elems if leq(a, c) and leq(b, c)]
        best = min(ub, key=lambda c: len(dnc[c]))
        jm[(a, b)] = best
        return best

    JI = []
    for x in elems:
        if x == bot:
            continue
        below = [a for a in dnc[x] if a != x]
        if not any(join(a, b) == x for a in below for b in below):
            JI.append(x)
    coat = [m for m in elems if m != top and leq(m, top) and
            not any(leq(m, z) and m != z and leq(z, top) and z != top for z in elems)]

    # Frankl: some join-irreducible has |↑x| ≤ |L|/2
    frankl = any(2 * len(upc[j]) <= n for j in JI)
    min_up = min(len(upc[j]) for j in JI)

    # (★) slack: max over join-irreducibles of |⋃_{coatoms m ⊉ x} ↓m| − |↑x|
    def star_slack(x):                        # |⋃_{coatoms m ⊉ x} ↓m| − |↑x|
        union = set()
        for m in coat:
            if not leq(x, m):                 # x ⊄ m
                for e in dnc[m]:
                    union.add(_key(e))
        return len(union) - len(upc[x])
    slack = max(star_slack(x) for x in JI)
    return dict(n=n, frankl=frankl, min_up=min_up, half=n / 2, ncoat=len(coat),
                nJI=len(JI), star_slack=slack, star_ok=(slack >= 0))


def _key(e):
    # hashable key for lattice elements (frozensets, ints, tuples already hashable)
    try:
        hash(e); return e
    except TypeError:
        return id(e)


# --------------------------------------------------------------------------
# Permutation groups and their subgroup lattices.
# --------------------------------------------------------------------------

def compose(p, q):                      # (p∘q)[i] = p[q[i]]
    return tuple(p[q[i]] for i in range(len(p)))

def identity(n):
    return tuple(range(n))

def generate(gens, n):
    e = identity(n)
    G = {e} | set(gens)
    frontier = list(G)
    while frontier:
        a = frontier.pop()
        for b in list(G):
            for c in (compose(a, b), compose(b, a)):
                if c not in G:
                    G.add(c); frontier.append(c)
    return frozenset(G)

def all_subgroups(G, n):
    e = identity(n)
    subs = {frozenset([e])}
    changed = True
    while changed:
        changed = False
        for H in list(subs):
            for g in G:
                if g in H:
                    continue
                K = generate(set(H) | {g}, n)
                if K not in subs:
                    subs.add(K); changed = True
    return sorted(subs, key=lambda H: (len(H), sorted(H)))

def subgroup_lattice_analysis(name, gens, n):
    G = generate(gens, n)
    subs = all_subgroups(G, n)
    r = analyze(subs, lambda A, B: A <= B)   # A ≤ B  iff  A ⊆ B
    print(f"{name}: |G|={len(G)}, #subgroups={r['n']}, coatoms={r['ncoat']}, JI={r['nJI']} | "
          f"Frankl(min|↑|={r['min_up']}≤{r['half']})={r['frankl']} | (★) slack={r['star_slack']} ok={r['star_ok']}")
    return r


# --------------------------------------------------------------------------
# Height-3 bipartite lattices: bottom, atoms A, coatoms C, top; a≤c iff (a,c)∈I.
# This is a lattice iff joins/meets are unique; we just test candidates.
# --------------------------------------------------------------------------

def height3_lattice(p, q, inc):
    """p atoms (0..p-1), q coatoms (0..q-1), inc set of (atom,coatom) pairs.
    Elements: ('bot',), ('a',i), ('c',j), ('top',).  Returns (elems, leq) or None
    if not a lattice."""
    bot = ('bot',); top = ('top',)
    atoms = [('a', i) for i in range(p)]
    coats = [('c', j) for j in range(q)]
    elems = [bot] + atoms + coats + [top]
    below = {bot: set(), top: set(elems) - {top}}
    for i in range(p):
        below[('a', i)] = {bot}
    for j in range(q):
        below[('c', j)] = {bot} | {('a', i) for i in range(p) if (i, j) in inc}
    below[top] = set(elems) - {top}
    def leq(x, y):
        return x == y or x in below.get(y, set())
    # lattice test: every pair has a unique least upper bound and greatest lower bound
    def has_unique_lub(x, y):
        ub = [c for c in elems if leq(x, c) and leq(y, c)]
        lub = [c for c in ub if all(leq(c, d) for d in ub)]
        return len(lub) == 1
    def has_unique_glb(x, y):
        lb = [c for c in elems if leq(c, x) and leq(c, y)]
        glb = [c for c in lb if all(leq(d, c) for d in lb)]
        return len(glb) == 1
    for x in elems:
        for y in elems:
            if not has_unique_lub(x, y) or not has_unique_glb(x, y):
                return None
    return elems, leq


def search_height3(p, q, trials, seed, dense=False):
    random.seed(seed)
    pairs = [(i, j) for i in range(p) for j in range(q)]
    worst = None
    fails = 0; tested = 0
    for _ in range(trials):
        prob = random.uniform(0.3, 0.85)
        inc = set(pr for pr in pairs if random.random() < prob)
        L = height3_lattice(p, q, inc)
        if L is None:
            continue
        elems, leq = L
        r = analyze(elems, leq)
        tested += 1
        if not r['star_ok']:
            fails += 1
            print(f"  (★) FAILS! p={p} q={q} inc={sorted(inc)} -> {r}")
        if worst is None or r['star_slack'] < worst[0]:
            worst = (r['star_slack'], r['frankl'], sorted(inc))
    print(f"height3 p={p} q={q}: tested={tested} lattices, (★) fails={fails}, "
          f"min slack={worst[0] if worst else None} (frankl={worst[1] if worst else None})")


def bouquet(k, m):
    """k chains of length m from ⊥, joined only at ⊤ (a 'fan of chains')."""
    bot = ('bot',); top = ('top',)
    elems = [bot, top] + [('c', i, j) for i in range(k) for j in range(m)]
    def leq(x, y):
        if x == y or x == bot or y == top:
            return True
        if x[0] == 'c' and y[0] == 'c' and x[1] == y[1]:
            return x[2] <= y[2]
        return False
    return elems, leq


def chain_vs_fan(chain_len, w):
    """A long private chain (its top a coatom) plus `w` atom-coatoms; designed to
    create a large trapped-element gap on the chain side."""
    bot = ('bot',); top = ('top',)
    chain = [('b', j) for j in range(chain_len)]
    fan = [('a', i) for i in range(w)]
    elems = [bot, top] + chain + fan
    def leq(x, y):
        if x == y or x == bot or y == top:
            return True
        if x[0] == 'b' and y[0] == 'b':
            return x[1] <= y[1]
        return False
    return elems, leq


if __name__ == "__main__":
    print("== subgroup lattices ==")
    subgroup_lattice_analysis("S_3", [(1, 0, 2), (1, 2, 0)], 3)
    subgroup_lattice_analysis("D_4", [(1, 2, 3, 0), (3, 2, 1, 0)], 4)
    subgroup_lattice_analysis("A_4", [(1, 2, 0, 3), (0, 2, 3, 1)], 4)
    subgroup_lattice_analysis("S_4", [(1, 2, 3, 0), (1, 0, 2, 3)], 4)
    subgroup_lattice_analysis("D_5", [(1, 2, 3, 4, 0), (4, 3, 2, 1, 0)], 5)
    subgroup_lattice_analysis("D_6", [(1, 2, 3, 4, 5, 0), (5, 4, 3, 2, 1, 0)], 6)
    print("== height-3 adversarial bipartite lattices (targeting trapped gaps) ==")
    for (p, q) in [(3, 3), (4, 3), (3, 4), (4, 4), (5, 4), (4, 5), (5, 5), (6, 5)]:
        search_height3(p, q, 3000, seed=p * 100 + q)
    print("== engineered constructions (self-balancing stress) ==")
    for k, m in [(2, 3), (3, 3), (4, 2), (5, 2), (3, 4), (6, 2), (4, 4)]:
        e, leq = bouquet(k, m); r = analyze(e, leq)
        print(f"  bouquet k={k} m={m}: |L|={r['n']} Frankl={r['frankl']} (★)slack={r['star_slack']} ok={r['star_ok']}")
    for cl, w in [(4, 2), (6, 2), (8, 2), (8, 3), (10, 2), (6, 4)]:
        e, leq = chain_vs_fan(cl, w); r = analyze(e, leq)
        print(f"  chain_vs_fan len={cl} w={w}: |L|={r['n']} Frankl={r['frankl']} (★)slack={r['star_slack']} ok={r['star_ok']}")
