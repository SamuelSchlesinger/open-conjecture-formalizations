#!/usr/bin/env python3
"""Explore the coupled-OR window for small union-closed families.

The experiment studies the following relaxation from
`entropy_transport_strategy.tex`.

Let F be a finite union-closed family and X uniform on F.  For a coupling
pi of two uniform copies X,Y, put Z = X OR Y and

    p_i = P[X_i = 1],      q_i = P[Z_i = 1].

The "window" asks whether a coupling can make

    p_i + gamma <= q_i <= 1 - p_i - gamma

simultaneously for a selected list of coordinates, with gamma > 0.
For one coordinate, the possible q_i values fill [p_i, min(1, 2 p_i)];
therefore exact centering at q_i = 1/2 is only possible when p_i >= 1/4.

For exact small cases, the script uses the Birkhoff-von Neumann theorem:
uniform couplings are convex combinations of permutation couplings.  It
projects all permutation-coupling q-vectors into their affine hull, computes a
small-dimensional convex hull by facet enumeration, and maximizes gamma by
enumerating vertices of the resulting halfspace LP.

With --scan-subsets, it tests every eligible coordinate subset up to
--max-coords, which probes whether critical centering survives for arbitrary
small subcollections rather than only the highest-frequency coordinates.
The --reduced-only and --maximal-only flags remove duplicate and dominated
coordinate traces, matching the normalizations one expects in a minimal
counterexample.
"""

from __future__ import annotations

import argparse
import itertools
import math
import random
from dataclasses import dataclass, replace
from typing import Iterable, Sequence

import numpy as np


Mask = int
Family = tuple[Mask, ...]


TOL = 1e-9


@dataclass(frozen=True)
class WindowResult:
    margin: float
    q: tuple[float, ...]
    exact: bool
    point_count: int
    affine_dim: int
    coords: tuple[int, ...]
    center_feasible: bool | None
    center_separator: tuple[float, ...] | None
    center_sample_bound: float | None
    center_target_value: float | None
    center_status: str | None = None
    center_iterations: int | None = None
    center_generation_points: int | None = None


@dataclass(frozen=True)
class CenterGenerationResult:
    status: str
    feasible: bool | None
    iterations: int
    point_count: int
    certificate: "CenterCertificate | None" = None


@dataclass(frozen=True)
class CenterCertificate:
    lambdas: tuple[float, ...]
    sample_bound: float
    target_value: float
    exact_max: float
    best_q: tuple[float, ...]
    verified_obstruction: bool


@dataclass(frozen=True)
class LambdaStressResult:
    slack: float
    lambdas: tuple[float, ...]
    diagonal_cone: float
    random_cone: float
    trace_slack: float | None
    trace_q: tuple[float, ...] | None
    target_value: float
    exact_max: float
    best_q: tuple[float, ...]


@dataclass(frozen=True)
class LambdaStressSummary:
    raw_best: LambdaStressResult
    cone_best: LambdaStressResult | None
    cone_trace_worst: LambdaStressResult | None


def bits(mask: Mask, n: int) -> str:
    """Print a set mask as a compact bitstring in coordinate order 0..n-1."""
    return format(mask, f"0{n}b")[::-1]


def family_str(F: Family, n: int) -> str:
    return "{" + ", ".join(bits(A, n) for A in F) + "}"


def is_union_closed(F: Family) -> bool:
    S = set(F)
    return all((A | B) in S for A in F for B in F)


def active_coords(F: Family, n: int) -> tuple[int, ...]:
    return tuple(i for i in range(n) if any((A >> i) & 1 for A in F))


def coordinate_signature(F: Family, i: int) -> tuple[int, ...]:
    return tuple((A >> i) & 1 for A in F)


def coordinate_implies(F: Family, i: int, j: int) -> bool:
    return all(((A >> i) & 1) <= ((A >> j) & 1) for A in F)


def maximal_trace_coords(F: Family, n: int, coords: Sequence[int]) -> tuple[int, ...]:
    active = active_coords(F, n)
    maximal = []
    for i in coords:
        dominated = any(
            i != j
            and coordinate_implies(F, i, j)
            and not coordinate_implies(F, j, i)
            for j in active
        )
        if not dominated:
            maximal.append(i)
    return tuple(maximal)


def is_coordinate_reduced(F: Family, n: int) -> bool:
    signatures = [coordinate_signature(F, i) for i in active_coords(F, n)]
    return len(signatures) == len(set(signatures))


def frequencies(F: Family, n: int) -> tuple[float, ...]:
    m = len(F)
    return tuple(sum(1 for A in F if (A >> i) & 1) / m for i in range(n))


def single_coordinate_q_range(F: Family, i: int) -> tuple[float, float]:
    """Exact q_i range over all uniform couplings for one coordinate."""
    p = frequencies(F, i + 1)[i]
    return p, min(1.0, 2.0 * p)


def frankl_witnesses(F: Family, n: int) -> tuple[int, ...]:
    p = frequencies(F, n)
    return tuple(i for i in active_coords(F, n) if p[i] >= 0.5 - TOL)


def all_union_closed_families(n: int) -> Iterable[Family]:
    masks = list(range(1 << n))
    for selector in range(1, 1 << (1 << n)):
        F = tuple(m for j, m in enumerate(masks) if (selector >> j) & 1)
        if is_union_closed(F):
            yield F


def row_allocations(total: int, caps: Sequence[int]) -> Iterable[tuple[int, ...]]:
    if len(caps) == 1:
        if total <= caps[0]:
            yield (total,)
        return
    for x in range(min(total, caps[0]) + 1):
        for rest in row_allocations(total - x, caps[1:]):
            yield (x,) + rest


def transport_matrices(supplies: Sequence[int]) -> Iterable[tuple[tuple[int, ...], ...]]:
    rows: list[tuple[int, ...]] = []

    def go(row_index: int, cols_left: tuple[int, ...]) -> Iterable[tuple[tuple[int, ...], ...]]:
        if row_index == len(supplies):
            if all(x == 0 for x in cols_left):
                yield tuple(rows)
            return
        for row in row_allocations(supplies[row_index], cols_left):
            rows.append(row)
            next_cols = tuple(cols_left[j] - row[j] for j in range(len(cols_left)))
            yield from go(row_index + 1, next_cols)
            rows.pop()

    yield from go(0, tuple(supplies))


def count_vectors(total: int, slots: int) -> Iterable[tuple[int, ...]]:
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in count_vectors(total - first, slots - 1):
            yield (first,) + rest


def support_union_closed(counts: Sequence[int]) -> bool:
    support = tuple(u for u, count in enumerate(counts) if count > 0)
    support_set = set(support)
    return all((u | v) in support_set for u in support for v in support)


def permute_trace(trace: int, permutation: Sequence[int]) -> int:
    permuted = 0
    for old_bit, new_bit in enumerate(permutation):
        if (trace >> old_bit) & 1:
            permuted |= 1 << new_bit
    return permuted


def canonical_trace_counts(counts: Sequence[int], coord_count: int) -> tuple[int, ...]:
    candidates = []
    for permutation in itertools.permutations(range(coord_count)):
        permuted = [0] * (1 << coord_count)
        for trace, count in enumerate(counts):
            permuted[permute_trace(trace, permutation)] = count
        candidates.append(tuple(permuted))
    return min(candidates)


def trace_counts(F: Family, coords: Sequence[int]) -> tuple[int, ...]:
    counts = [0] * (1 << len(coords))
    for A in F:
        trace = 0
        for j, coord in enumerate(coords):
            if (A >> coord) & 1:
                trace |= 1 << j
        counts[trace] += 1
    return tuple(counts)


def trace_transport_q_points(counts: Sequence[int], coord_count: int) -> list[tuple[float, ...]]:
    m = sum(counts)
    points: set[tuple[float, ...]] = set()
    for T in transport_matrices(counts):
        q = []
        for bit in range(coord_count):
            total = 0
            for u in range(1 << coord_count):
                for v in range(1 << coord_count):
                    if ((u | v) >> bit) & 1:
                        total += T[u][v]
            q.append(total / m)
        points.add(tuple(q))
    return sorted(points)


def closure_under_union(generators: Iterable[Mask]) -> Family:
    closed = set(generators)
    changed = True
    while changed:
        changed = False
        current = tuple(closed)
        for A in current:
            for B in current:
                C = A | B
                if C not in closed:
                    closed.add(C)
                    changed = True
    return tuple(sorted(closed))


def random_union_closed_family(
    n: int,
    generator_count: int,
    rng: random.Random,
    include_empty_probability: float = 0.35,
) -> Family:
    universe = list(range(1 << n))
    generators = {rng.choice(universe) for _ in range(generator_count)}
    if rng.random() < include_empty_probability:
        generators.add(0)
    return closure_under_union(generators)


def permutation_q_points(
    F: Family,
    coords: Sequence[int],
    max_exact_size: int,
    samples: int,
    rng: random.Random,
) -> tuple[list[tuple[float, ...]], bool]:
    """Return q-vectors from exact or sampled permutation couplings."""
    m = len(F)
    index_perms: Iterable[tuple[int, ...]]
    exact = m <= max_exact_size
    if exact:
        index_perms = itertools.permutations(range(m))
    else:
        perms: set[tuple[int, ...]] = {tuple(range(m))}
        reversed_perm = tuple(reversed(range(m)))
        perms.add(reversed_perm)
        while len(perms) < samples:
            arr = list(range(m))
            rng.shuffle(arr)
            perms.add(tuple(arr))
        index_perms = perms

    pts: set[tuple[float, ...]] = set()
    for perm in index_perms:
        vals = []
        for i in coords:
            count = 0
            for row, col in enumerate(perm):
                if ((F[row] | F[col]) >> i) & 1:
                    count += 1
            vals.append(count / m)
        pts.add(tuple(vals))
    return sorted(pts), exact


def affine_coordinates(points: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Return origin, basis, coordinates, affine dimension.

    Points are rows in R^d.  The returned basis has shape (d, r), and the
    coordinate matrix has rows y with point = origin + basis @ y.
    """
    origin = points[0]
    centered = points - origin
    if len(points) == 1:
        basis = np.zeros((points.shape[1], 0))
        coords = np.zeros((1, 0))
        return origin, basis, coords, 0
    _, singular_values, vt = np.linalg.svd(centered, full_matrices=False)
    rank = int(np.sum(singular_values > 1e-10))
    if rank == 0:
        basis = np.zeros((points.shape[1], 0))
        coords = np.zeros((len(points), 0))
        return origin, basis, coords, 0
    basis = vt[:rank].T
    coords = centered @ basis
    return origin, basis, coords, rank


def normalize_halfspace(a: np.ndarray, b: float) -> tuple[tuple[float, ...], float]:
    norm = float(np.linalg.norm(a))
    if norm <= TOL:
        raise ValueError("zero normal")
    a = a / norm
    b = b / norm
    rounded_a = tuple(float(round(x, 12)) for x in a)
    rounded_b = float(round(b, 12))
    return rounded_a, rounded_b


def convex_hull_halfspaces(coords: np.ndarray, rank: int) -> list[tuple[np.ndarray, float]]:
    """Compute an H-description of a small-dimensional convex hull.

    The input points are assumed to span R^rank.  This intentionally handles
    only rank <= 3; that is enough for the exhaustive experiments below and
    keeps the script dependency-free.
    """
    if rank == 0:
        return []
    if rank == 1:
        lo = float(np.min(coords[:, 0]))
        hi = float(np.max(coords[:, 0]))
        return [(np.array([1.0]), hi), (np.array([-1.0]), -lo)]
    if rank > 3:
        raise ValueError("exact hull fallback only supports affine dimension <= 3")

    seen: set[tuple[tuple[float, ...], float]] = set()
    halfspaces: list[tuple[np.ndarray, float]] = []
    for combo in itertools.combinations(range(len(coords)), rank):
        pts = coords[list(combo)]
        base = pts[0]
        diffs = pts[1:] - base
        if np.linalg.matrix_rank(diffs, tol=1e-10) < rank - 1:
            continue
        _, _, vt = np.linalg.svd(diffs)
        normal = vt[-1]
        offset = float(normal @ base)
        signed = coords @ normal - offset
        if np.all(signed <= 1e-8):
            a, b = normal, offset
        elif np.all(signed >= -1e-8):
            a, b = -normal, -offset
        else:
            continue
        key = normalize_halfspace(a, b)
        if key not in seen:
            seen.add(key)
            halfspaces.append((np.array(key[0]), key[1]))
    return halfspaces


def point_in_convex_hull(points: np.ndarray, target: np.ndarray) -> bool:
    origin, basis, hull_coords, rank = affine_coordinates(points)
    if rank == 0:
        return bool(np.linalg.norm(target - origin) <= 1e-8)
    y = basis.T @ (target - origin)
    residual = target - origin - basis @ y
    if np.linalg.norm(residual) > 1e-8:
        return False
    halfspaces = convex_hull_halfspaces(hull_coords, rank)
    return all(float(a @ y) <= b + 1e-8 for a, b in halfspaces)


def separating_lambda(
    points: np.ndarray,
    target: np.ndarray,
) -> tuple[np.ndarray, float, float] | None:
    """Find lambda with lambda.target > max lambda.points, if visible.

    This separates `target` from the convex hull represented by `points`.
    For sampled hulls this is only a sampled separator; it must be checked
    against the exact assignment problem before being trusted.
    """
    origin, basis, hull_coords, rank = affine_coordinates(points)
    if rank == 0:
        delta = target - origin
        if np.linalg.norm(delta) <= 1e-8:
            return None
        lambdas = delta
        return lambdas, float(np.max(points @ lambdas)), float(target @ lambdas)

    y = basis.T @ (target - origin)
    residual = target - origin - basis @ y
    if np.linalg.norm(residual) > 1e-8:
        lambdas = residual
        return lambdas, float(np.max(points @ lambdas)), float(target @ lambdas)

    halfspaces = convex_hull_halfspaces(hull_coords, rank)
    best: tuple[np.ndarray, float, float] | None = None
    best_gap = 0.0
    for a_y, b in halfspaces:
        gap = float(a_y @ y - b)
        if gap > best_gap + 1e-8:
            lambdas = basis @ a_y
            sample_bound = float(np.max(points @ lambdas))
            target_value = float(target @ lambdas)
            best = (lambdas, sample_bound, target_value)
            best_gap = target_value - sample_bound
    return best


def solve_halfspace_lp(
    constraints: Sequence[tuple[np.ndarray, float]],
    dimension: int,
    objective_index: int,
) -> tuple[float, np.ndarray] | None:
    """Maximize z[objective_index] over a small H-polytope by vertices."""
    best_value = -math.inf
    best_z: np.ndarray | None = None
    if dimension == 0:
        return None
    for active in itertools.combinations(range(len(constraints)), dimension):
        A = np.vstack([constraints[j][0] for j in active])
        b = np.array([constraints[j][1] for j in active])
        if np.linalg.matrix_rank(A, tol=1e-10) < dimension:
            continue
        try:
            z = np.linalg.solve(A, b)
        except np.linalg.LinAlgError:
            continue
        if all(float(a @ z) <= rhs + 1e-8 for a, rhs in constraints):
            value = float(z[objective_index])
            if value > best_value:
                best_value = value
                best_z = z
    if best_z is None:
        return None
    return best_value, best_z


def max_window_margin(
    q_points: Sequence[Sequence[float]],
    p_selected: Sequence[float],
    exact: bool,
    coords: Sequence[int],
) -> WindowResult | None:
    """Maximize gamma with p_i + gamma <= q_i <= 1-p_i-gamma."""
    if not coords:
        return None
    points = np.array(q_points, dtype=float)
    p = np.array(p_selected, dtype=float)
    origin, basis, hull_coords, rank = affine_coordinates(points)
    center_feasible: bool | None = None
    center_separator: tuple[float, ...] | None = None
    center_sample_bound: float | None = None
    center_target_value: float | None = None
    if bool(np.all((p >= 0.25 - TOL) & (p < 0.5 - TOL))):
        center = np.full(len(coords), 0.5)
        center_feasible = point_in_convex_hull(points, center)
        if not center_feasible:
            separated = separating_lambda(points, center)
            if separated is not None:
                lambdas, sample_bound, target_value = separated
                center_separator = tuple(float(x) for x in lambdas)
                center_sample_bound = sample_bound
                center_target_value = target_value

    if rank == 0:
        q = origin
        margin = float(np.min(np.minimum(q - p, 1 - p - q)))
        return WindowResult(
            margin=margin,
            q=tuple(float(x) for x in q),
            exact=exact,
            point_count=len(q_points),
            affine_dim=0,
            coords=tuple(coords),
            center_feasible=center_feasible,
            center_separator=center_separator,
            center_sample_bound=center_sample_bound,
            center_target_value=center_target_value,
        )

    halfspaces_y = convex_hull_halfspaces(hull_coords, rank)
    constraints: list[tuple[np.ndarray, float]] = []
    for a_y, b in halfspaces_y:
        a = np.zeros(rank + 1)
        a[:rank] = a_y
        constraints.append((a, b))

    for j in range(len(coords)):
        row = basis[j, :]

        # p_j + gamma <= origin_j + row*y
        a_lower = np.zeros(rank + 1)
        a_lower[:rank] = -row
        a_lower[-1] = 1.0
        constraints.append((a_lower, float(origin[j] - p[j])))

        # origin_j + row*y <= 1 - p_j - gamma
        a_upper = np.zeros(rank + 1)
        a_upper[:rank] = row
        a_upper[-1] = 1.0
        constraints.append((a_upper, float(1 - p[j] - origin[j])))

    solved = solve_halfspace_lp(constraints, rank + 1, rank)
    if solved is None:
        return None
    margin, z = solved
    y = z[:rank]
    q = origin + basis @ y
    return WindowResult(
        margin=float(margin),
        q=tuple(float(x) for x in q),
        exact=exact,
        point_count=len(q_points),
        affine_dim=rank,
        coords=tuple(coords),
        center_feasible=center_feasible,
        center_separator=center_separator,
        center_sample_bound=center_sample_bound,
        center_target_value=center_target_value,
    )


def max_weight_assignment(weights: Sequence[Sequence[float]]) -> tuple[float, list[int]]:
    """Maximum-weight perfect matching in a square matrix via Hungarian."""
    n = len(weights)
    if n == 0:
        return 0.0, []
    cost = [[-float(weights[i][j]) for j in range(n)] for i in range(n)]
    u = [0.0] * (n + 1)
    v = [0.0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)

    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [math.inf] * (n + 1)
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = math.inf
            j1 = 0
            for j in range(1, n + 1):
                if used[j]:
                    continue
                cur = cost[i0 - 1][j - 1] - u[i0] - v[j]
                if cur < minv[j]:
                    minv[j] = cur
                    way[j] = j0
                if minv[j] < delta:
                    delta = minv[j]
                    j1 = j
            for j in range(0, n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break

    assignment = [-1] * n
    for j in range(1, n + 1):
        if p[j] != 0:
            assignment[p[j] - 1] = j - 1
    value = sum(float(weights[i][assignment[i]]) for i in range(n))
    return value, assignment


def assignment_q(F: Family, coords: Sequence[int], assignment: Sequence[int]) -> tuple[float, ...]:
    m = len(F)
    vals = []
    for i in coords:
        count = 0
        for row, col in enumerate(assignment):
            if ((F[row] | F[col]) >> i) & 1:
                count += 1
        vals.append(count / m)
    return tuple(vals)


def exact_assignment_certificate(
    F: Family,
    coords: Sequence[int],
    lambdas: Sequence[float],
    sample_bound: float,
    target_value: float,
) -> CenterCertificate:
    """Optimize a coordinate separator over all permutation couplings."""
    m = len(F)
    weights = []
    for A in F:
        row = []
        for B in F:
            row.append(
                sum(
                    lambdas[j] * (1.0 if ((A | B) >> coord) & 1 else 0.0)
                    for j, coord in enumerate(coords)
                )
            )
        weights.append(row)
    max_sum, assignment = max_weight_assignment(weights)
    exact_max = max_sum / m
    return CenterCertificate(
        lambdas=tuple(float(x) for x in lambdas),
        sample_bound=sample_bound,
        target_value=target_value,
        exact_max=exact_max,
        best_q=assignment_q(F, coords, assignment),
        verified_obstruction=exact_max < target_value - 1e-8,
    )


def certify_center_separator(F: Family, result: WindowResult) -> CenterCertificate | None:
    """Check a sampled center separator against all permutation couplings."""
    if result.center_separator is None:
        return None
    lambdas = result.center_separator
    target_value = (
        result.center_target_value
        if result.center_target_value is not None
        else 0.5 * sum(lambdas)
    )
    sample_bound = (
        result.center_sample_bound
        if result.center_sample_bound is not None
        else math.nan
    )
    return exact_assignment_certificate(
        F,
        result.coords,
        lambdas,
        sample_bound,
        target_value,
    )


def normalized_lambda(values: Sequence[float]) -> tuple[float, ...] | None:
    norm = math.sqrt(sum(float(x) * float(x) for x in values))
    if norm <= TOL:
        return None
    return tuple(float(x) / norm for x in values)


def lambda_candidates(
    dimension: int,
    random_trials: int,
    rng: random.Random,
    d: Sequence[float] | None = None,
    e: Sequence[float] | None = None,
) -> Iterable[tuple[float, ...]]:
    """Generate deterministic and random signed weights on the unit sphere."""
    seen: set[tuple[int, ...]] = set()

    def emit(values: Sequence[float]) -> tuple[float, ...] | None:
        lambdas = normalized_lambda(values)
        if lambdas is None:
            return None
        key = tuple(int(round(10**8 * x)) for x in lambdas)
        if key in seen:
            return None
        seen.add(key)
        return lambdas

    for j in range(dimension):
        for sign in (-1.0, 1.0):
            values = [0.0] * dimension
            values[j] = sign
            lambdas = emit(values)
            if lambdas is not None:
                yield lambdas

    if dimension <= 3:
        for values in itertools.product((-2.0, -1.0, 0.0, 1.0, 2.0), repeat=dimension):
            lambdas = emit(values)
            if lambdas is not None:
                yield lambdas

    if d is not None and e is not None:
        for i in range(dimension):
            for j in range(dimension):
                if i == j or d[j] <= TOL or e[j] <= TOL:
                    continue
                lower = 0.0
                if e[i] >= 0:
                    lower = e[i] / e[j]
                upper = d[i] / d[j]
                if lower + 1e-6 >= upper:
                    continue
                for mix in (0.1, 0.3, 0.5, 0.7, 0.9):
                    t = lower + mix * (upper - lower)
                    values = [0.0] * dimension
                    values[i] = 1.0
                    values[j] = -t
                    lambdas = emit(values)
                    if lambdas is not None:
                        yield lambdas

        low = [j for j, value in enumerate(e) if value < -TOL]
        high = [j for j, value in enumerate(e) if value >= -TOL]
        for j in low:
            values = [0.0] * dimension
            values[j] = 1.0
            lambdas = emit(values)
            if lambdas is not None:
                yield lambdas
        for i in low:
            for j in high:
                if d[j] <= TOL:
                    continue
                max_t = 0.98 * d[i] / d[j]
                for scale in (0.2, 0.5, 0.9):
                    values = [0.0] * dimension
                    values[i] = 1.0
                    values[j] = -scale * max_t
                    lambdas = emit(values)
                    if lambdas is not None:
                        yield lambdas
        for _ in range(random_trials):
            if not low:
                break
            values = [0.0] * dimension
            for j in low:
                values[j] = rng.random()
            for j in high:
                values[j] = -rng.random()
            diagonal = sum(values[j] * d[j] for j in range(dimension))
            if diagonal <= TOL:
                boost = low[0]
                values[boost] += (TOL - diagonal) / d[boost] + rng.random()
            lambdas = emit(values)
            if lambdas is not None:
                yield lambdas

    for _ in range(random_trials):
        values = [rng.gauss(0.0, 1.0) for _ in range(dimension)]
        lambdas = emit(values)
        if lambdas is not None:
            yield lambdas


def stress_lambdas_for_coords(
    F: Family,
    coords: Sequence[int],
    random_trials: int,
    rng: random.Random,
) -> LambdaStressSummary | None:
    """Search for signed weights that nearly separate the center."""
    coords = tuple(coords)
    if not coords:
        return None
    p_all = frequencies(F, max(coords) + 1)
    d = tuple(0.5 - p_all[coord] for coord in coords)
    e = tuple(2 * p_all[coord] - p_all[coord] * p_all[coord] - 0.5 for coord in coords)
    raw_best: LambdaStressResult | None = None
    cone_best: LambdaStressResult | None = None
    cone_trace_worst: LambdaStressResult | None = None
    for lambdas in lambda_candidates(len(coords), random_trials, rng, d, e):
        target_value = 0.5 * sum(lambdas)
        cert = exact_assignment_certificate(
            F,
            coords,
            lambdas,
            math.nan,
            target_value,
        )
        slack = cert.exact_max - cert.target_value
        diagonal_cone = sum(lambdas[j] * d[j] for j in range(len(coords)))
        random_cone = sum(lambdas[j] * e[j] for j in range(len(coords)))
        trace_positive = trace_preserving_positive_assignment(F, coords, lambdas)
        trace_slack: float | None = None
        trace_q: tuple[float, ...] | None = None
        if trace_positive is not None:
            trace_slack, trace_q = trace_positive
        result = LambdaStressResult(
            slack=slack,
            lambdas=cert.lambdas,
            diagonal_cone=diagonal_cone,
            random_cone=random_cone,
            trace_slack=trace_slack,
            trace_q=trace_q,
            target_value=cert.target_value,
            exact_max=cert.exact_max,
            best_q=cert.best_q,
        )
        if raw_best is None or result.slack < raw_best.slack:
            raw_best = result
        if diagonal_cone > 1e-8 and random_cone < -1e-8:
            if cone_best is None or result.slack < cone_best.slack:
                cone_best = result
            if trace_slack is not None:
                if cone_trace_worst is None or trace_slack < cone_trace_worst.trace_slack:
                    cone_trace_worst = result
    if raw_best is None:
        return None
    return LambdaStressSummary(raw_best, cone_best, cone_trace_worst)


def protected_block_max_frequency(
    F: Family,
    positive_coord: int,
    protected_coords: Sequence[int],
) -> float | None:
    if not protected_coords:
        return None
    blocks: dict[tuple[int, ...], list[Mask]] = {}
    for A in F:
        key = tuple((A >> coord) & 1 for coord in protected_coords)
        blocks.setdefault(key, []).append(A)
    return max(
        sum((A >> positive_coord) & 1 for A in block) / len(block)
        for block in blocks.values()
    )


def trace_preserving_boost_delta(
    F: Family,
    positive_coord: int,
    protected_coords: Sequence[int],
) -> float | None:
    if not protected_coords:
        return None
    blocks: dict[tuple[int, ...], list[Mask]] = {}
    for A in F:
        key = tuple((A >> coord) & 1 for coord in protected_coords)
        blocks.setdefault(key, []).append(A)
    boost = 0
    for block in blocks.values():
        present = sum((A >> positive_coord) & 1 for A in block)
        absent = len(block) - present
        boost += min(present, absent)
    return boost / len(F)


def trace_preserving_positive_assignment(
    F: Family,
    coords: Sequence[int],
    lambdas: Sequence[float],
) -> tuple[float, tuple[float, ...]] | None:
    positive = [j for j, value in enumerate(lambdas) if value > 1e-8]
    negative_coords = tuple(
        coord for j, coord in enumerate(coords) if lambdas[j] < -1e-8
    )
    if not positive:
        return None

    blocks: dict[tuple[int, ...], list[int]] = {}
    for idx, A in enumerate(F):
        key = tuple((A >> coord) & 1 for coord in negative_coords)
        blocks.setdefault(key, []).append(idx)

    global_assignment = [-1] * len(F)
    for block_indices in blocks.values():
        weights: list[list[float]] = []
        for row_index in block_indices:
            row_mask = F[row_index]
            row = []
            for col_index in block_indices:
                col_mask = F[col_index]
                row.append(
                    sum(
                        lambdas[j]
                        for j in positive
                        if ((row_mask >> coords[j]) & 1) == 0
                        and ((col_mask >> coords[j]) & 1) == 1
                    )
                )
            weights.append(row)
        _, local_assignment = max_weight_assignment(weights)
        for local_row, local_col in enumerate(local_assignment):
            global_assignment[block_indices[local_row]] = block_indices[local_col]

    q = assignment_q(F, coords, global_assignment)
    slack = sum(lambdas[j] * (q[j] - 0.5) for j in range(len(coords)))
    return slack, q


def q_key(q: Sequence[float]) -> tuple[int, ...]:
    return tuple(int(round(10**10 * x)) for x in q)


def generate_center_certificate(
    F: Family,
    coords: Sequence[int],
    initial_q_points: Sequence[Sequence[float]],
    max_iterations: int,
) -> CenterGenerationResult:
    """Column-generate exact permutation q-points until center is decided."""
    if not coords:
        return CenterGenerationResult("no-coordinates", None, 0, len(initial_q_points))
    target = np.full(len(coords), 0.5)
    points = [tuple(float(x) for x in q) for q in initial_q_points]
    point_keys = {q_key(q) for q in points}

    for iteration in range(max_iterations + 1):
        point_array = np.array(points, dtype=float)
        if point_in_convex_hull(point_array, target):
            return CenterGenerationResult(
                "generated-feasible",
                True,
                iteration,
                len(points),
            )
        separated = separating_lambda(point_array, target)
        if separated is None:
            return CenterGenerationResult("unknown-no-separator", None, iteration, len(points))
        lambdas, sample_bound, target_value = separated
        cert = exact_assignment_certificate(
            F,
            coords,
            tuple(float(x) for x in lambdas),
            sample_bound,
            target_value,
        )
        if cert.verified_obstruction:
            return CenterGenerationResult(
                "verified-obstruction",
                False,
                iteration,
                len(points),
                cert,
            )
        key = q_key(cert.best_q)
        if key in point_keys:
            return CenterGenerationResult(
                "unknown-stalled",
                None,
                iteration,
                len(points),
                cert,
            )
        points.append(cert.best_q)
        point_keys.add(key)

    return CenterGenerationResult("unknown-iteration-limit", None, max_iterations, len(points))


def eligible_coords_for_mode(
    F: Family,
    n: int,
    coord_mode: str,
    maximal_only: bool,
) -> tuple[int, ...]:
    p_all = frequencies(F, n)
    active = active_coords(F, n)
    if coord_mode == "active":
        coords = active
    elif coord_mode == "light":
        coords = tuple(i for i in active if p_all[i] < 0.5 - TOL)
    elif coord_mode == "critical":
        coords = tuple(i for i in active if 0.25 - TOL <= p_all[i] < 0.5 - TOL)
    elif coord_mode == "nonheavy":
        coords = tuple(i for i in active if p_all[i] <= 0.5 + TOL)
    else:
        raise ValueError(f"unknown coord mode {coord_mode}")
    if maximal_only:
        coords = maximal_trace_coords(F, n, coords)
    return coords


def coordinate_subsets(coords: Sequence[int], max_coords: int) -> Iterable[tuple[int, ...]]:
    if max_coords > 3:
        raise ValueError("the dependency-free exact hull solver supports at most 3 coordinates")
    upper = min(max_coords, len(coords))
    for size in range(1, upper + 1):
        yield from itertools.combinations(coords, size)


def run_family_window_for_coords(
    F: Family,
    n: int,
    coords: Sequence[int],
    max_exact_size: int,
    samples: int,
    center_generate: bool,
    center_iterations: int,
    rng: random.Random,
) -> WindowResult | None:
    p_all = frequencies(F, n)
    if len(coords) > 3:
        raise ValueError("the dependency-free exact hull solver supports at most 3 coordinates")
    coords = tuple(coords)
    if not coords:
        return None
    q_pts, exact = permutation_q_points(F, coords, max_exact_size, samples, rng)
    p_selected = [p_all[i] for i in coords]
    result = max_window_margin(q_pts, p_selected, exact, coords)
    if result is None:
        return None
    if result.center_feasible is True:
        return replace(
            result,
            center_status="exact-feasible" if result.exact else "sampled-feasible",
            center_generation_points=result.point_count,
        )
    if result.center_feasible is False:
        if result.exact:
            return replace(
                result,
                center_status="verified-obstruction",
                center_generation_points=result.point_count,
            )
        if center_generate:
            generated = generate_center_certificate(F, coords, q_pts, center_iterations)
            if generated.feasible is True:
                return replace(
                    result,
                    center_feasible=True,
                    center_status=generated.status,
                    center_iterations=generated.iterations,
                    center_generation_points=generated.point_count,
                    center_separator=None,
                    center_sample_bound=None,
                    center_target_value=None,
                )
            if generated.feasible is False and generated.certificate is not None:
                cert = generated.certificate
                return replace(
                    result,
                    center_status=generated.status,
                    center_iterations=generated.iterations,
                    center_generation_points=generated.point_count,
                    center_separator=cert.lambdas,
                    center_sample_bound=cert.exact_max,
                    center_target_value=cert.target_value,
                )
            return replace(
                result,
                center_status=generated.status,
                center_iterations=generated.iterations,
                center_generation_points=generated.point_count,
            )
        return replace(result, center_status="sampled-miss")
    return result


def run_family_window(
    F: Family,
    n: int,
    coord_mode: str,
    maximal_only: bool,
    max_coords: int,
    max_exact_size: int,
    samples: int,
    center_generate: bool,
    center_iterations: int,
    rng: random.Random,
) -> WindowResult | None:
    p_all = frequencies(F, n)
    coords = eligible_coords_for_mode(F, n, coord_mode, maximal_only)
    if max_coords > 3:
        raise ValueError("the dependency-free exact hull solver supports at most 3 coordinates")
    if len(coords) > max_coords:
        coords = tuple(sorted(coords, key=lambda i: p_all[i], reverse=True)[:max_coords])
    return run_family_window_for_coords(
        F,
        n,
        coords,
        max_exact_size,
        samples,
        center_generate,
        center_iterations,
        rng,
    )


def run_family_subset_windows(
    F: Family,
    n: int,
    coord_mode: str,
    maximal_only: bool,
    max_coords: int,
    max_exact_size: int,
    samples: int,
    center_generate: bool,
    center_iterations: int,
    rng: random.Random,
) -> list[WindowResult]:
    coords = eligible_coords_for_mode(F, n, coord_mode, maximal_only)
    results: list[WindowResult] = []
    for subset in coordinate_subsets(coords, max_coords):
        result = run_family_window_for_coords(
            F,
            n,
            subset,
            max_exact_size,
            samples,
            center_generate,
            center_iterations,
            rng,
        )
        if result is not None:
            results.append(result)
    return results



def summarize_exhaustive(args: argparse.Namespace) -> None:
    rng = random.Random(args.seed + 1)
    families = list(all_union_closed_families(args.n))
    nontrivial = [F for F in families if active_coords(F, args.n)]
    if args.reduced_only:
        nontrivial = [F for F in nontrivial if is_coordinate_reduced(F, args.n)]
    violations = [F for F in nontrivial if not frankl_witnesses(F, args.n)]

    print(f"exhaustive n={args.n}")
    print(f"union-closed families: {len(families)}")
    print(f"nontrivial families:   {len(nontrivial)}")
    print(f"reduced only:          {args.reduced_only}")
    print(f"Frankl violations:     {len(violations)}")

    results: list[tuple[WindowResult, Family]] = []
    skipped = 0
    for F in nontrivial:
        if args.scan_subsets:
            family_results = run_family_subset_windows(
                F,
                args.n,
                args.coord_mode,
                args.maximal_only,
                args.max_coords,
                args.max_exact_size,
                args.samples,
                args.center_generate,
                args.center_iterations,
                rng,
            )
            if family_results:
                results.extend((result, F) for result in family_results)
            else:
                skipped += 1
        else:
            result = run_family_window(
                F,
                args.n,
                args.coord_mode,
                args.maximal_only,
                args.max_coords,
                args.max_exact_size,
                args.samples,
                args.center_generate,
                args.center_iterations,
                rng,
            )
            if result is None:
                skipped += 1
            else:
                results.append((result, F))

    exact_count = sum(1 for r, _ in results if r.exact)
    print(f"window mode:          {args.coord_mode}")
    print(f"subset scan:          {args.scan_subsets}")
    print(f"maximal only:         {args.maximal_only}")
    print(f"window results:       {len(results)} ({exact_count} exact), skipped {skipped}")
    print_center_summary(results)
    print_lambda_stress_summary(results, args.n, args.lambda_stress, args.seed + 2, args.show)
    if not results:
        return

    results.sort(key=lambda item: item[0].margin)
    print("\nsmallest margins:")
    for result, F in results[: args.show]:
        print_case(result, F, args.n)

    print("\nlargest margins:")
    for result, F in reversed(results[-args.show :]):
        print_case(result, F, args.n)
    print_center_misses(results, args.n, args.show_misses)


def summarize_random(args: argparse.Namespace) -> None:
    family_rng = random.Random(args.seed)
    coupling_seed = args.seed + 1
    seen: set[Family] = set()
    results: list[tuple[WindowResult, Family]] = []
    for trial in range(args.random):
        F = random_union_closed_family(args.n, args.generators, family_rng)
        if F in seen or not active_coords(F, args.n):
            continue
        if args.reduced_only and not is_coordinate_reduced(F, args.n):
            continue
        seen.add(F)
        coupling_rng = random.Random(coupling_seed + trial)
        if args.scan_subsets:
            family_results = run_family_subset_windows(
                F,
                args.n,
                args.coord_mode,
                args.maximal_only,
                args.max_coords,
                args.max_exact_size,
                args.samples,
                args.center_generate,
                args.center_iterations,
                coupling_rng,
            )
            results.extend((result, F) for result in family_results)
        else:
            result = run_family_window(
                F,
                args.n,
                args.coord_mode,
                args.maximal_only,
                args.max_coords,
                args.max_exact_size,
                args.samples,
                args.center_generate,
                args.center_iterations,
                coupling_rng,
            )
            if result is not None:
                results.append((result, F))

    print(f"random n={args.n}, generated={args.random}, unique_nontrivial={len(seen)}")
    print(f"window mode: {args.coord_mode}")
    print(f"subset scan: {args.scan_subsets}")
    print(f"reduced only: {args.reduced_only}")
    print(f"maximal only: {args.maximal_only}")
    print(f"window results: {len(results)}")
    print_center_summary(results)
    print_lambda_stress_summary(results, args.n, args.lambda_stress, args.seed + 2, args.show)
    if not results:
        return
    results.sort(key=lambda item: item[0].margin)
    print("\nsmallest sampled margins:")
    for result, F in results[: args.show]:
        print_case(result, F, args.n)
    print("\nlargest sampled margins:")
    for result, F in reversed(results[-args.show :]):
        print_case(result, F, args.n)
    print_center_misses(results, args.n, args.show_misses)


def print_case(result: WindowResult, F: Family, n: int, show_family: bool = False) -> None:
    p = frequencies(F, n)
    selected_p = tuple(p[i] for i in result.coords)
    witness = frankl_witnesses(F, n)
    exactness = "exact" if result.exact else "sampled"
    print(
        f"  margin={result.margin:+.6f} {exactness}, "
        f"|F|={len(F)}, coords={result.coords}, "
        f"p={tuple(round(x, 4) for x in selected_p)}, "
        f"window_q={tuple(round(x, 4) for x in result.q)}, "
        f"points={result.point_count}, dim={result.affine_dim}, "
        f"Frankl={witness}"
    )
    if result.center_feasible is not None:
        print(f"    critical center q=(1/2,...,1/2): {result.center_feasible}")
    if result.center_status is not None:
        extra = ""
        if result.center_iterations is not None:
            extra += f", iterations={result.center_iterations}"
        if result.center_generation_points is not None:
            extra += f", generated_points={result.center_generation_points}"
        print(f"    center status: {result.center_status}{extra}")
    if result.center_separator is not None:
        cert = certify_center_separator(F, result)
        if cert is not None:
            status = (
                "VERIFIED obstruction"
                if cert.verified_obstruction
                else "sampling weakness"
            )
            print(
                "    separator "
                f"lambda={tuple(round(x, 4) for x in cert.lambdas)}, "
                f"sample<= {cert.sample_bound:.6f}, "
                f"target={cert.target_value:.6f}, "
                f"exact max={cert.exact_max:.6f} ({status})"
            )
            print(f"    exact maximizing q={tuple(round(x, 4) for x in cert.best_q)}")
    if len(result.coords) == 1:
        lo, hi = single_coordinate_q_range(F, result.coords[0])
        center = "centerable" if lo <= 0.5 + TOL and 0.5 <= hi + TOL else "not-centerable"
        print(f"    single-coordinate q-range=[{lo:.4f}, {hi:.4f}] ({center})")
    if show_family or (n <= 4 and len(F) <= 12):
        print(f"    F={family_str(F, n)}")


def print_center_summary(results: Sequence[tuple[WindowResult, Family]]) -> None:
    center_results = [r for r, _ in results if r.center_feasible is not None]
    if center_results:
        center = [r.center_feasible for r in center_results]
        exact = [r.center_feasible for r in center_results if r.exact]
        sampled = [r.center_feasible for r in center_results if not r.exact]
        print(
            "critical center checks: "
            f"{sum(center)} feasible, {len(center) - sum(center)} not seen feasible"
        )
        if exact:
            print(
                "  exact:   "
                f"{sum(exact)} feasible, {len(exact) - sum(exact)} infeasible"
            )
        if sampled:
            print(
                "  sampled: "
                f"{sum(sampled)} feasible, {len(sampled) - sum(sampled)} not seen feasible"
            )
        statuses: dict[str, int] = {}
        for r in center_results:
            if r.center_status is not None:
                statuses[r.center_status] = statuses.get(r.center_status, 0) + 1
        if statuses:
            status_text = ", ".join(f"{k}={v}" for k, v in sorted(statuses.items()))
            print(f"  statuses: {status_text}")


def print_center_misses(
    results: Sequence[tuple[WindowResult, Family]],
    n: int,
    limit: int,
) -> None:
    if limit <= 0:
        return
    misses = [(r, F) for r, F in results if r.center_feasible is False]
    if not misses:
        return
    print(f"\nfirst {min(limit, len(misses))} critical center misses:")
    for result, F in misses[:limit]:
        print_case(result, F, n, show_family=True)


def print_lambda_stress_summary(
    results: Sequence[tuple[WindowResult, Family]],
    n: int,
    random_trials: int,
    seed: int,
    limit: int,
) -> None:
    if random_trials <= 0 or not results:
        return
    rng = random.Random(seed)
    stressed: list[tuple[LambdaStressSummary, WindowResult, Family]] = []
    for result, F in results:
        stress = stress_lambdas_for_coords(F, result.coords, random_trials, rng)
        if stress is not None:
            stressed.append((stress, result, F))
    if not stressed:
        return
    stressed.sort(key=lambda item: item[0].raw_best.slack)
    obstructions = sum(1 for stress, _, _ in stressed if stress.raw_best.slack < -1e-8)
    cone_stressed = [
        (stress.cone_best, result, F)
        for stress, result, F in stressed
        if stress.cone_best is not None
    ]
    cone_trace = [
        (stress.cone_trace_worst, result, F)
        for stress, result, F in stressed
        if stress.cone_trace_worst is not None
    ]
    print(
        "lambda stress: "
        f"{len(stressed)} coordinate sets, {random_trials} random directions each, "
        f"min slack={stressed[0][0].raw_best.slack:+.6f}, obstructions={obstructions}"
    )
    if cone_stressed:
        cone_stressed.sort(key=lambda item: item[0].slack)
        print(
            "  remaining-cone candidates: "
            f"{len(cone_stressed)}, min cone slack={cone_stressed[0][0].slack:+.6f}"
        )
    else:
        print("  remaining-cone candidates: 0")
    if cone_trace:
        cone_trace.sort(key=lambda item: item[0].trace_slack)
        trace_failures = sum(
            1
            for stress, _, _ in cone_trace
            if stress.trace_slack is not None and stress.trace_slack < -1e-8
        )
        print(
            "  trace-preserving cone checks: "
            f"{len(cone_trace)}, min trace slack={cone_trace[0][0].trace_slack:+.6f}, "
            f"failures={trace_failures}"
        )
    print("\nhardest raw lambda directions:")
    for stress, result, F in stressed[:limit]:
        print_lambda_stress_case(stress.raw_best, result, F, n)
    if cone_stressed:
        print("\nhardest remaining-cone directions:")
        for stress, result, F in cone_stressed[:limit]:
            print_lambda_stress_case(stress, result, F, n)
    if cone_trace:
        print("\nhardest trace-preserving cone directions:")
        for stress, result, F in cone_trace[:limit]:
            print_lambda_stress_case(stress, result, F, n)


def print_lambda_stress_case(
    stress: LambdaStressResult,
    result: WindowResult,
    F: Family,
    n: int,
) -> None:
    p = frequencies(F, n)
    selected_p = tuple(p[i] for i in result.coords)
    protected_text = ""
    trace_positive = trace_preserving_positive_assignment(
        F,
        result.coords,
        stress.lambdas,
    )
    if trace_positive is not None:
        trace_slack, trace_q = trace_positive
        protected_text += (
            f", trace_slack={trace_slack:+.6f}, "
            f"trace_q={tuple(round(x, 4) for x in trace_q)}"
        )
    positive_indices = [j for j, value in enumerate(stress.lambdas) if value > 1e-8]
    if len(positive_indices) == 1 and all(
        value <= 1e-8
        for j, value in enumerate(stress.lambdas)
        if j not in positive_indices
    ):
        positive_coord = result.coords[positive_indices[0]]
        protected = tuple(
            coord
            for j, coord in enumerate(result.coords)
            if j not in positive_indices and stress.lambdas[j] < -1e-8
        )
        max_cond = protected_block_max_frequency(F, positive_coord, protected)
        boost_delta = trace_preserving_boost_delta(F, positive_coord, protected)
        if max_cond is not None:
            protected_text = f", protected_max={max_cond:.6f}"
        if boost_delta is not None:
            positive_weight = stress.lambdas[positive_indices[0]]
            selected_p = tuple(p[i] for i in result.coords)
            required_delta = 0.5 - selected_p[positive_indices[0]]
            for j, value in enumerate(stress.lambdas):
                if j != positive_indices[0]:
                    required_delta += value * (0.5 - selected_p[j]) / positive_weight
            protected_text += (
                f", protected_delta={boost_delta:.6f}, "
                f"required_delta={required_delta:.6f}"
            )
    print(
        f"  slack={stress.slack:+.6f}, |F|={len(F)}, coords={result.coords}, "
        f"p={tuple(round(x, 4) for x in selected_p)}, "
        f"lambda={tuple(round(x, 4) for x in stress.lambdas)}, "
        f"best_q={tuple(round(x, 4) for x in stress.best_q)}, "
        f"diag_cone={stress.diagonal_cone:+.6f}, "
        f"random_cone={stress.random_cone:+.6f}, "
        f"target={stress.target_value:+.6f}, exact={stress.exact_max:+.6f}"
        f"{protected_text}"
    )


def summarize_two_trace_counts(max_size: int) -> None:
    checked, misses, max_points = summarize_trace_counts(
        coord_count=2,
        max_size=max_size,
        union_support_only=False,
        stop_at_first_miss=True,
    )
    print(
        "two-coordinate trace count check: "
        f"max_size={max_size}, checked={checked}, misses={misses}, "
        f"max_points={max_points}"
    )


def summarize_trace_counts(
    coord_count: int,
    max_size: int,
    union_support_only: bool,
    stop_at_first_miss: bool,
) -> tuple[int, int, int]:
    checked = 0
    misses = 0
    max_points = 0
    target = np.array([0.5] * coord_count)
    for m in range(1, max_size + 1):
        for counts in count_vectors(m, 1 << coord_count):
            if union_support_only and not support_union_closed(counts):
                continue
            ps = tuple(
                sum(counts[u] for u in range(1 << coord_count) if (u >> bit) & 1)
                / m
                for bit in range(coord_count)
            )
            if not all(0.25 - TOL <= p < 0.5 - TOL for p in ps):
                continue
            checked += 1
            points = trace_transport_q_points(counts, coord_count)
            max_points = max(max_points, len(points))
            if not point_in_convex_hull(np.array(points, dtype=float), target):
                misses += 1
                print(
                    "trace-count miss: "
                    f"k={coord_count}, m={m}, counts={counts}, "
                    f"p={tuple(round(p, 4) for p in ps)}, "
                    f"union_support={support_union_closed(counts)}"
                )
                if stop_at_first_miss:
                    return checked, misses, max_points
    return checked, misses, max_points


def summarize_three_trace_obstruction() -> None:
    counts = (4, 0, 0, 2, 2, 0, 2, 1)
    points = trace_transport_q_points(counts, 3)
    center = np.array([0.5, 0.5, 0.5])
    feasible = point_in_convex_hull(np.array(points, dtype=float), center)
    ps = tuple(
        sum(counts[u] for u in range(8) if (u >> bit) & 1) / sum(counts)
        for bit in range(3)
    )
    lambda_value = max(q[0] - q[1] - q[2] for q in points)
    lifted_family = (0, 1, 7, 8, 9, 15, 24, 25, 28, 29, 31)
    lifted_coords = (1, 2, 4)
    print("three-coordinate trace obstruction:")
    print(f"  counts={counts}, p={tuple(round(p, 6) for p in ps)}")
    print(f"  support_union_closed={support_union_closed(counts)}")
    print(f"  points={len(points)}, center_feasible={feasible}")
    print(
        "  separator lambda=(1,-1,-1): "
        f"max={lambda_value:.6f}, target={-0.5:.6f}"
    )
    print(
        "  lifted family: "
        f"n=5, |F|={len(lifted_family)}, tracked_coords={lifted_coords}, "
        f"trace_counts={trace_counts(lifted_family, lifted_coords)}, "
        f"frequencies={tuple(round(p, 6) for p in frequencies(lifted_family, 5))}"
    )


def trace_support_assignment_value(counts: Sequence[int], lambdas: Sequence[int]) -> float:
    traces = []
    for trace, count in enumerate(counts):
        traces.extend([trace] * count)
    weights = [
        [
            sum(
                lambdas[bit]
                for bit in range(len(lambdas))
                if ((row_trace | col_trace) >> bit) & 1
            )
            for col_trace in traces
        ]
        for row_trace in traces
    ]
    value, _ = max_weight_assignment(weights)
    return value / len(traces)


def first_sign_separator(counts: Sequence[int], coord_count: int) -> tuple[tuple[int, ...], float, float] | None:
    lambdas = [
        lambdas
        for lambdas in itertools.product((-1, 0, 1), repeat=coord_count)
        if any(lambdas)
    ]
    for lambdas in lambdas:
        target = 0.5 * sum(lambdas)
        value = trace_support_assignment_value(counts, lambdas)
        if value < target - 1e-9:
            return tuple(lambdas), value, target
    return None


def local_zero_fiber_bound(size: int) -> int | None:
    """Certified lower bounds for a zero fiber of the given size.

    These are small local union-closed facts used only by the obstruction
    experiments: 4 -> 2, 5 -> 3, 6 -> 4, 7 -> 4.  The 6-set bound is stronger
    than the ordinary half bound and is verified by the finite incidence
    search below.
    """
    bounds = {0: 0, 1: 1, 2: 1, 3: 2, 4: 2, 5: 3, 6: 4, 7: 4}
    return bounds.get(size)


def propagation_lower_bound(counts: Sequence[int]) -> tuple[int | None, tuple[int, ...] | None]:
    """Minimize a sound lower bound for hidden-element propagation.

    `y[u]` is the number of members in trace fiber `u` containing a fixed
    auxiliary element `h`.  We use three sound constraints:

    * a certified local lower bound in the zero fiber;
    * bottom-fiber propagation gives `y[u] >= 1` for every nonzero fiber;
    * if all of fiber `u | v` contains `h`, then fibers `u` and `v` cannot
      both contain an `h`-free member.
    """
    zero_bound = local_zero_fiber_bound(counts[0])
    if zero_bound is None:
        return None, None
    support = [u for u, count in enumerate(counts) if count > 0]
    best = math.inf
    best_y: tuple[int, ...] | None = None

    def go(trace: int, y: list[int]) -> None:
        nonlocal best, best_y
        if trace == len(counts):
            total = sum(y)
            if total >= best:
                return
            for u in support:
                for v in support:
                    w = u | v
                    if counts[w] == 0:
                        return
                    if y[w] == counts[w] and y[u] < counts[u] and y[v] < counts[v]:
                        return
            best = total
            best_y = tuple(y)
            return

        count = counts[trace]
        if count == 0:
            go(trace + 1, y + [0])
            return
        lower = 0
        if trace == 0:
            lower = zero_bound
        else:
            lower = 1
        for value in range(lower, count + 1):
            if sum(y) + value >= best:
                break
            go(trace + 1, y + [value])

    go(0, [])
    if best_y is None:
        return None, None
    return int(best), best_y


def abstract_local_frankl_check(size: int, threshold: int) -> bool:
    """Check there is no `size`-set union-closed family with max frequency below threshold.

    If such a counterexample existed, after naming a maximum row every active
    coordinate would have an incidence column containing the maximum row and
    at most `threshold - 2` other rows.  This makes the check finite.
    """
    top = size - 1
    columns = []
    for extra_size in range(threshold - 1):
        for extra in itertools.combinations(range(top), extra_size):
            column_support = set(extra) | {top}
            columns.append(tuple(1 if row in column_support else 0 for row in range(size)))
    for mask in range(1, 1 << len(columns)):
        chosen = [columns[i] for i in range(len(columns)) if (mask >> i) & 1]
        rows = [tuple(column[row] for column in chosen) for row in range(size)]
        if len(set(rows)) < size:
            continue
        row_set = set(rows)
        if all(
            tuple(max(a[j], b[j]) for j in range(len(chosen))) in row_set
            for a in rows
            for b in rows
        ):
            return False
    return True


def summarize_local_frankl_checks() -> None:
    checks = [(4, 2), (5, 3), (6, 4), (7, 4)]
    for size, threshold in checks:
        print(
            "local Frankl incidence check: "
            f"size={size}, threshold={threshold}, "
            f"verified={abstract_local_frankl_check(size, threshold)}"
        )


def summarize_three_sign_obstructions(max_size: int) -> None:
    for m in range(1, max_size + 1):
        critical = 0
        classes: dict[tuple[int, ...], int] = {}
        examples: dict[tuple[int, ...], tuple[tuple[int, ...], tuple[int, ...], float, float]] = {}
        for counts in count_vectors(m, 8):
            if not support_union_closed(counts):
                continue
            ps = tuple(
                sum(counts[u] for u in range(8) if (u >> bit) & 1) / m
                for bit in range(3)
            )
            if not all(0.25 - TOL <= p < 0.5 - TOL for p in ps):
                continue
            critical += 1
            separator = first_sign_separator(counts, 3)
            if separator is None:
                continue
            key = canonical_trace_counts(counts, 3)
            classes[key] = classes.get(key, 0) + 1
            examples.setdefault(key, (counts, *separator))
        print(
            "three-coordinate sign scan: "
            f"m={m}, critical={critical}, classes={len(classes)}, "
            f"separated={sum(classes.values())}"
        )
        for key in sorted(classes):
            counts, lambdas, value, target = examples[key]
            print(
                "  class: "
                f"multiplicity={classes[key]}, canonical={key}, "
                f"example={counts}, lambda={lambdas}, "
                f"gap={value - target:+.6f}"
            )


def summarize_three_propagation_obstructions(max_size: int) -> None:
    for m in range(1, max_size + 1):
        critical = 0
        separated = 0
        paid = 0
        unpaid: list[tuple[tuple[int, ...], tuple[int, ...] | None, int | None]] = []
        seen_unpaid: set[tuple[int, ...]] = set()
        for counts in count_vectors(m, 8):
            if not support_union_closed(counts):
                continue
            ps = tuple(
                sum(counts[u] for u in range(8) if (u >> bit) & 1) / m
                for bit in range(3)
            )
            if not all(0.25 - TOL <= p < 0.5 - TOL for p in ps):
                continue
            critical += 1
            if first_sign_separator(counts, 3) is None:
                continue
            separated += 1
            lower, witness_counts = propagation_lower_bound(counts)
            if lower is not None and 2 * lower >= m:
                paid += 1
                continue
            key = canonical_trace_counts(counts, 3)
            if key not in seen_unpaid:
                seen_unpaid.add(key)
                unpaid.append((key, witness_counts, lower))
        print(
            "three-coordinate propagation scan: "
            f"m={m}, critical={critical}, separated={separated}, "
            f"paid={paid}, unpaid_classes={len(unpaid)}"
        )
        for key, witness_counts, lower in unpaid:
            print(f"  unpaid: canonical={key}, lower={lower}, y={witness_counts}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=3, help="ground-set size")
    parser.add_argument(
        "--mode",
        choices=["exhaustive", "random"],
        default="exhaustive",
        help="enumerate all families or sample generated ones",
    )
    parser.add_argument(
        "--coord-mode",
        choices=["active", "light", "critical", "nonheavy"],
        default="nonheavy",
        help=(
            "coordinates used in the window LP: all active, only p<1/2, "
            "only 1/4<=p<1/2, or p<=1/2"
        ),
    )
    parser.add_argument(
        "--max-exact-size",
        type=int,
        default=8,
        help="enumerate all permutation couplings only up to this |F|",
    )
    parser.add_argument(
        "--max-coords",
        type=int,
        default=3,
        help="when more coordinates are eligible, keep the ones with largest p_i",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=5000,
        help="random permutation samples for larger families",
    )
    parser.add_argument("--random", type=int, default=200, help="random trials")
    parser.add_argument("--generators", type=int, default=6, help="random generators")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--show", type=int, default=5)
    parser.add_argument(
        "--show-misses",
        type=int,
        default=0,
        help="print this many critical-center misses, including the family",
    )
    parser.add_argument(
        "--scan-subsets",
        action="store_true",
        help="scan every eligible coordinate subset up to --max-coords",
    )
    parser.add_argument(
        "--reduced-only",
        action="store_true",
        help="skip families with duplicate active coordinate traces",
    )
    parser.add_argument(
        "--maximal-only",
        action="store_true",
        help="after selecting coordinates, keep only maximal traces under implication",
    )
    parser.add_argument(
        "--center-generate",
        action="store_true",
        help="use assignment-based column generation to resolve sampled center misses",
    )
    parser.add_argument(
        "--center-iterations",
        type=int,
        default=25,
        help="maximum assignment columns to add for each center-generation attempt",
    )
    parser.add_argument(
        "--lambda-stress",
        type=int,
        default=0,
        help="random signed assignment-dual directions to test for each result",
    )
    parser.add_argument(
        "--trace-two-max-size",
        type=int,
        default=0,
        help="exhaustively check two-coordinate trace counts up to this total size and exit",
    )
    parser.add_argument(
        "--trace-three-max-size",
        type=int,
        default=0,
        help="exhaustively check three-coordinate trace counts up to this total size and exit",
    )
    parser.add_argument(
        "--trace-union-support-only",
        action="store_true",
        help="for trace-count checks, require the positive trace support to be union-closed",
    )
    parser.add_argument(
        "--trace-three-obstruction",
        action="store_true",
        help="print the first known three-coordinate trace-count obstruction and exit",
    )
    parser.add_argument(
        "--trace-three-sign-scan-size",
        type=int,
        default=0,
        help="scan critical three-coordinate trace counts for {-1,0,1} separators",
    )
    parser.add_argument(
        "--trace-three-propagation-scan-size",
        type=int,
        default=0,
        help="scan sign obstructions and test the hidden-element propagation certificate",
    )
    parser.add_argument(
        "--local-frankl-checks",
        action="store_true",
        help="run finite incidence checks for the small local Frankl bounds",
    )
    args = parser.parse_args()

    if args.trace_three_obstruction:
        summarize_three_trace_obstruction()
        return
    if args.trace_three_sign_scan_size > 0:
        summarize_three_sign_obstructions(args.trace_three_sign_scan_size)
        return
    if args.trace_three_propagation_scan_size > 0:
        summarize_three_propagation_obstructions(args.trace_three_propagation_scan_size)
        return
    if args.local_frankl_checks:
        summarize_local_frankl_checks()
        return
    if args.trace_two_max_size > 0:
        summarize_two_trace_counts(args.trace_two_max_size)
        return
    if args.trace_three_max_size > 0:
        checked, misses, max_points = summarize_trace_counts(
            coord_count=3,
            max_size=args.trace_three_max_size,
            union_support_only=args.trace_union_support_only,
            stop_at_first_miss=True,
        )
        print(
            "three-coordinate trace count check: "
            f"max_size={args.trace_three_max_size}, checked={checked}, "
            f"misses={misses}, max_points={max_points}, "
            f"union_support_only={args.trace_union_support_only}"
        )
        return

    if args.mode == "exhaustive":
        if args.n > 4:
            raise SystemExit("exhaustive mode is intended for n <= 4")
        summarize_exhaustive(args)
    else:
        summarize_random(args)


if __name__ == "__main__":
    main()
