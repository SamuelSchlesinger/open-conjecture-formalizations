#!/usr/bin/env python3
"""Audit the Gilmer / Alweiss-Huang-Sellke entropy hinge.

This script reproduces the narrow numerical part of Alweiss-Huang-Sellke:

    phi * H(x^2) >= x * H(x),  x in [phi, 1],

where phi = (sqrt(5)-1)/2 and H is binary entropy with natural logarithms.
Their paper reduces the tight Gilmer lemma to this one-variable inequality
plus structural reductions over probability measures.  The checks here are
not a Lean proof; they are a local, high-precision audit scaffold for the
finite computations that should eventually be converted to interval/Lean
certificates.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from dataclasses import dataclass

import mpmath as mp


mp.mp.dps = 80
mp.iv.dps = 80

PHI = (mp.sqrt(5) - 1) / 2
FRANKL_CONSTANT = 1 - PHI

CERTIFICATE_DIGITS = 60
RATIONAL_FLOOR_DENOMINATOR = 10**50


@dataclass(frozen=True)
class AHSVerification:
    i1_min_L: mp.mpf
    i1_argmin: mp.mpf
    i1_required_floor: mp.mpf
    i2_point_count: int
    i2_min_gap: mp.mpf
    i2_gap_arg: tuple[mp.mpf, mp.mpf]
    i2_start: mp.mpf
    i3_margin: mp.mpf


def H(x: mp.mpf) -> mp.mpf:
    """Binary entropy with natural logarithms, continuously extended to 0, 1."""
    x = mp.mpf(x)
    if x <= 0 or x >= 1:
        return mp.mpf("0")
    return -x * mp.log(x) - (1 - x) * mp.log(1 - x)


def H_iv(x: mp.iv.mpf) -> mp.iv.mpf:
    return -x * mp.iv.log(x) - (1 - x) * mp.iv.log(1 - x)


def G(x: mp.mpf) -> mp.mpf:
    return PHI * H(x * x) - x * H(x)


def L(x: mp.mpf) -> mp.mpf:
    """The numerator (1-x^2) G''(x) from the AHS appendix."""
    x = mp.mpf(x)
    return (
        2 * PHI * (1 - x * x) * mp.log(1 / (x * x) - 1)
        - 4 * PHI
        - 2 * x * x * mp.log(x)
        + 2 * (x * x - 1) * mp.log(1 - x)
        + x
        + 2 * mp.log(x)
        + 1
    )


def L_iv(x: mp.iv.mpf) -> mp.iv.mpf:
    """Interval version of `L`, using mpmath interval arithmetic."""
    phi = (mp.iv.sqrt(5) - 1) / 2
    return (
        2 * phi * (1 - x * x) * mp.iv.log(1 / (x * x) - 1)
        - 4 * phi
        - 2 * x * x * mp.iv.log(x)
        + 2 * (x * x - 1) * mp.iv.log(1 - x)
        + x
        + 2 * mp.iv.log(x)
        + 1
    )


def g1(x: mp.mpf) -> mp.mpf:
    return PHI * H(x * x)


def g2(x: mp.mpf) -> mp.mpf:
    return x * H(x)


def g1_iv(x: mp.iv.mpf) -> mp.iv.mpf:
    phi = (mp.iv.sqrt(5) - 1) / 2
    return phi * H_iv(x * x)


def g2_iv(x: mp.iv.mpf) -> mp.iv.mpf:
    return x * H_iv(x)


def rational_grid(start_num: int, end_num: int, denominator: int) -> list[mp.mpf]:
    return [mp.mpf(k) / denominator for k in range(start_num, end_num + 1)]


def mp_decimal(x: mp.mpf, digits: int = CERTIFICATE_DIGITS) -> str:
    return mp.nstr(x, digits)


def interval_record(x: mp.iv.mpf) -> dict[str, str]:
    return {
        "lower": mp_decimal(mp.mpf(x.a)),
        "upper": mp_decimal(mp.mpf(x.b)),
    }


def rational_floor_record(
    x: mp.mpf,
    denominator: int = RATIONAL_FLOOR_DENOMINATOR,
) -> dict[str, int | str]:
    numerator = int(mp.floor(x * denominator))
    return {
        "num": numerator,
        "den": denominator,
        "decimal": mp_decimal(mp.mpf(numerator) / denominator),
    }


def rational_record(num: int, den: int) -> dict[str, int | str]:
    return {"num": num, "den": den, "decimal": mp_decimal(mp.mpf(num) / den)}


def decimal_to_rational_record(x: mp.mpf, denominator: int) -> dict[str, int | str]:
    num = int(mp.nint(x * denominator))
    if abs(x - mp.mpf(num) / denominator) > mp.mpf("1e-40"):
        raise ValueError(f"{x} is not on the expected 1/{denominator} grid")
    return rational_record(num, denominator)


def ahs_i1_check() -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Reproduce the I1 finite L-table.

    AHS prove L is 15.5-Lipschitz on I1 and use a 1/400-dense grid, so it
    suffices that the grid values are at least 15.5/400 = 0.03875.  Their
    printed table has all values above 0.09.
    """
    points = rational_grid(120, 154, 200)  # 0.600, 0.605, ..., 0.770
    values = [(L(x), x) for x in points]
    min_value, argmin = min(values)
    required_floor = mp.mpf("15.5") / 400
    return min_value, argmin, required_floor


def ahs_i2_points(
    start: mp.mpf = mp.mpf("0.76"),
    end: mp.mpf = mp.mpf("0.98"),
    step: mp.mpf = mp.mpf("0.0001"),
    margin: mp.mpf = mp.mpf("0.002"),
) -> list[mp.mpf]:
    """Generate the finite chain used on I2, matching AHS numerics.py."""
    points = [end]
    while points[-1] > start:
        previous = points[-1]
        g1_previous = g1(previous)
        current = previous
        while g2(current) < g1_previous - margin:
            current -= step
        points.append(current + step)
    return list(reversed(points))


def ahs_i2_check() -> tuple[int, mp.mpf, tuple[mp.mpf, mp.mpf], mp.mpf]:
    """Check the monotone-chain gaps g1(x_{i+1}) - g2(x_i)."""
    points = ahs_i2_points()
    gaps = [
        (g1(points[i + 1]) - g2(points[i]), points[i], points[i + 1])
        for i in range(len(points) - 1)
    ]
    min_gap, left, right = min(gaps)
    return len(points), min_gap, (left, right), points[0]


def ahs_i3_check() -> mp.mpf:
    """Numerical margin in the final analytic inequality for I3."""
    return (mp.sqrt(5) - 2) * mp.log(50) - (mp.sqrt(5) - 1) * mp.log(2)


def verify_ahs() -> AHSVerification:
    i1_min_L, i1_argmin, i1_required_floor = ahs_i1_check()
    i2_count, i2_min_gap, i2_gap_arg, i2_start = ahs_i2_check()
    i3_margin = ahs_i3_check()
    return AHSVerification(
        i1_min_L=i1_min_L,
        i1_argmin=i1_argmin,
        i1_required_floor=i1_required_floor,
        i2_point_count=i2_count,
        i2_min_gap=i2_min_gap,
        i2_gap_arg=i2_gap_arg,
        i2_start=i2_start,
        i3_margin=i3_margin,
    )


def ahs_certificate_payload() -> dict[str, object]:
    """Return a compact, deterministic certificate payload for the AHS audit.

    This is still not a Lean proof.  It records finite rational grids,
    high-precision values, mpmath interval enclosures, and conservative
    rational floors that the future Lean checker should consume.
    """
    i1_rows = []
    for num in range(120, 155):
        x = mp.mpf(num) / 200
        x_iv = mp.iv.mpf([x, x])
        L_interval = L_iv(x_iv)
        L_lower = mp.mpf(L_interval.a)
        i1_rows.append(
            {
                "x": rational_record(num, 200),
                "L_value": mp_decimal(L(x)),
                "L_interval": interval_record(L_interval),
                "L_rational_floor": rational_floor_record(L_lower),
            }
        )

    i2_points = ahs_i2_points()
    i2_rows = []
    for left, right in zip(i2_points, i2_points[1:]):
        left_iv = mp.iv.mpf([left, left])
        right_iv = mp.iv.mpf([right, right])
        gap_interval = g1_iv(right_iv) - g2_iv(left_iv)
        gap_lower = mp.mpf(gap_interval.a)
        i2_rows.append(
            {
                "left": decimal_to_rational_record(left, 10000),
                "right": decimal_to_rational_record(right, 10000),
                "gap": mp_decimal(g1(right) - g2(left)),
                "gap_interval": interval_record(gap_interval),
                "gap_rational_floor": rational_floor_record(gap_lower),
            }
        )

    result = verify_ahs()
    return {
        "name": "AHS one-variable entropy hinge audit certificate",
        "status": "mpmath_interval_audit_not_lean_proof",
        "phi": {
            "formula": "(sqrt(5)-1)/2",
            "decimal": mp_decimal(PHI),
        },
        "frankl_constant": {
            "formula": "1-phi",
            "decimal": mp_decimal(FRANKL_CONSTANT),
        },
        "i1": {
            "interval": "[phi, 0.77]",
            "grid": "x = k/200 for 120 <= k <= 154",
            "lipschitz_constant": "15.5",
            "mesh_radius": "1/400",
            "required_floor": mp_decimal(result.i1_required_floor),
            "min_L": mp_decimal(result.i1_min_L),
            "argmin": decimal_to_rational_record(result.i1_argmin, 200),
            "rows": i1_rows,
        },
        "i2": {
            "interval": "[0.76, 0.98]",
            "step": "1/10000",
            "margin": "0.002",
            "point_count": result.i2_point_count,
            "start": decimal_to_rational_record(result.i2_start, 10000),
            "min_gap": mp_decimal(result.i2_min_gap),
            "min_gap_left": decimal_to_rational_record(result.i2_gap_arg[0], 10000),
            "min_gap_right": decimal_to_rational_record(result.i2_gap_arg[1], 10000),
            "rows": i2_rows,
        },
        "i3": {
            "interval": "[0.98, 1]",
            "analytic_margin": mp_decimal(result.i3_margin),
            "analytic_margin_rational_floor": rational_floor_record(result.i3_margin),
        },
    }


def emit_ahs_certificate(path: Path) -> None:
    payload = ahs_certificate_payload()
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def rational_value(record: dict[str, object]) -> mp.mpf:
    return mp.mpf(int(record["num"])) / int(record["den"])


def check_ahs_certificate(path: Path) -> bool:
    payload = json.loads(path.read_text())

    if payload["status"] != "mpmath_interval_audit_not_lean_proof":
        raise ValueError("unexpected certificate status")

    i1 = payload["i1"]
    i1_floor = mp.mpf(i1["required_floor"])
    i1_min = mp.inf
    i1_argmin: dict[str, object] | None = None
    for row in i1["rows"]:
        x = rational_value(row["x"])
        if x < mp.mpf("0.6") or x > mp.mpf("0.77"):
            raise ValueError(f"I1 grid point out of range: {x}")
        value = mp.mpf(row["L_value"])
        lower = mp.mpf(row["L_interval"]["lower"])
        upper = mp.mpf(row["L_interval"]["upper"])
        rational_floor = rational_value(row["L_rational_floor"])
        if not lower <= value <= upper:
            raise ValueError(f"I1 decimal value outside interval at {x}")
        if rational_floor > lower:
            raise ValueError(f"I1 rational floor is above interval lower at {x}")
        if value < i1_floor:
            raise ValueError(f"I1 row below floor at {x}: {value} < {i1_floor}")
        if rational_floor < i1_floor:
            raise ValueError(f"I1 rational floor below required floor at {x}")
        if value < i1_min:
            i1_min = value
            i1_argmin = row["x"]
    if i1_argmin != i1["argmin"]:
        raise ValueError("I1 argmin does not match rows")
    if abs(i1_min - mp.mpf(i1["min_L"])) > mp.mpf("1e-50"):
        raise ValueError("I1 min_L does not match rows")

    i2 = payload["i2"]
    rows = i2["rows"]
    if len(rows) + 1 != int(i2["point_count"]):
        raise ValueError("I2 point count does not match row count")
    previous_right = None
    i2_min = mp.inf
    i2_min_left = None
    i2_min_right = None
    for row in rows:
        left = rational_value(row["left"])
        right = rational_value(row["right"])
        if previous_right is not None and left != previous_right:
            raise ValueError("I2 chain is not contiguous")
        if not left < right:
            raise ValueError(f"I2 row is not increasing: {left}, {right}")
        gap = mp.mpf(row["gap"])
        lower = mp.mpf(row["gap_interval"]["lower"])
        upper = mp.mpf(row["gap_interval"]["upper"])
        rational_floor = rational_value(row["gap_rational_floor"])
        if not lower <= gap <= upper:
            raise ValueError(f"I2 decimal gap outside interval between {left} and {right}")
        if rational_floor > lower:
            raise ValueError(f"I2 rational floor is above interval lower between {left} and {right}")
        if gap <= 0:
            raise ValueError(f"I2 nonpositive gap between {left} and {right}")
        if rational_floor <= 0:
            raise ValueError(f"I2 rational floor is not positive between {left} and {right}")
        recomputed_gap = g1(right) - g2(left)
        if abs(gap - recomputed_gap) > mp.mpf("1e-50"):
            raise ValueError(f"I2 gap mismatch between {left} and {right}")
        if gap < i2_min:
            i2_min = gap
            i2_min_left = row["left"]
            i2_min_right = row["right"]
        previous_right = right
    if i2_min_left != i2["min_gap_left"] or i2_min_right != i2["min_gap_right"]:
        raise ValueError("I2 min-gap location does not match rows")
    if abs(i2_min - mp.mpf(i2["min_gap"])) > mp.mpf("1e-50"):
        raise ValueError("I2 min_gap does not match rows")

    i3_margin = mp.mpf(payload["i3"]["analytic_margin"])
    i3_floor = rational_value(payload["i3"]["analytic_margin_rational_floor"])
    if i3_margin <= 0:
        raise ValueError("I3 margin is not positive")
    if i3_floor <= 0 or i3_floor > i3_margin:
        raise ValueError("I3 rational floor is invalid")

    return True


def entropy_gain(p: mp.mpf, q: mp.mpf) -> mp.mpf:
    return H(q) - H(p)


def one_coordinate_q_interval(p: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """Frechet interval for the OR marginal of one coupled Bernoulli bit."""
    p = mp.mpf(p)
    return p, min(2 * p, mp.mpf("1"))


def best_one_coordinate_q(p: mp.mpf) -> mp.mpf:
    """Entropy-maximizing OR marginal in the one-coordinate Frechet interval."""
    low, high = one_coordinate_q_interval(p)
    center = mp.mpf("0.5")
    if low <= center <= high:
        return center
    if high < center:
        return high
    return low


def print_one_coordinate_frontier() -> None:
    """Print the exact one-coordinate barrier shift from iid to coupled OR."""
    print("one-coordinate coupled OR frontier")
    print("p          iid_q      iid_gain       q_interval        best_q    best_gain")
    for k in range(10, 55, 5):
        p = mp.mpf(k) / 100
        iid_q = 2 * p - p * p
        q_low, q_high = one_coordinate_q_interval(p)
        q_best = best_one_coordinate_q(p)
        print(
            f"{float(p):.2f}       {float(iid_q):.6f}  "
            f"{float(entropy_gain(p, iid_q)):+.8f}  "
            f"[{float(q_low):.3f}, {float(q_high):.3f}]  "
            f"{float(q_best):.3f}     {float(entropy_gain(p, q_best)):+.8f}"
        )


def print_coupled_coordinate_probe() -> None:
    """Compare iid OR against centered coupled OR for one coordinate."""
    print("coordinate entropy probe")
    print("p          iid_q      iid_gain       centered_r  centered_gain")
    for k in range(25, 50, 3):
        p = mp.mpf(k) / 100
        iid_q = 2 * p - p * p
        centered_q = mp.mpf("0.5")
        centered_r = 2 * p - centered_q
        centered_feasible = centered_r >= 0 and centered_r <= p
        centered_gain = entropy_gain(p, centered_q) if centered_feasible else mp.nan
        print(
            f"{float(p):.2f}       {float(iid_q):.6f}  "
            f"{float(entropy_gain(p, iid_q)):+.8f}  "
            f"{float(centered_r):+.6f}    {float(centered_gain):+.8f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-ahs", action="store_true")
    parser.add_argument(
        "--emit-ahs-certificate",
        type=Path,
        help="write the finite AHS audit certificate payload as JSON",
    )
    parser.add_argument(
        "--check-ahs-certificate",
        type=Path,
        help="check an emitted finite AHS audit certificate JSON file",
    )
    parser.add_argument("--one-coordinate-frontier", action="store_true")
    parser.add_argument("--coupled-coordinate-probe", action="store_true")
    args = parser.parse_args()

    if args.verify_ahs:
        result = verify_ahs()
        print("AHS one-variable inequality audit")
        print(f"  phi=(sqrt(5)-1)/2 = {mp.nstr(PHI, 30)}")
        print(f"  Frankl constant 1-phi = {mp.nstr(FRANKL_CONSTANT, 30)}")
        print(
            "  I1 L-table: "
            f"min L={mp.nstr(result.i1_min_L, 20)} at x={mp.nstr(result.i1_argmin, 10)}, "
            f"required >= {mp.nstr(result.i1_required_floor, 20)}"
        )
        print(
            "  I2 monotone chain: "
            f"points={result.i2_point_count}, start={mp.nstr(result.i2_start, 10)}, "
            f"min gap={mp.nstr(result.i2_min_gap, 20)} "
            f"between {mp.nstr(result.i2_gap_arg[0], 10)} and {mp.nstr(result.i2_gap_arg[1], 10)}"
        )
        print(f"  I3 analytic margin: {mp.nstr(result.i3_margin, 20)}")
        ok = (
            result.i1_min_L >= result.i1_required_floor
            and result.i2_start < mp.mpf("0.76")
            and result.i2_min_gap > 0
            and result.i3_margin > 0
        )
        print(f"  audit_passed={ok}")
    if args.emit_ahs_certificate is not None:
        emit_ahs_certificate(args.emit_ahs_certificate)
        print(f"wrote {args.emit_ahs_certificate}")
    if args.check_ahs_certificate is not None:
        ok = check_ahs_certificate(args.check_ahs_certificate)
        print(f"certificate_checked={ok}")
    if args.one_coordinate_frontier:
        print_one_coordinate_frontier()
    if args.coupled_coordinate_probe:
        print_coupled_coordinate_probe()
    if (
        not args.verify_ahs
        and args.emit_ahs_certificate is None
        and args.check_ahs_certificate is None
        and not args.one_coordinate_frontier
        and not args.coupled_coordinate_probe
    ):
        parser.print_help()


if __name__ == "__main__":
    main()
