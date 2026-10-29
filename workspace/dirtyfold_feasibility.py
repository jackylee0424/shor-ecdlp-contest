#!/usr/bin/env python3
"""Exact single-trial pricing and algebra checks for Brief 16.

This deliberately distinguishes proved/current costs from conditional fast-cell
costs.  A conditional row is not a passed gate until every component named in
that row has a circuit and a worst-case count.
"""

from dataclasses import dataclass
from fractions import Fraction
import random

N_BITS = 256
N = 1 << N_BITS
C = (1 << 32) + 977
P = N - C
WINDOWS = 30
CALLS_PER_WINDOW = 8
SPACIOUS_CALLS = 5
TIGHT_CALLS = 3
OLD_CELL_CCX = 2813 + 1531
OLD_CALL_CCX = 1_110_533
BASE_T = 15_365_238_944
BASE_SCORE = 855 * BASE_T


def pct_cut(new_t: int) -> float:
    return 100.0 * (BASE_T - new_t) / BASE_T


def project(cell_spacious: int, cell_tight: int) -> tuple[int, int, float]:
    """Replace the 255 recurring cells in each of eight calls per window.

    The old call also has one terminal modular addition.  It is retained, so
    only 255 * OLD_CELL_CCX is replaced in each call.
    """
    old_replaced = WINDOWS * CALLS_PER_WINDOW * 255 * OLD_CELL_CCX * 7
    new_replaced = WINDOWS * 255 * 7 * (
        SPACIOUS_CALLS * cell_spacious + TIGHT_CALLS * cell_tight
    )
    new_t = BASE_T - old_replaced + new_replaced
    return new_t, 855 * new_t, pct_cut(new_t)


def fused_classical(z: int, y: int, sign: int) -> tuple[int, int, int, int, int]:
    """Classical skeleton of the exact signed-add/double fused cell.

    Returns (answer, raw carry k, rotated word d, small signed addend B,
    quotient q).  The exact correction is `d + B - q*p`.
    """
    assert 0 <= z < P and 0 <= y < P and sign in (0, 1)
    raw_z = z if sign == 0 else N - 1 - z
    total = raw_z + y
    k, w = divmod(total, N)
    v = w if sign == 0 else N - 1 - w
    h = v >> (N_BITS - 1)
    d = ((v << 1) & (N - 1)) | h
    eps = 1 if sign == 0 else -1
    small = 2 * eps * k * C + h * (C - 1)
    q = (d + small) // P
    answer = d + small - q * P
    assert answer == (2 * (z + eps * y)) % P
    assert 0 <= answer < P
    return answer, k, d, small, q


def exercise_algebra() -> dict[int, int]:
    rng = random.Random(16)
    edge = [0, 1, C - 1, C, P // 2 - 1, P // 2, P - 2, P - 1]
    qs: dict[int, int] = {}
    pairs = [(z, y) for z in edge for y in edge]
    pairs += [(rng.randrange(P), rng.randrange(P)) for _ in range(20_000)]
    for z, y in pairs:
        for sign in (0, 1):
            *_, q = fused_classical(z, y, sign)
            qs[q] = qs.get(q, 0) + 1
    return qs


@dataclass(frozen=True)
class Row:
    name: str
    spacious: int
    tight: int
    status: str


def main() -> None:
    print(f"base: {BASE_T:,} T; score {BASE_SCORE:,}")
    print(f"old recurring cell: {OLD_CELL_CCX:,} CCX; old call: {OLD_CALL_CCX:,} CCX")
    print(f"exact fused quotient values observed: {exercise_algebra()}")
    rows = [
        Row("unchanged proved cell", OLD_CELL_CCX, OLD_CELL_CCX, "proved"),
        # Sensitivity rows only.  They are not circuit claims.
        Row("threshold at 3%", 2623, 4338, "conditional sensitivity"),
        Row("candidate target", 2500, 3500, "conditional sensitivity"),
    ]
    for row in rows:
        t, score, cut = project(row.spacious, row.tight)
        print(
            f"{row.name}: high={row.spacious} low={row.tight} CCX/cell; "
            f"T={t:,}; score={score:,}; cut={cut:.6f}% [{row.status}]"
        )
    threshold_sum = Fraction(
        8 * OLD_CELL_CCX * WINDOWS * 255 * 7
        - Fraction(3, 100) * BASE_T,
        WINDOWS * 255 * 7,
    )
    print(
        "3% weighted condition: "
        f"5*high + 3*low < {float(threshold_sum):.6f} CCX"
    )


if __name__ == "__main__":
    main()
