#!/usr/bin/env python3
"""Reproduce Brief 15's coarse-bin diagnostics and conditional resources.

The integer resource counts are exact.  The sinc integrals are large-order
diagnostics, not finite-order proofs and not grounds for enabling this patch.
"""

from fractions import Fraction
from math import pi, sin

ROW_CAP = 983_040
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
STACK20_T = 15_351_820_448
STACK20_LEFT_ROWS = 442_368
SIGNED_15_T = 510_666_415
SIGNED_16_T = 512_157_359
SIGNED_17_T = 515_139_247


def sinc(x: float) -> float:
    return 1.0 if x == 0.0 else sin(pi * x) / (pi * x)


def simpson(f, a: float, b: float, panels: int = 10_000) -> float:
    if panels % 2:
        panels += 1
    h = (b - a) / panels
    total = f(a) + f(b)
    for i in range(1, panels):
        total += (4 if i % 2 else 2) * f(a + i * h)
    return total * h / 3


def coarse_bin_mass(width: int) -> float:
    half = width // 2
    return simpson(
        lambda x: sum(sinc(j - x) ** 2 for j in range(-half, half)),
        -half,
        half,
    ) / width


def resources(bits: int) -> tuple[int, int, int, int]:
    wide = bits - 208
    rows = STACK20_LEFT_ROWS + 13 * 2**15 + wide * 2**15
    phases = 224 * 223 // 2 - bits * (bits - 1) // 2
    t_model = STACK20_T - SIGNED_16_T + wide * (SIGNED_17_T - SIGNED_16_T) - phases
    qubits = 855 if wide == 0 else 856
    return wide, rows, qubits, t_model


def main() -> None:
    threshold = (99 / 100) / (200 / 201)
    print(f"required right average with the 263-bit left bound: {threshold:.9f}")
    # A finite, conservative no-go upper bound for B=208.  Four disjoint
    # quarter/eighth-outcome strips next to the positive coarse-bin boundary
    # force one excluded fine outcome to carry the stated sinc² lower mass.
    forced_failure = Fraction(11_449, 1_128_960)
    floor_loss = Fraction(1_153, 882 * ORDER)
    right_208_upper = 1 - forced_failure + floor_loss
    combined_208_upper = Fraction(200, 201) * right_208_upper
    print(f"finite B=208 upper bound: right<{float(right_208_upper):.12f}, "
          f"combined<{float(combined_208_upper):.12f}")
    for bits in range(208, 213):
        width = 2 ** (bits - 203)
        right = coarse_bin_mass(width)
        wide, rows, qubits, t_model = resources(bits)
        print(f"B={bits}: right={right:.12f}, combined={right*200/201:.12f}, "
              f"17-bit={wide}, rows={rows:,}, Q={qubits}, T={t_model:,}, "
              f"QxT={qubits*t_model:,}, row-fit={rows <= ROW_CAP}")

    # The B=212 option misses the row cap by exactly one 15-bit block.  A
    # 262-bit left axis converts one 16-bit left window to 15 bits and fits.
    _, rows, qubits, t_model = resources(212)
    rows -= 2**14
    t_model -= SIGNED_16_T - SIGNED_15_T
    t_model -= 262
    left_262 = 0.996833869611197
    right_212 = coarse_bin_mass(512)
    print(f"B=212, L=262: union diagnostic={left_262+right_212-1:.12f}, "
          f"rows={rows:,}, Q={qubits}, T={t_model:,}, QxT={qubits*t_model:,}")

    assert coarse_bin_mass(32) * 200 / 201 < 0.99
    assert combined_208_upper < Fraction(99, 100)
    assert coarse_bin_mass(128) * 200 / 201 < 0.99
    assert coarse_bin_mass(256) * 200 / 201 > 0.99
    assert resources(211)[1] <= ROW_CAP
    assert resources(212)[1] > ROW_CAP
    assert rows == ROW_CAP


if __name__ == "__main__":
    main()
