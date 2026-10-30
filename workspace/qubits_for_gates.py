#!/usr/bin/env python3
"""Exact integer pricing for Brief 18 (patch 10 qubits-for-T curve).

This is deliberately a resource calculator, not a circuit claim.  Rows marked
"conditional" are exact consequences of the stated replacement count, but the
replacement circuit/proof does not yet exist.
"""

from functools import lru_cache


BASE_Q = 856
BASE_T = 11_513_899_424
BASE_SCORE = BASE_Q * BASE_T

SIGNED_WINDOWS = 30
HORNER_CALLS_PER_WINDOW = 6
SQUARE_LADDERS_PER_WINDOW = 2
CCX_PER_LADDER = 1_110_533
CCX_PER_CONTROLLED_MODULAR_ADD = 2_813

# A 256-bit controlled modular add/sub contains two coherent carry chains:
# controlledAddCarry has 256 paired MAJ/UMA cleanup CCX, and
# controlledCompareLT has 256 paired majority/adjoint cleanup CCX.  The two
# chains are sequential, so a hypothetical held-AND rewrite can reuse a pool
# of 256 clean lanes.
WIDTH = 256
PAIRS_PER_MODULAR_STAGE = 2 * WIDTH
MODULAR_STAGES_PER_WINDOW = (
    HORNER_CALLS_PER_WINDOW * WIDTH
    + SQUARE_LADDERS_PER_WINDOW * WIDTH
    + 1  # retained subtraction between square and inverse-square ladders
)
MODULAR_STAGES = SIGNED_WINDOWS * MODULAR_STAGES_PER_WINDOW
T_PER_LOWERED_CCX = 5
HELD_AND_SAVING_PER_LANE = 2 * MODULAR_STAGES * T_PER_LOWERED_CCX

# Conditional C8 sensitivity point from the donor.  It is not an exact
# secp256k1 circuit: the quotient-flag erasure remains open.
TOTAL_LADDER_CALLS = SIGNED_WINDOWS * (
    HORNER_CALLS_PER_WINDOW + SQUARE_LADDERS_PER_WINDOW
)
DONOR_CCX_PER_BIT = 540
DONOR_CCX_PER_CALL = WIDTH * DONOR_CCX_PER_BIT
CURRENT_LADDER_T = TOTAL_LADDER_CALLS * CCX_PER_LADDER * T_PER_LOWERED_CCX
DONOR_LADDER_T = TOTAL_LADDER_CALLS * DONOR_CCX_PER_CALL * T_PER_LOWERED_CCX
DONOR_DELTA_T = CURRENT_LADDER_T - DONOR_LADDER_T

# Patch-10 target coefficient layout: direct 16-bit table, then 247 left bits
# and 224 right bits in signed windows of width at most 17.
ROW_CAP = 983_040
DIRECT_ROWS = 65_536
CURRENT_ROWS = 901_120


def new_score(added_wires: int, delta_t: int) -> int:
    return (BASE_Q + added_wires) * (BASE_T - delta_t)


def score_change(added_wires: int, delta_t: int) -> int:
    """New score minus patch-10 score; negative is better."""
    return new_score(added_wires, delta_t) - BASE_SCORE


def required_delta_t(added_wires: int) -> int:
    """Smallest integer T saving that strictly improves the score."""
    if added_wires == 0:
        return 1
    return (added_wires * BASE_T) // (BASE_Q + added_wires) + 1


def max_replacement_ccx_per_call(added_wires: int) -> int:
    """Largest integer CCX/call for replacing all 240 ladder calls profitably."""
    q = BASE_Q + added_wires
    fixed_t = BASE_T - CURRENT_LADDER_T
    max_new_t = (BASE_SCORE - 1) // q
    return (max_new_t - fixed_t) // (TOTAL_LADDER_CALLS * T_PER_LOWERED_CCX)


def signed_rows(width: int) -> int:
    return 1 << (width - 1)


@lru_cache(None)
def best_axis_rows(bits: int, windows: int):
    """Minimum (rows, widths) using exact widths 1..17, or None."""
    if windows == 0:
        return (0, ()) if bits == 0 else None
    best = None
    for width in range(1, 18):
        prior = best_axis_rows(bits - width, windows - 1)
        if prior is None:
            continue
        candidate = (prior[0] + signed_rows(width), prior[1] + (width,))
        if best is None or candidate < best:
            best = candidate
    return best


def best_layout_rows(signed_windows: int):
    """Minimum rows for 247 left + 224 right signed bits."""
    best = None
    for left_count in range(signed_windows + 1):
        left = best_axis_rows(247, left_count)
        right = best_axis_rows(224, signed_windows - left_count)
        if left is None or right is None:
            continue
        candidate = (DIRECT_ROWS + left[0] + right[0], left_count, left[1], right[1])
        if best is None or candidate < best:
            best = candidate
    return best


def pct(change: int) -> str:
    return f"{100 * change / BASE_SCORE:+.6f}%"


def main() -> None:
    assert BASE_SCORE == 9_855_897_906_944
    assert TOTAL_LADDER_CALLS == 240
    assert CURRENT_LADDER_T == 1_332_639_600
    assert MODULAR_STAGES_PER_WINDOW == 2_049
    assert MODULAR_STAGES == 61_470
    assert HELD_AND_SAVING_PER_LANE == 614_700
    assert DONOR_LADDER_T == 165_888_000
    assert DONOR_DELTA_T == 1_166_751_600
    assert best_layout_rows(30)[0] == CURRENT_ROWS
    assert best_layout_rows(29)[0] == 1_245_184

    print(f"patch10: Q={BASE_Q}, T={BASE_T:,}, score={BASE_SCORE:,}")
    print("break-even T savings")
    for k in (1, 2, 10, 20, 30, 40, 44, 45):
        print(f"  +{k:2d} wires: {required_delta_t(k):,} T")

    print("\nsource budgets")
    print(f"  Horner (180 calls): {180 * CCX_PER_LADDER:,} CCX, "
          f"{180 * CCX_PER_LADDER * 5:,} T")
    print(f"  square ladders (60 calls): {60 * CCX_PER_LADDER:,} CCX, "
          f"{60 * CCX_PER_LADDER * 5:,} T")
    print(f"  coherent modular stages: {MODULAR_STAGES:,}")
    print(f"  cleanup-pair CCX: {MODULAR_STAGES * PAIRS_PER_MODULAR_STAGE:,}")
    print(f"  held-AND conditional saving/lane: {HELD_AND_SAVING_PER_LANE:,} T")

    print("\ncandidate prices (new score minus patch10; negative wins)")
    candidates = (
        ("second compiler scratch", 1, 0),
        ("third compiler scratch", 2, 0),
        ("held carries, 1 lane (conditional)", 1, HELD_AND_SAVING_PER_LANE),
        ("held carries, 44 lanes (conditional)", 44, 44 * HELD_AND_SAVING_PER_LANE),
        ("held carries, all 256 lanes (conditional)", 256,
         WIDTH * HELD_AND_SAVING_PER_LANE),
        ("one 17-bit bank wire, no window cut", 1, 0),
        ("540 CCX/bit multiplier, independent pool (conditional)", 45,
         DONOR_DELTA_T),
    )
    for name, wires, delta_t in candidates:
        change = score_change(wires, delta_t)
        print(f"  {name}: +{wires}q, dT={delta_t:,}, "
              f"dScore={change:+,}, {pct(change)}")

    print("\nmarginal curve, exact/source-established positive-wire transformations")
    print("  No established positive-wire transformation saves T; with an at-most-Q")
    print("  budget the frontier is patch10 for every Q=856..900.")
    print("\nconditional held-carry forced-Q curve")
    for q in range(856, 901):
        k = q - BASE_Q
        delta_t = k * HELD_AND_SAVING_PER_LANE
        print(f"  {q}: T={BASE_T-delta_t:,}, score={new_score(k, delta_t):,}, "
              f"dScore={score_change(k, delta_t):+,}")

    print("\nconditional multiplier endpoint")
    for k in (44, 45):
        print(f"  +{k}q: max profitable replacement={max_replacement_ccx_per_call(k):,} "
              f"CCX/call; donor={DONOR_CCX_PER_CALL:,}")
    k = 45
    print(f"  Q={BASE_Q+k}: T={BASE_T-DONOR_DELTA_T:,}, "
          f"score={new_score(k, DONOR_DELTA_T):,}, "
          f"dScore={score_change(k, DONOR_DELTA_T):+,}")

    layout29 = best_layout_rows(29)
    print("\nrow-cap check")
    print(f"  current 30 signed windows: {CURRENT_ROWS:,} rows")
    print(f"  minimum 29 signed windows with widths <=17: {layout29[0]:,} rows")
    print(f"  cap excess: {layout29[0] - ROW_CAP:,} rows")


if __name__ == "__main__":
    main()
