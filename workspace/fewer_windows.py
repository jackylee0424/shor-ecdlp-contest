#!/usr/bin/env python3
"""Exact resource arithmetic and numerical mass diagnostics for Brief 14b.

Only the standard library is used.  Integer outputs are exact.  The sinc
integrals are diagnostics for the large-r finite sums; they are not Lean
proofs and are labelled as such in docs/FEWER-WINDOWS.md.
"""

from __future__ import annotations

from functools import lru_cache
from fractions import Fraction
from math import ceil, floor, pi, sin


ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
CANDIDATE_CAP = 56 * (2**49 + 2)
ROW_CAP = 983_040
QUBITS = 855
LEADER_T = 16_901_720_498
LEADER_SCORE = QUBITS * LEADER_T
SUBMISSION_BAR = 13_005_873_923_211

# Brief 15 base: dadon c6a88fc/c13a293 after stack patch 20.
STACK20_T = 15_351_820_448
STACK20_SCORE = 855 * STACK20_T
STACK20_LEFT_ROWS = 442_368
SIGNED_16_T = 512_157_359
SIGNED_17_T = 515_139_247

DIRECT_ROWS = 2**16
DIRECT_T = 458_745
PATCH_SAVING = 1_156_680
LEADER_SIGNED_T = 513_314_039 - PATCH_SAVING
LOOKUP_16_T = 91 * (2**15 - 1) + 85_848
FIXED_SIGNED_T = LEADER_SIGNED_T - LOOKUP_16_T


def trial_candidate_limit(right_bits: int) -> int:
    return 2 * (ORDER // 2**right_bits + 2)


def numerator_interval(r: int, precision: int, value: int) -> range:
    """Python form of protected Decoder.numeratorInterval (inclusive range)."""
    denominator = 2 * 2**precision
    lo = max(2 * r * value - r, 0) // denominator
    hi = (2 * r * value + r) // denominator
    return range(lo, hi + 1)


def wrapped_numerators(r: int, precision: int, value: int) -> set[int]:
    result = set(numerator_interval(r, precision, value))
    if value == 0:
        result.update(numerator_interval(r, precision, 2**precision))
    return result


def nearest_numerator(r: int, precision: int, value: int) -> int:
    return (2 * r * value + 2**precision) // (2 * 2**precision)


def wrapped_accepts(r: int, left_bits: int, right_bits: int,
                    left: int, right: int, secret: int) -> bool:
    """Exact protected accepted-set predicate, ignoring list order/dedup."""
    a = nearest_numerator(r, left_bits, left)
    if a % r == 0:
        return False
    target = (secret * a) % r
    return any(q % r == target for q in wrapped_numerators(r, right_bits, right))


def signed_rows(width: int) -> int:
    assert 1 <= width <= 17
    return 2 ** (width - 1)


def specialized_signed_t(width: int) -> int:
    rows = signed_rows(width)
    return FIXED_SIGNED_T + 91 * (rows - 1) + 85_848


@lru_cache(maxsize=None)
def best_axis(bits: int, windows: int) -> tuple[int, tuple[int, ...]] | None:
    """Minimum rows for an exact-width partition using signed widths 1..17."""
    if windows == 0:
        return (0, ()) if bits == 0 else None
    best = None
    for width in range(1, 18):
        if width > bits:
            break
        previous = best_axis(bits - width, windows - 1)
        if previous is None:
            continue
        candidate = (previous[0] + signed_rows(width), previous[1] + (width,))
        if best is None or candidate < best:
            best = candidate
    return best


def optimal_layout(left_bits: int, right_bits: int) -> dict[str, object]:
    """Lexicographically minimize signed-window count, then coefficient rows."""
    feasible = []
    for signed_count in range(1, 65):
        for left_count in range(signed_count + 1):
            left = best_axis(left_bits - 16, left_count)
            right = best_axis(right_bits, signed_count - left_count)
            if left is None or right is None:
                continue
            rows = DIRECT_ROWS + left[0] + right[0]
            if rows <= ROW_CAP:
                feasible.append((signed_count, rows, left[1], right[1]))
        if feasible:
            signed_count, rows, left, right = min(feasible)
            return {"signed": signed_count, "total": signed_count + 1,
                    "rows": rows, "left": left, "right": right}
    raise ValueError("no row-cap-feasible layout")


def exact_t(left_bits: int, right_bits: int, left: tuple[int, ...],
            right: tuple[int, ...], specialized: bool) -> int:
    if specialized:
        body = sum(specialized_signed_t(w) for w in left + right)
    else:
        body = len(left + right) * LEADER_SIGNED_T
    phases = left_bits * (left_bits - 1) // 2 + right_bits * (right_bits - 1) // 2
    return DIRECT_T + body + phases


def sinc(x: float) -> float:
    return 1.0 if x == 0.0 else sin(pi * x) / (pi * x)


def simpson(f, a: float, b: float, panels: int = 200_000) -> float:
    """Deterministic composite Simpson integration for printed diagnostics."""
    if panels % 2:
        panels += 1
    h = (b - a) / panels
    total = f(a) + f(b)
    for i in range(1, panels):
        total += (4 if i % 2 else 2) * f(a + i * h)
    return total * h / 3


def average_rounding_window(register_to_order_ratio: int) -> float:
    radius = register_to_order_ratio / 2
    return simpson(lambda x: sinc(x) ** 2, -radius, radius)


def average_same_window_pair(register_to_order_ratio: int) -> float:
    """Limiting retained correct-window mass for d=1 (wrong windows omitted)."""
    radius = register_to_order_ratio / 2

    def window_mass(x: float) -> float:
        lo = ceil(x - radius)
        # The endpoint convention is irrelevant to this integral (measure zero).
        hi = floor(x + radius - 1e-12)
        return sum(sinc(n - x) ** 2 for n in range(lo, hi + 1))

    return simpson(lambda x: window_mass(x) ** 2, 0.0, 1.0, 20_000)


def average_same_any_rounding_window_pair(register_to_order_ratio: int) -> float:
    """d=1 collision mass, including both axes choosing the same wrong window.

    The infinite sinc tail is truncated at 3,000 output offsets.  This is only
    a diagnostic; the document does not treat it as an exact finite-r value.
    """
    radius = register_to_order_ratio / 2

    def collision_mass(x: float) -> float:
        groups: dict[int, float] = {}
        for n in range(-3_000, 3_001):
            u = n - x
            group = floor(u / register_to_order_ratio + 0.5)
            groups[group] = groups.get(group, 0.0) + sinc(u) ** 2
        return sum(value * value for value in groups.values())

    # radius is referenced to make the grouping interpretation explicit.
    assert radius > 0
    return simpson(collision_mass, 0.0, 1.0, 1_000)


def average_coarse_bin(register_to_coarse_ratio: int) -> float:
    """Large-order diagnostic for rounding a fine QPE word to a coarse word.

    A coarse bin contains ``W`` fine outcomes.  As the target phase moves
    uniformly through that bin, sum the limiting sinc² kernel over precisely
    the outcomes which round back to the bin.  This is not a finite-order
    machine proof; it prices the success margin before Lean implementation.
    """
    W = register_to_coarse_ratio
    assert W > 0 and W % 2 == 0
    lo = -(W // 2)
    hi = W // 2
    return simpson(
        lambda x: sum(sinc(j - x) ** 2 for j in range(lo, hi)),
        -W / 2,
        W / 2,
        10_000,
    ) / W


def brief15_right_candidate(physical_bits: int) -> tuple[int, int, int, int]:
    """Conditional resources for 13 right windows on top of stack patch 20.

    Bits beyond 208 are supplied by replacing that many 16-bit windows by
    specialized 17-bit windows.  Such a tree and its extra bank wire are not
    implemented; these counts are the exact conditional resource price.
    """
    assert 208 <= physical_bits <= 212
    wide = physical_bits - 208
    rows = STACK20_LEFT_ROWS + 13 * 2**15 + wide * 2**15
    phase_saving = 224 * 223 // 2 - physical_bits * (physical_bits - 1) // 2
    t_model = STACK20_T - SIGNED_16_T + wide * (SIGNED_17_T - SIGNED_16_T) - phase_saving
    qubits = 855 if wide == 0 else 856
    return wide, rows, qubits, t_model


def peak_average() -> float:
    return simpson(lambda x: sinc(x) ** 2, -0.5, 0.5)


def widths_summary(widths: tuple[int, ...]) -> str:
    counts = {w: widths.count(w) for w in sorted(set(widths))}
    return "+".join(f"{n}x{w}" for w, n in counts.items())


def print_design(name: str, left_bits: int, right_bits: int) -> None:
    layout = optimal_layout(left_bits, right_bits)
    left = layout["left"]
    right = layout["right"]
    assert isinstance(left, tuple) and isinstance(right, tuple)
    old_t = exact_t(left_bits, right_bits, left, right, specialized=False)
    new_t = exact_t(left_bits, right_bits, left, right, specialized=True)
    print(f"{name}: {left_bits}/{right_bits}; {layout['signed']} signed + direct; "
          f"rows={layout['rows']:,}")
    print(f"  left={widths_summary(left)}; right={widths_summary(right)}")
    print(f"  leader-tree T={old_t:,}; specialized-tree T={new_t:,}; "
          f"score={QUBITS * new_t:,}; vs leader={(new_t / LEADER_T - 1) * 100:.9f}%")


def main() -> None:
    assert LEADER_SCORE == 14_450_971_025_790
    assert LEADER_SIGNED_T == 512_157_359
    assert LOOKUP_16_T == 3_067_645
    assert FIXED_SIGNED_T == 509_089_714
    assert specialized_signed_t(15) == 510_666_415
    assert specialized_signed_t(16) == LEADER_SIGNED_T
    assert specialized_signed_t(17) == 515_139_247

    print("candidate budget")
    for bits in range(202, 209):
        limit = trial_candidate_limit(bits)
        print(f"  R={bits}: limit={limit:,}; fits={limit <= CANDIDATE_CAP}")
    assert trial_candidate_limit(202) == 2**55 + 2
    assert trial_candidate_limit(203) == 2**54 + 2
    assert trial_candidate_limit(202) > CANDIDATE_CAP
    assert trial_candidate_limit(203) <= CANDIDATE_CAP

    print("\nlarge-r mass diagnostics (not finite-r proofs)")
    print(f"  nearest-bin average={peak_average():.15f}")
    for ratio in (32, 64, 128):
        one = average_rounding_window(ratio)
        pair = average_same_window_pair(ratio)
        print(f"  N/r={ratio}: marginal={one:.15f}; union={2 * one - 1:.15f}; "
              f"d=1 retained pair={pair:.15f}")
    grouped_32 = average_same_any_rounding_window_pair(32)
    print(f"  N/r=32: d=1 same-any-window diagnostic={grouped_32:.15f}")
    assert 0.98740 < grouped_32 < 0.98742

    print("\nresource optima")
    print_design("leader packing", 263, 263)
    print_design("sharper nearestPair", 262, 262)
    print_design("minimum-budget wrappedShift", 263, 203)
    print_design("combined speculative", 262, 203)

    baseline = optimal_layout(263, 263)
    sharp = optimal_layout(262, 262)
    wrapped = optimal_layout(263, 203)
    assert (baseline["signed"], baseline["rows"]) == (33, 851_968)
    assert (sharp["signed"], sharp["rows"]) == (33, 819_200)
    assert (wrapped["signed"], wrapped["rows"]) == (29, 786_432)

    left = wrapped["left"]
    right = wrapped["right"]
    assert isinstance(left, tuple) and isinstance(right, tuple)
    wrapped_current_t = exact_t(263, 203, left, right, specialized=False)
    wrapped_special_t = exact_t(263, 203, left, right, specialized=True)
    assert wrapped_current_t == 14_853_077_112
    assert QUBITS * wrapped_current_t == 12_699_380_930_760
    assert wrapped_special_t == 14_832_203_896
    assert QUBITS * wrapped_special_t == 12_681_534_331_080
    assert QUBITS * wrapped_special_t < SUBMISSION_BAR

    print("\nBrief 15: one fewer right window on c13a293 + patch 20")
    threshold = (99 / 100) / (200 / 201)
    print(f"  required averaged right mass before negligible finite corrections: {threshold:.9f}")
    forced_failure = Fraction(11_449, 1_128_960)
    floor_loss = Fraction(1_153, 882 * ORDER)
    finite_208_upper = Fraction(200, 201) * (1 - forced_failure + floor_loss)
    print(f"  rigorous finite B=208 combined upper: {float(finite_208_upper):.12f}")
    for bits in range(208, 213):
        W = 2 ** (bits - 203)
        mass = average_coarse_bin(W)
        wide, rows, qubits, t_model = brief15_right_candidate(bits)
        score = qubits * t_model
        print(f"  B={bits}, W={W}: right={mass:.12f}, with-left={mass*200/201:.12f}; "
              f"17-bit={wide}, rows={rows:,}, Q={qubits}, T={t_model:,}, QxT={score:,}, "
              f"row-fit={rows <= ROW_CAP}")
    assert average_coarse_bin(32) * 200 / 201 < 0.99
    assert finite_208_upper < Fraction(99, 100)
    assert average_coarse_bin(128) * 200 / 201 < 0.99
    assert average_coarse_bin(256) * 200 / 201 > 0.99
    assert brief15_right_candidate(211)[1] <= ROW_CAP
    assert brief15_right_candidate(212)[1] > ROW_CAP

    # At 212 right bits, trimming the left axis to 262 converts one 16-bit
    # left window to 15 bits.  This saves exactly the missing 16,384 rows.
    right_212 = average_coarse_bin(512)
    left_262 = average_rounding_window(64)
    _, rows_212, qubits_212, t_212 = brief15_right_candidate(212)
    rows_262_212 = rows_212 - 2**14
    t_262_212 = t_212 - (SIGNED_16_T - specialized_signed_t(15)) - 262
    print(f"  B=212 with left=262: averaged union diagnostic="
          f"{left_262 + right_212 - 1:.12f}; rows={rows_262_212:,}, "
          f"Q={qubits_212}, T={t_262_212:,}, QxT={qubits_212*t_262_212:,}")
    assert rows_262_212 == ROW_CAP
    assert left_262 + right_212 - 1 > 0.99


if __name__ == "__main__":
    main()
