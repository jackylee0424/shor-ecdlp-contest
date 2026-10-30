#!/usr/bin/env python3
"""Exact-integer screening arithmetic for Brief 23.

This file deliberately separates three kinds of number:

* ``proved``: kernel-backed counts already present in the leader/protected tree;
* ``floor``: an exact subtraction, but not an implementable circuit count;
* ``screen``: an exact evaluation of an explicitly stated research profile whose
  width/circuit hypotheses are not yet proved.

Nothing in this calculator is a new Certificate or an exact resource theorem for
divsteps/greedyfrog.  It is intended to prevent rounded-paper and sampled-donor
numbers from being mistaken for challenge bounds.
"""

from dataclasses import dataclass


N = 256
WINDOWS = 29
EEA_PER_WINDOW = 4
EEA_OCCURRENCES = WINDOWS * EEA_PER_WINDOW
LOWERED_T_PER_CCX = 4

BASE_Q = 856
BASE_T = 8_480_934_044
BASE_SCORE = BASE_Q * BASE_T
BASE_RECORD_BOUND = 8_266_128_294
OFFICIAL_RECORD_LIMIT = 47_471_340_504

# Protected measured wrapper, before the leader's literal cancellation.
RAW_WRAPPER_CCX = 15_910_015
RAW_WRAPPER_ALGORITHM_RECORDS = 6_961_844

# The leader proves 714 T of source-level cancellation in every one of 1,620
# microsteps.  Before 4-P lowering, 714 T = 102 ordinary 7-T CCX.
MICROSTEPS = 1_620
CANCEL_T_PER_STEP_BEFORE_LOWERING = 714
CANCEL_CCX_PER_STEP = CANCEL_T_PER_STEP_BEFORE_LOWERING // 7
CANCEL_CCX_PER_WRAPPER = MICROSTEPS * CANCEL_CCX_PER_STEP
EFFECTIVE_WRAPPER_CCX = RAW_WRAPPER_CCX - CANCEL_CCX_PER_WRAPPER

# After the compiler/catalyst stack, each remaining CCX contributes four P/T
# gates.  The catalyst's one global preparation T remains in NON_EEA_T.
BASE_EEA_T = EEA_OCCURRENCES * LOWERED_T_PER_CCX * EFFECTIVE_WRAPPER_CCX
NON_EEA_T = BASE_T - BASE_EEA_T

# Exact inventory terms identified as repeated data-dependent boundary location.
# Counts are per wrapper before cancellation.
RAW_LOCATION_CCX = 4_387_970 + 3_998_010 + 673_920

# Of the 102 cancelled CCX/microstep, 72 are in B/E location work:
# B1 twice (28), B2 (32), E prepare/clean (12).  The other 30 are A/epoch.
LOCATION_CANCEL_CCX_PER_STEP = 72
EFFECTIVE_LOCATION_CCX = RAW_LOCATION_CCX - MICROSTEPS * LOCATION_CANCEL_CCX_PER_STEP
ZERO_LOCATION_FLOOR_CCX = EFFECTIVE_WRAPPER_CCX - EFFECTIVE_LOCATION_CCX

# B/E measured erasures attributable to the location scans.
LOCATION_ALGORITHM_RECORDS = 2_925_752 + 2_281_800
ZERO_LOCATION_ALGORITHM_RECORDS = RAW_WRAPPER_ALGORITHM_RECORDS - LOCATION_ALGORITHM_RECORDS


@dataclass(frozen=True)
class Projection:
    name: str
    status: str
    qubits: int
    wrapper_ccx: int
    algorithm_records_per_wrapper: int

    @property
    def replacement_t(self) -> int:
        return EEA_OCCURRENCES * LOWERED_T_PER_CCX * self.wrapper_ccx

    @property
    def total_t(self) -> int:
        return NON_EEA_T + self.replacement_t

    @property
    def score(self) -> int:
        return self.qubits * self.total_t

    @property
    def records_per_wrapper(self) -> int:
        # One compiler measurement is introduced per lowered CCX.
        return self.wrapper_ccx + self.algorithm_records_per_wrapper

    @property
    def projected_record_bound(self) -> int:
        # Bookkeeping projection against the leader's conservative bound.  This
        # is useful for capacity screening, not an exact finalCursor theorem.
        current = EFFECTIVE_WRAPPER_CCX + RAW_WRAPPER_ALGORITHM_RECORDS
        return (
            BASE_RECORD_BOUND
            - EEA_OCCURRENCES * current
            + EEA_OCCURRENCES * self.records_per_wrapper
        )

    @property
    def score_change_ppm(self) -> int:
        return (self.score - BASE_SCORE) * 1_000_000 // BASE_SCORE


def strict_total_t_ceiling(qubits: int, score_numerator: int = BASE_SCORE, score_denominator: int = 1) -> int:
    """Largest T with q*T strictly below score_numerator/score_denominator."""
    return (score_numerator - 1) // (score_denominator * qubits)


def strict_wrapper_ccx_ceiling(qubits: int, ten_percent: bool = False) -> int:
    """Largest uniform replacement CCX/wrapper under a strict score target."""
    if ten_percent:
        total_t = strict_total_t_ceiling(qubits, 9 * BASE_SCORE, 10)
    else:
        total_t = strict_total_t_ceiling(qubits)
    return (total_t - NON_EEA_T) // (EEA_OCCURRENCES * LOWERED_T_PER_CCX)


def divstep_screen(*, ticks: int, ring_width: int, h_bits: int = 11) -> tuple[int, int]:
    """Return (CCX, algorithm records) for the stated *screening* tick model.

    Per tick this charges two fixed-width signed-add/cswap lane passes (2W),
    sigma/control and a conservative two-h_bits delta update.  Sign conjugation
    is Clifford.  Records charge one measured carry/AND erase per ring lane and
    two decision/control erasures.  These formulas are a milestone target, not
    a proved circuit receipt.
    """
    ccx_per_tick = 2 * ring_width + 2 * h_bits + 1
    algorithm_records_per_tick = ring_width + 2
    return ticks * ccx_per_tick, ticks * algorithm_records_per_tick


CURRENT = Projection(
    "leader EEA after cancellation",
    "proved",
    BASE_Q,
    EFFECTIVE_WRAPPER_CCX,
    RAW_WRAPPER_ALGORITHM_RECORDS,
)

V3_RAW = Projection(
    "v3/protected wrapper before leader cancellation",
    "proved but dominated",
    BASE_Q,
    RAW_WRAPPER_CCX,
    RAW_WRAPPER_ALGORITHM_RECORDS,
)

HYBRID_FLOOR = Projection(
    "zero-cost B/E boundary-location floor",
    "floor, no circuit",
    BASE_Q,
    ZERO_LOCATION_FLOOR_CCX,
    ZERO_LOCATION_ALGORITHM_RECORDS,
)

# Conditional packed-ring divstep screen: 340 is the conservative research
# width discussed in ECDSAFAIL-855, and 952 = 856 + 2*(340-292) assumes the
# donor's two-ring sharing and all other leader owners transfer unchanged.
BY590_CCX, BY590_ALGORITHM_RECORDS = divstep_screen(ticks=590, ring_width=340)
BY590_SCREEN = Projection(
    "BY half-delta, 590 ticks, W=340",
    "screen, width/replay unproved",
    952,
    BY590_CCX,
    BY590_ALGORITHM_RECORDS,
)

BY590_FALLBACK_SCREEN = Projection(
    "BY 590-tick arithmetic at four-word fallback width",
    "score-only screen; full layout/count absent",
    1_290,
    BY590_CCX,
    BY590_ALGORITHM_RECORDS,
)

BY742_CCX, BY742_ALGORITHM_RECORDS = divstep_screen(ticks=742, ring_width=340)
BY742_SCREEN = Projection(
    "BY theorem-11.2-style, 742 ticks, W=340",
    "screen, width/replay unproved",
    952,
    BY742_CCX,
    BY742_ALGORITHM_RECORDS,
)

# Greedyfrog screen.  469 = 405 non-stall slots + ceil(512/8) stalls is only a
# proposed consequence of a future <=2n total-renormalisation theorem.  The
# donor's unwindowed forward/reverse prices are retained exactly here.  There
# are two forward and two reverse occurrences per window.
GREEDY_SLOTS = 405 + (2 * N + 7) // 8
GREEDY_FORWARD_CCX = GREEDY_SLOTS * 5_496
GREEDY_REVERSE_CCX = GREEDY_SLOTS * 12_754
GREEDY_AVERAGE_WRAPPER_CCX = (GREEDY_FORWARD_CCX + GREEDY_REVERSE_CCX) // 2
GREEDY_SCREEN = Projection(
    "greedyfrog unwindowed, 469-slot screen",
    "screen, exact decode/slot theorem absent",
    841,
    GREEDY_AVERAGE_WRAPPER_CCX,
    # Conservative screen: charge one algorithmic measured erase for every
    # CCX as well as three recorded slot decisions.  The donor does not expose
    # a challenge-compatible exact record receipt, so this is intentionally an
    # upper profile rather than a claimed transcription of its mean stream.
    GREEDY_AVERAGE_WRAPPER_CCX + 3 * GREEDY_SLOTS,
)


def pct(delta: int, base: int) -> str:
    return f"{100.0 * delta / base:+.9f}%"


def main() -> None:
    assert BASE_SCORE == 7_259_679_541_664
    assert CANCEL_CCX_PER_STEP == 102
    assert CANCEL_CCX_PER_WRAPPER == 165_240
    assert EFFECTIVE_WRAPPER_CCX == 15_744_775
    assert BASE_EEA_T == 7_305_575_600
    assert NON_EEA_T == 1_175_358_444
    assert RAW_LOCATION_CCX == 9_059_900
    assert EFFECTIVE_LOCATION_CCX == 8_943_260
    assert ZERO_LOCATION_FLOOR_CCX == 6_801_515
    assert ZERO_LOCATION_ALGORITHM_RECORDS == 1_754_292
    assert BY590_CCX == 414_770
    assert BY742_CCX == 521_626
    assert GREEDY_SLOTS == 469
    assert GREEDY_FORWARD_CCX == 2_577_624
    assert GREEDY_REVERSE_CCX == 5_981_626
    assert GREEDY_AVERAGE_WRAPPER_CCX == 4_279_625

    print(f"leader: {BASE_Q:,} x {BASE_T:,} = {BASE_SCORE:,}")
    print(f"effective EEA: {EFFECTIVE_WRAPPER_CCX:,} CCX/wrapper, {BASE_EEA_T:,} T total")
    print(f"non-EEA retained T: {NON_EEA_T:,}")
    print()
    print("candidate | kind | Q | CCX/wrapper | total T | QxT | change | records/wrapper | projected records")
    for p in (
        CURRENT,
        V3_RAW,
        HYBRID_FLOOR,
        BY590_SCREEN,
        BY590_FALLBACK_SCREEN,
        BY742_SCREEN,
        GREEDY_SCREEN,
    ):
        assert p.projected_record_bound < OFFICIAL_RECORD_LIMIT
        print(
            f"{p.name} | {p.status} | {p.qubits:,} | {p.wrapper_ccx:,} | "
            f"{p.total_t:,} | {p.score:,} | {pct(p.score - BASE_SCORE, BASE_SCORE)} | "
            f"{p.records_per_wrapper:,} | {p.projected_record_bound:,}"
        )

    print()
    print("strict wrapper-CCX ceilings")
    print("Q | any improvement | >10% improvement")
    for q in (835, 841, 855, 856, 900, 952, 1_112, 1_290, 1_400):
        print(f"{q:,} | {strict_wrapper_ccx_ceiling(q):,} | {strict_wrapper_ccx_ceiling(q, True):,}")

    # The projection requested by the brief is exact integer arithmetic under
    # the explicitly conditional BY590 profile.
    assert BY590_SCREEN.total_t == 1_367_811_724
    assert BY590_SCREEN.score == 1_302_156_761_248
    assert BY590_FALLBACK_SCREEN.score == 1_764_477_123_960


if __name__ == "__main__":
    main()
