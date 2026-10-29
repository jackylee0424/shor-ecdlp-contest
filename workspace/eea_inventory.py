#!/usr/bin/env python3
"""Exact source-formula inventory for one measured secp256k1 EEA wrapper.

This is an independent integer transcription of the closed count formulas in
2607_13816/EEA/{Windows,IntervalPrimitiveCounts,SchedulePrimitiveCounts,
IndexedStepPrimitiveCounts,MeasuredBlockH,MeasuredEndIteration,
MeasuredScheduleCounts,MeasuredPrimitiveCounts,WrapperPrimitiveCounts}.lean.
It deliberately does not enumerate the emitted Straight program.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass


N = 256
STEPS = 1620
WRAPPERS_PER_WINDOW = 4
WINDOWS_PER_ROUND = 28
ROUNDS = 6
CCX_T = 7


@dataclass(frozen=True)
class Window:
    start: int
    stop: int

    @property
    def lanes(self) -> int:
        return self.stop + 1 - self.start


def ceil_div_at_least_one(numerator: int, denominator: int) -> int:
    # Lean: Int.toNat (max 1 (-((-numerator) / denominator))).  Python's //
    # has the same floor convention for the positive denominator used here.
    return max(1, -((-numerator) // denominator))


def windows(t: int) -> tuple[Window, Window, Window, Window, Window]:
    r_num = 1323 * (250 * (t - N - 1) - 727)
    q_num = 1323 * (250 * (t - 3 * (N + 1)) - 727)
    lt_num = 1323 * (250 * (t - 4 * (N + 1)) - 727)
    lrp_num = 1323 * (250 * t - 727)
    remainder = Window(min(ceil_div_at_least_one(r_num, 1_758_250) + 1, N + 3), N + 3)
    quotient = Window(
        min(ceil_div_at_least_one(q_num, 1_096_750) + 1, N + 2),
        max(1, min(t // 2 + 2, N + 2)),
    )
    coefficient = Window(1, max(1, min(t // 4 + 2, N + 1)))
    length_t = Window(
        min(ceil_div_at_least_one(lt_num, 766_000), N + 3),
        max(1, min(t // 4 + 3, N + 2)),
    )
    length_rp = Window(
        min(ceil_div_at_least_one(lrp_num, 2_089_000) + 2, N + 3), N + 3
    )
    return remainder, quotient, coefficient, length_t, length_rp


def interval_has_top_special(lanes: int) -> bool:
    return 1 < lanes and ((lanes - 1) & (lanes - 2)) == 0


def one_step(t: int) -> tuple[Counter[str], Counter[str], Counter[str]]:
    """Return CCX cells, measurement-erasure classes, and occurrence counts."""
    rem, quotient, coefficient, length_t, length_rp = windows(t)
    ql, qn = quotient.lanes, quotient.lanes - 1
    cl, cn = coefficient.lanes, coefficient.lanes - 1
    special = interval_has_top_special(rem.lanes)
    labels = rem.lanes - 1 if special else rem.lanes
    nodes = labels - 1

    ccx: Counter[str] = Counter()
    mbu: Counter[str] = Counter()
    occ: Counter[str] = Counter()

    # IndexedStepPrimitiveCounts: exact A--G split of the core vector.
    ccx["A terminal tests / padding / preshift"] += 906
    ccx["B surrounding controls"] += 198
    ccx["C terminal tests / epoch restore"] += 35
    ccx["D quotient length/sign control"] += 108 + ql + 2 * qn
    ccx["E boundary + coherent controls"] += 160
    ccx["E measured coefficient-prefix cells"] += 10 * cl + 4 * cn
    ccx["F postshift"] += 566
    ccx["G measured phase-update controls"] += 54

    # IntervalPrimitiveCounts: two complete B calls, each with two ripple scans.
    endpoint = 2 * 104
    # The adaptive ripple cells erase one clean AND per leaf, hence the count
    # formulas use (ripple{First,Second}CellToffoliCost mode - 1): 3+2=5,
    # not the coherent 4+3=7.
    top = 73 if special else 0
    traversal = 5 * labels + (4 if special else 0) + 4 * nodes
    per_interval = endpoint + top + traversal
    ccx["B interval endpoint prepare/restore"] += 2 * endpoint
    ccx["B interval top-special cells"] += 2 * top
    ccx["B measured interval ripple/decoder cells"] += 2 * traversal

    # Each interval call has 2*labels+4*nodes (+58 for the top-special pair)
    # measurement erasures; there are two interval calls in B.
    interval_mbu = 2 * labels + 4 * nodes + (58 if special else 0)
    mbu["B interval leaf/decoder erasures"] += 2 * interval_mbu
    mbu["E coefficient leaf/decoder erasures"] += 4 * (cl + cn)
    mbu["G phase-update v-chain erasures"] += 44

    occ["microsteps"] += 1
    occ["B interval calls"] += 2
    occ["B interval main-tree leaf visits"] += 4 * labels
    occ["B interval main-tree internal-node visits"] += 4 * nodes
    occ["E coefficient-prefix calls"] += 2
    occ["E coefficient leaf visits"] += 2 * cl
    occ["E coefficient internal-node visits"] += 2 * cn

    if t % 4 == 0:
        len4 = length_t.lanes
        decode5 = min(length_rp.stop + 1, N + 3)
        len5 = decode5 + 1 - length_rp.start
        # MeasuredEndIterationToffoliFormula plus the unchanged Block-H flag tests.
        ccx["H coherent length-zero flag tests"] += 66
        ccx["H controlled work-bank swap"] += 259
        ccx["H coherent constant add/sub"] += 64 + 36
        ccx["H measured upper zero-map cells"] += 24 * len4 - 16
        ccx["H measured lower zero-map cells"] += 24 * len5 - 16
        saved4 = 16 * len4 - 12
        saved5 = 16 * len5 - 12
        mbu["H upper zero-map erasures"] += saved4
        mbu["H lower zero-map erasures"] += saved5
        occ["H scheduled refreshes"] += 1
        occ["H upper zero-map lanes"] += len4
        occ["H lower zero-map lanes"] += len5

    # Guard against accidentally changing the algebra while refactoring labels.
    expected_core = (
        2027 + ql + 2 * qn + 10 * cl + 4 * cn + 2 * per_interval
    )
    if t % 4 == 0:
        expected_core += 66 + 259 + 64 + 36 + (24 * len4 - 16) + (24 * len5 - 16)
    assert sum(ccx.values()) == expected_core
    return ccx, mbu, occ


def total_schedule() -> tuple[Counter[str], Counter[str], Counter[str]]:
    ccx: Counter[str] = Counter()
    mbu: Counter[str] = Counter()
    occ: Counter[str] = Counter()
    for t in range(1, STEPS + 1):
        a, b, c = one_step(t)
        ccx.update(a)
        mbu.update(b)
        occ.update(c)
    return ccx, mbu, occ


def wrapper_inventory() -> tuple[Counter[str], Counter[str], Counter[str]]:
    ccx, mbu, occ = total_schedule()
    # WrapperPrimitiveCounts and PreprocessResources exact wrapper boundary.
    ccx["wrapper length initialize/uninitialize"] += 131_068
    ccx["wrapper centering comparator"] += 767
    ccx["wrapper centering constant adders"] += 1_528
    ccx["wrapper parity constant adders"] += 1_528
    ccx["wrapper canonical rotation"] += 2_620
    ccx["wrapper terminal epoch compression"] += 15
    mbu["wrapper centering comparator/adders"] += 766
    mbu["wrapper parity adders"] += 510
    return ccx, mbu, occ


def fmt(n: int) -> str:
    return f"{n:,}"


def main() -> None:
    schedule_ccx, schedule_mbu, occ = total_schedule()
    wrapper_ccx, wrapper_mbu, _ = wrapper_inventory()

    coherent_schedule_ccx = 17_454_225
    measured_h_savings = (
        schedule_mbu["H upper zero-map erasures"]
        + schedule_mbu["H lower zero-map erasures"]
    )
    measured_schedule_ccx = sum(schedule_ccx.values())
    wrapper_total_ccx = sum(wrapper_ccx.values())
    wrapper_t = CCX_T * wrapper_total_ccx
    per_window_t = WRAPPERS_PER_WINDOW * wrapper_t

    assert occ["microsteps"] == STEPS
    assert occ["H scheduled refreshes"] == 405
    assert measured_h_savings == 1_681_736  # MeasuredScheduleCounts
    assert coherent_schedule_ccx - measured_h_savings == measured_schedule_ccx
    assert measured_schedule_ccx == 15_772_489
    assert sum(schedule_mbu.values()) == 6_960_568
    assert wrapper_total_ccx == 15_910_015  # MeasuredPrimitiveCounts
    assert sum(wrapper_mbu.values()) == 6_961_844
    assert wrapper_t == 111_370_105
    assert per_window_t == 445_480_420

    print("EXACT RECONCILIATION")
    print(f"  schedule: {fmt(STEPS)} microsteps, {fmt(measured_schedule_ccx)} CCX")
    print(f"  coherent schedule before measured H: {fmt(coherent_schedule_ccx)} CCX")
    print(f"  measured-H saving: {fmt(measured_h_savings)} CCX")
    print(f"  schedule measured erasures: {fmt(sum(schedule_mbu.values()))}")
    print(f"  wrapper boundary overhead: {fmt(wrapper_total_ccx-measured_schedule_ccx)} CCX")
    print(f"  one wrapper: {fmt(wrapper_total_ccx)} CCX = {fmt(wrapper_t)} T")
    print(f"  four wrappers/window: {fmt(per_window_t)} T")

    print("\nCCX CELLS PER WRAPPER (descending)")
    for name, count in wrapper_ccx.most_common():
        print(f"  {fmt(count):>14}  {fmt(CCX_T*count):>15} T  {name}")

    print("\nMEASUREMENT ERASURES PER WRAPPER")
    for name, count in wrapper_mbu.most_common():
        print(f"  {fmt(count):>14}  {name}")

    print("\nSTRUCTURAL OCCURRENCES PER WRAPPER")
    for name, count in occ.most_common():
        print(f"  {fmt(count):>14}  {name}")

    print("\nTOP 10 CELLS ACROSS FOUR WRAPPERS PER ADDITION WINDOW")
    for name, count in wrapper_ccx.most_common(10):
        print(f"  {fmt(4*count):>14} CCX  {fmt(28*count):>15} T  {name}")

    print("\nEXACT SAVING CONVERSIONS")
    for label, saved_ccx_per_wrapper in [
        ("one CCX removed in every microstep", STEPS),
        ("Block-E middle: two CCX cleanups/microstep", 2*STEPS),
        ("all remaining 2-bit E controls: four CCX/microstep", 4*STEPS),
        ("one CCX removed per wrapper", 1),
    ]:
        save_window = WRAPPERS_PER_WINDOW * CCX_T * saved_ccx_per_wrapper
        save_round = WINDOWS_PER_ROUND * save_window
        save_total = ROUNDS * save_round
        print(
            f"  {label}: {fmt(save_window)} T/window; {fmt(save_round)} T/round; "
            f"{fmt(save_total)} T/6 rounds"
        )


if __name__ == "__main__":
    main()
