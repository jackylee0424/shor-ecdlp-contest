#!/usr/bin/env python3
"""Exact resource projection for Brief 29's hypothetical WEX adder swap.

This is arithmetic only.  It does not claim that the 0b650bb program has the
uniform table-template interface needed by WEX; docs/WEX-SWAP.md audits that
separate feasibility question.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Limits:
    gate_slots: int = 4_000_000_000_000_000
    measurements: int = 47_471_340_504
    coefficient_rows: int = 983_040
    candidate_checks: int = 56 * (2**49 + 2)


LIMITS = Limits()

# Unchanged f1518daf producer/compiler ledger.
ADDITIONS = 29
FIRST_LOAD_CCX = 65_535
FOURIER_T = 56_773
LOOKUP_TRAVERSALS = 24
CCX_PER_TRAVERSAL = 32_767
OUTER_NEGATION_CCX = 2_044
RESET_RECORDS = 854
AXIS_RECORDS = 474
NEIGHBOR_RECORDS = 34_114
COEFFICIENT_ROWS = 917_504
CANDIDATE_CHECKS = 55 * (2**49 + 2)
SOURCE_SLOT_BOUND = 90_000_176_648

# Accepted ecdsafail-lean 0b650bb bounds.
FRONTIER_QUBITS = 1_594
FRONTIER_CCX = 2_155_232
FRONTIER_RECORDS = 1_501_195
FRONTIER_SLOT_BOUND = 50_000_004

# f1518daf and its c3f340a arithmetic component.
LEADER_QUBITS = 1_932
LEADER_T = 348_877_454
LEADER_SCORE = 674_031_241_128
OLD_ADDER_QUBITS = 1_899
OLD_ADDER_CCX = 2_216_363


def t_after_four_p(body_ccx: int) -> int:
    return 4 * (FIRST_LOAD_CCX + ADDITIONS * body_ccx) + FOURIER_T + 1


def source_t_bound(body_ccx: int) -> int:
    """The conservative pre-lowering bound reused as a record/slot allowance."""
    return 7 * (FIRST_LOAD_CCX + ADDITIONS * body_ccx) + FOURIER_T


def main() -> None:
    old_body = OLD_ADDER_CCX + LOOKUP_TRAVERSALS * CCX_PER_TRAVERSAL + OUTER_NEGATION_CCX
    assert old_body == 3_004_815
    assert t_after_four_p(old_body) == LEADER_T
    assert LEADER_QUBITS * LEADER_T == LEADER_SCORE

    projected_qubits = LEADER_QUBITS - (OLD_ADDER_QUBITS - FRONTIER_QUBITS)
    body_ccx = FRONTIER_CCX + LOOKUP_TRAVERSALS * CCX_PER_TRAVERSAL + OUTER_NEGATION_CCX
    body_records = FRONTIER_RECORDS + LOOKUP_TRAVERSALS * CCX_PER_TRAVERSAL + OUTER_NEGATION_CCX
    parent_ccx = FIRST_LOAD_CCX + ADDITIONS * body_ccx
    t_model = t_after_four_p(body_ccx)
    score = projected_qubits * t_model

    source_records = (
        FIRST_LOAD_CCX
        + ADDITIONS * body_records
        + AXIS_RECORDS
        + RESET_RECORDS
        + NEIGHBOR_RECORDS
    )
    pre_lower_t = source_t_bound(body_ccx)
    conservative_measurements = source_records + pre_lower_t
    exact_lowering_records = source_records + parent_ccx

    # The unchanged producer takes max(3e9, body slot bound), so 0b650bb's
    # 50,000,004-slot bound does not change the certified source slot bound.
    assert FRONTIER_SLOT_BOUND < 3_000_000_000
    conservative_slots = SOURCE_SLOT_BOUND + 24 * pre_lower_t + 2

    assert projected_qubits == 1_627
    assert body_ccx == 2_943_684
    assert body_records == 2_289_647
    assert parent_ccx == 85_432_371
    assert t_model == 341_786_258
    assert score == 556_086_241_766
    assert source_records == 66_500_740
    assert pre_lower_t == 598_083_370
    assert exact_lowering_records == 151_933_111
    assert conservative_measurements == 664_584_110
    assert conservative_slots == 104_354_177_530

    assert conservative_slots <= LIMITS.gate_slots
    assert conservative_measurements <= LIMITS.measurements
    assert COEFFICIENT_ROWS <= LIMITS.coefficient_rows
    assert CANDIDATE_CHECKS <= LIMITS.candidate_checks

    delta = score - LEADER_SCORE
    pct = 100 * delta / LEADER_SCORE
    print(f"projected qubits:             {projected_qubits:,}")
    print(f"body CCX:                    {body_ccx:,}")
    print(f"  arithmetic:                {FRONTIER_CCX:,}")
    print(f"  24 x 32,767 lookups:       {LOOKUP_TRAVERSALS * CCX_PER_TRAVERSAL:,}")
    print(f"  two outer negations:       {OUTER_NEGATION_CCX:,}")
    print(f"parent eligible CCX:         {parent_ccx:,}")
    print(f"projected T-model:           {t_model:,}")
    print(f"projected Q x T:             {score:,} ({pct:+.6f}% vs leader)")
    print(f"body source records:         {body_records:,}")
    print(f"parent source records:       {source_records:,}")
    print(f"exact post-lowering records: {exact_lowering_records:,}")
    print(f"conservative measurement UB: {conservative_measurements:,}")
    print(f"conservative slot UB:        {conservative_slots:,}")
    print(f"coefficient rows:            {COEFFICIENT_ROWS:,}")
    print(f"candidate checks:            {CANDIDATE_CHECKS:,}")
    print("all organizer-limit arithmetic checks pass")


if __name__ == "__main__":
    main()
