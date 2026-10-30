#!/usr/bin/env python3
"""Exact integer accounting for Brief 21's downward-qubit frontier.

This calculator deliberately distinguishes certified/source-backed points from
conditional budgets.  It does not assign a T count to an unported ecdsa.fail
algorithm.
"""

from dataclasses import dataclass


LEADER_Q = 855
LEADER_T = 11_512_613_384
PARENT_Q = 854
PARENT_T = 15_258_353_144
COMPILER_ADDED_LOWER = 1_872_869_880
COMPILER_SAVING_LOWER = 2 * COMPILER_ADDED_LOWER
CCX_T = 5


@dataclass(frozen=True)
class Group:
    name: str
    wires: frozenset[int]


def span(start: int, count: int) -> frozenset[int]:
    return frozenset(range(start, start + count))


def comma(n: int) -> str:
    return f"{n:,}"


LEADER_SCORE = LEADER_Q * LEADER_T

# Physical groups at the EEA peak.  These are disjoint owners at that instant.
EEA_PEAK = (
    Group("EEA phase/iteration/sign", span(0, 4)),
    Group("EEA work1", span(4, 259)),
    Group("EEA work2", span(263, 259)),
    Group("EEA length registers", span(522, 36)),
    Group("EEA aux/rotation/control", span(558, 22)),
    Group("live data / accumulator-y bank", span(580, 256)),
    Group("borrowed arithmetic flag / lookup root", frozenset({836})),
    Group("accumulator infinity", frozenset({838})),
    Group("relocated address/sign bank", span(855, 16)),
    Group("temporary-AND compiler ancilla", frozenset({1024})),
)


def validate_census() -> None:
    union: set[int] = set()
    for group in EEA_PEAK:
        overlap = union.intersection(group.wires)
        assert not overlap, (group.name, sorted(overlap))
        union.update(group.wires)
    assert len(union) == 855
    parent = set(range(837)) | {838} | set(range(855, 871))
    assert len(parent) == 854
    assert union == parent | {1024}

    accumulator = span(263, 256) | span(580, 256) | {838}
    assert len(accumulator) == 513
    assert len(span(519, 15)) == 15
    assert len(span(855, 15) | {870}) == 16


def strict_t_ceiling(q: int) -> int:
    """Largest integer T for which q*T is strictly below the leader score."""
    return (LEADER_SCORE - 1) // q


def print_frontier() -> None:
    print("q | strict T ceiling | total added-T budget | constant-T score | status")
    print("---:|---:|---:|---:|:---")
    for q in range(LEADER_Q, 799, -1):
        ceiling = strict_t_ceiling(q)
        budget = ceiling - LEADER_T
        constant_score = q * LEADER_T
        if q == LEADER_Q:
            status = "leader (certified)"
        elif q == PARENT_Q:
            status = f"only source-backed build: T={comma(PARENT_T)}"
        else:
            status = "no exact construction established"
        print(
            f"{q} | {comma(ceiling)} | {comma(budget)} | "
            f"{comma(constant_score)} | {status}"
        )


def main() -> None:
    validate_census()
    parent_score = PARENT_Q * PARENT_T
    parent_delta = parent_score - LEADER_SCORE
    parent_pct = 100 * parent_delta / LEADER_SCORE
    q854_budget = strict_t_ceiling(PARENT_Q) - LEADER_T

    assert LEADER_SCORE == 9_843_284_443_320
    assert PARENT_T - COMPILER_SAVING_LOWER == LEADER_T
    assert PARENT_Q * strict_t_ceiling(PARENT_Q) < LEADER_SCORE
    assert PARENT_Q * (strict_t_ceiling(PARENT_Q) + 1) >= LEADER_SCORE

    print(f"leader score: {comma(LEADER_SCORE)}")
    print(f"parent score: {comma(parent_score)}")
    print(f"parent delta: +{comma(parent_delta)} ({parent_pct:.9f}%)")
    print(f"compiler saving lower bound: {comma(COMPILER_SAVING_LOWER)} T")
    print(f"Q=854 strict added-T budget: {comma(q854_budget)}")
    print(
        "Q=854 max 5T-CCX premium: "
        f"{comma(q854_budget // CCX_T)} CCX, with {q854_budget % CCX_T} T slack"
    )
    print()
    print_frontier()


if __name__ == "__main__":
    main()
