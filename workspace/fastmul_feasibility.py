#!/usr/bin/env python3
"""Exact integer accounting for Brief 20's conservative exact multiplier.

This is a construction-level count, not an Entrant certificate.  Every row is
an exact consequence of the pass decomposition documented in
docs/FAST-MUL-FEASIBILITY.md:

* logical-AND compute: one CCX, erased by measurement for zero CCX;
* a held chunk-boundary carry: X-measured, then its exact phase comparator is
  charged on the worst branch;
* patch 10 lowers every literal CCX to five T.
"""

from dataclasses import dataclass
from fractions import Fraction

N = 256
WINDOWS = 30
BASE_QUBITS = 856
BASE_T = 11_513_899_424
BASE_SCORE = BASE_QUBITS * BASE_T
LEADER_SCORE = 9_857_180_674_304

OLD_CALL_CCX = 1_110_533
OLD_CALLS_PER_WINDOW = 8
OLD_BUCKET_T = WINDOWS * OLD_CALLS_PER_WINDOW * OLD_CALL_CCX * 5


def chunk_lengths(width: int, carry_lanes: int) -> tuple[int, ...]:
    """Donor-style fewest-chunk schedule, made worst-branch exact.

    Before the final chunk, chunk j can use at most P-j-1 word lanes: j
    earlier boundary carries remain live and one lane owns this boundary.
    The final chunk can use P-(nchunks-1).  The final chunk is maximal, which
    minimizes the prefixes whose boundary phase comparators must be paid.
    """
    assert width > 0 and carry_lanes > 0
    nchunks = 1
    while True:
        capacity = sum(carry_lanes - j - 1 for j in range(nchunks - 1))
        capacity += carry_lanes - (nchunks - 1)
        if capacity >= width:
            break
        nchunks += 1
        if nchunks > carry_lanes:
            raise ValueError(
                f"{carry_lanes} carry lanes cannot cover width {width}"
            )

    final = min(carry_lanes - (nchunks - 1), width)
    remaining = width - final
    lengths: list[int] = []
    for j in range(nchunks - 1):
        length = min(remaining, carry_lanes - j - 1)
        assert length > 0
        lengths.append(length)
        remaining -= length
    assert remaining == 0
    lengths.append(final)
    assert sum(lengths) == width
    return tuple(lengths)


def carry_pass_ccx(carry_lanes: int) -> int:
    """One exact 256-bit chunked carry/add/phase pass.

    There are 256 forward temporary-AND computations.  Ordinary carry erases
    cost zero.  Each non-final chunk boundary needs a phase-only recomputation
    over that chunk, so the worst branch adds the non-final prefix lengths.
    """
    chunks = chunk_lengths(N, carry_lanes)
    return N + sum(chunks[:-1])


def modular_signed_add_ccx(clean_lanes: int) -> int:
    """Raw add, near-p flag, ctl*c correction, final flag phase oracle."""
    # The quotient flag occupies one lane for the first three passes.  Once it
    # is measured/reset, all clean lanes are available to its phase comparator.
    return 3 * carry_pass_ccx(clean_lanes - 1) + carry_pass_ccx(clean_lanes)


def modular_double_ccx(clean_lanes: int) -> int:
    """Threshold flag plus ctl*c; the output LSB clears the flag by CNOT."""
    return 2 * carry_pass_ccx(clean_lanes - 1)


def modular_halve_ccx(clean_lanes: int) -> int:
    """Input parity controls the exact p/c correction; no quotient flag."""
    return carry_pass_ccx(clean_lanes)


def forward_call_ccx(clean_lanes: int) -> int:
    """255 signed-add/double cells and one terminal signed add."""
    add = modular_signed_add_ccx(clean_lanes)
    return 255 * (add + modular_double_ccx(clean_lanes)) + add


def inverse_call_ccx(clean_lanes: int) -> int:
    """Terminal inverse add and 255 signed-add/halve cells."""
    add = modular_signed_add_ccx(clean_lanes)
    return add + 255 * (add + modular_halve_ccx(clean_lanes))


@dataclass(frozen=True)
class Projection:
    extra_wires: int
    qubits: int
    ordinary_forward: int
    ordinary_inverse: int
    square_forward: int
    square_inverse: int
    tight_forward: int
    tight_inverse: int
    ccx_per_window: int
    t_model: int
    score: int

    @property
    def delta_t(self) -> int:
        return self.t_model - BASE_T

    @property
    def delta_score(self) -> int:
        return self.score - BASE_SCORE

    @property
    def delta_leader(self) -> int:
        return self.score - LEADER_SCORE


def projection(extra_wires: int) -> Projection:
    assert 0 <= extra_wires <= 64
    ordinary = 68 + extra_wires
    square = 69 + extra_wires
    tight = 25 + extra_wires

    of = forward_call_ccx(ordinary)
    oi = inverse_call_ccx(ordinary)
    sf = forward_call_ccx(square)
    si = inverse_call_ccx(square)
    tf = forward_call_ccx(tight)
    ti = inverse_call_ccx(tight)

    # Per window: ordinary sites are 2 forward + 1 inverse; square is one of
    # each; post-EEA tight sites are 2 forward + 1 inverse.
    per_window = 2 * of + oi + sf + si + 2 * tf + ti
    new_bucket_t = WINDOWS * per_window * 5
    t_model = BASE_T - OLD_BUCKET_T + new_bucket_t
    qubits = BASE_QUBITS + extra_wires
    return Projection(
        extra_wires, qubits, of, oi, sf, si, tf, ti,
        per_window, t_model, qubits * t_model,
    )


def pct(delta: int, base: int) -> str:
    return f"{float(Fraction(100 * delta, base)):+.6f}%"


def validate() -> None:
    assert BASE_SCORE == 9_855_897_906_944
    assert OLD_BUCKET_T == 1_332_639_600
    # Twenty-three lanes have triangular capacity 253; twenty-four are the
    # first feasible pool and yield the displayed tight-site schedule.
    try:
        chunk_lengths(256, 23)
    except ValueError:
        pass
    else:
        raise AssertionError("23 lanes must be infeasible")
    assert chunk_lengths(256, 24) == (
        23, 22, 21, 20, 19, 18, 17, 16, 15,
        14, 13, 12, 11, 10, 9, 8, 8,
    )
    assert carry_pass_ccx(24) == 504
    assert carry_pass_ccx(67) == 448
    assert carry_pass_ccx(68) == 447

    p0 = projection(0)
    assert p0.ccx_per_window == 5_390_896
    assert p0.t_model == 10_989_894_224
    assert p0.score == 9_407_349_455_744
    assert min((projection(w) for w in range(65)), key=lambda p: p.score) == p0


def main() -> None:
    validate()
    p0 = projection(0)
    print("exact site counts at w=0 (CCX/call)")
    print(
        "site       clean  A(flag) A(all) modadd double halve "
        "forward inverse"
    )
    for name, lanes in (("ordinary", 68), ("square", 69), ("tight", 25)):
        print(
            f"{name:10} {lanes:5d} {carry_pass_ccx(lanes-1):7d} "
            f"{carry_pass_ccx(lanes):6d} "
            f"{modular_signed_add_ccx(lanes):6d} "
            f"{modular_double_ccx(lanes):6d} "
            f"{modular_halve_ccx(lanes):5d} "
            f"{forward_call_ccx(lanes):7d} {inverse_call_ccx(lanes):7d}"
        )
    print()
    print(
        "w,Q,ordinaryForwardCCX,ordinaryInverseCCX,"
        "squareForwardCCX,squareInverseCCX,tightForwardCCX,tightInverseCCX,"
        "CCXPerWindow,T,score,deltaT,deltaScore,pctVsPatch10,"
        "deltaLeader,pctVsLeader"
    )
    for w in range(65):
        p = projection(w)
        print(
            f"{w},{p.qubits},{p.ordinary_forward},{p.ordinary_inverse},"
            f"{p.square_forward},{p.square_inverse},"
            f"{p.tight_forward},{p.tight_inverse},{p.ccx_per_window},"
            f"{p.t_model},{p.score},{p.delta_t},"
            f"{p.delta_score},{pct(p.delta_score, BASE_SCORE)},"
            f"{p.delta_leader},{pct(p.delta_leader, LEADER_SCORE)}"
        )
    print()
    print(
        f"best: w={p0.extra_wires}, Q={p0.qubits}, T={p0.t_model}, "
        f"score={p0.score}, vs patch10={pct(p0.delta_score, BASE_SCORE)}, "
        f"vs leader={pct(p0.delta_leader, LEADER_SCORE)}"
    )


if __name__ == "__main__":
    main()
