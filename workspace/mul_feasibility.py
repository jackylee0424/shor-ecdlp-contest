#!/usr/bin/env python3
"""Exact integer arithmetic for Brief 13's feasibility gate and projections."""

from dataclasses import dataclass
from decimal import Decimal, getcontext

getcontext().prec = 40

QUBITS = 855
ROUNDS = 6
WINDOWS_PER_ROUND = 28
CALLS_PER_WINDOW = 8  # six Horner multiply/unmultiply plus two square calls
OLD_CALL_CCX = 1_110_533
LEADER_T = 86_239_836_030
LEADER_SCORE = QUBITS * LEADER_T
SUBMISSION_THRESHOLD = 66_361_553_825_085  # strict

BOUNDARY_POOL = tuple(range(0, 7)) + tuple(range(519, 580))
POST_EEA_POOL = tuple(range(4, 7)) + tuple(range(558, 580))
SQUARE_POOL = BOUNDARY_POOL + (837,)


@dataclass(frozen=True)
class Site:
    name: str
    source_order: str
    pool: tuple[int, ...]
    proof_anchor: str


SITES = (
    Site("division multiply-to-work", "forward EEA -> multiplyWork", POST_EEA_POOL,
         "secp256k1EEAOutputIdealState_correct"),
    Site("division recompute", "reverse EEA -> multiplyData", BOUNDARY_POOL,
         "fig15DivisionRestoredState_eq + Secp256k1InPlaceInputValid"),
    Site("division unrecompute", "Z correction -> unmultiplyData", BOUNDARY_POOL,
         "fig15DataProductState_correct frame"),
    Site("multiplication multiply-to-work", "multiplyWork -> reset", BOUNDARY_POOL,
         "Secp256k1InPlaceInputValid"),
    Site("multiplication recompute", "forward EEA in data bank -> multiplyData", POST_EEA_POOL,
         "relabel of secp256k1EEAOutputIdealState_correct"),
    Site("multiplication unrecompute", "Z correction -> unmultiplyData", POST_EEA_POOL,
         "fig15DataProductState_correct frame"),
    Site("square compute", "squareLoop -> subtract", SQUARE_POOL,
         "Secp256k1ZeroAllowedInputValid"),
    Site("square uncompute", "subtract -> squareLoopInverse", SQUARE_POOL,
         "squareSubtract_correct frame"),
)


def projected(per_bit_ccx: int, fixed_ccx_per_call: int = 0, qubits: int = QUBITS) -> tuple[int, int]:
    old_call_t = CALLS_PER_WINDOW * OLD_CALL_CCX * 7 * WINDOWS_PER_ROUND * ROUNDS
    new_call_ccx = 256 * per_bit_ccx + fixed_ccx_per_call
    new_call_t = CALLS_PER_WINDOW * new_call_ccx * 7 * WINDOWS_PER_ROUND * ROUNDS
    t_model = LEADER_T - old_call_t + new_call_t
    return t_model, qubits * t_model


def pct_cut(score: int) -> Decimal:
    return Decimal(100) * Decimal(LEADER_SCORE - score) / Decimal(LEADER_SCORE)


def main() -> None:
    assert LEADER_SCORE == 73_735_059_805_650
    assert len(set(BOUNDARY_POOL)) == len(BOUNDARY_POOL) == 68
    assert len(set(POST_EEA_POOL)) == len(POST_EEA_POOL) == 25
    assert len(set(SQUARE_POOL)) == len(SQUARE_POOL) == 69

    for site in SITES:
        print(f"{site.name}: {len(site.pool)} clean lanes; {site.pool}; {site.proof_anchor}")

    old_call_t = CALLS_PER_WINDOW * OLD_CALL_CCX * 7 * WINDOWS_PER_ROUND * ROUNDS
    print(f"old eight-call contribution over certificate: {old_call_t:,} T")
    print(f"T with all eight calls free: {LEADER_T - old_call_t:,}")

    for per_bit in (600, 757, 758, 800, 1000):
        t_model, score = projected(per_bit)
        print(
            f"conditional {per_bit} CCX/bit, zero fixed overhead: "
            f"T={t_model:,}; QxT={score:,}; cut={pct_cut(score):.9f}%; "
            f"threshold margin={SUBMISSION_THRESHOLD - score:,}"
        )

    # The post-EEA shortfall is 45 lanes against the brief's 70-lane design gate.
    extra_qubits = 70 - len(POST_EEA_POOL)
    fallback_qubits = QUBITS + extra_qubits
    free_t = LEADER_T - old_call_t
    free_score = fallback_qubits * free_t
    print(
        f"add-{extra_qubits}-lane fallback: {fallback_qubits} qubits; even zero-T calls give "
        f"QxT={free_score:,}; cut={pct_cut(free_score):.9f}%; "
        f"threshold margin={SUBMISSION_THRESHOLD - free_score:,}"
    )


if __name__ == "__main__":
    main()
