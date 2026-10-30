#!/usr/bin/env python3
"""Brief 22: fast-multiplier pricing audit on leader 32b7d38.

The first table is the corrected cost of the low-level carry/mask builders.
It remains an optimistic lower bound because Brief 20 charged one pass for a
quantum-sign-selected quotient erasure.  The second table prices the direct
phase-safe recompute/uncompute fallback, including its overflow cleanup.
"""

from fractions import Fraction

from fastmul_feasibility import (
    chunk_lengths,
)

WINDOWS = 29
QUBITS = 856
BASE_T = 8_480_934_044
OLD_CALL_CCX = 1_110_533
CCX_PRICE = 4
WIDTH = 256
CONTROLLED_C_EXTRA = 12


def carry_pass_ccx(carry_lanes: int) -> int:
    """Literal circuit count: 255 sum carries plus coherent boundary replays."""
    chunks = chunk_lengths(WIDTH, carry_lanes)
    return WIDTH - 1 + sum(chunks[:-1])


def modular_signed_add_ccx(clean_lanes: int) -> int:
    # The controlled c=2^32+977 pass has six non-low set bits.  Its quadratic
    # carry uses one extra literal CCX at each such bit in both the sum and
    # boundary-clear replays.
    return 3 * carry_pass_ccx(clean_lanes - 1) + carry_pass_ccx(clean_lanes) + CONTROLLED_C_EXTRA


def modular_double_ccx(clean_lanes: int) -> int:
    return 2 * carry_pass_ccx(clean_lanes - 1) + CONTROLLED_C_EXTRA


def modular_halve_ccx(clean_lanes: int) -> int:
    return carry_pass_ccx(clean_lanes)


def forward_call_ccx(clean_lanes: int) -> int:
    return WIDTH * modular_signed_add_ccx(clean_lanes) + (WIDTH - 1) * modular_double_ccx(clean_lanes)


def inverse_call_ccx(clean_lanes: int) -> int:
    return WIDTH * modular_signed_add_ccx(clean_lanes) + (WIDTH - 1) * modular_halve_ccx(clean_lanes)


def fallback_signed_add_ccx(clean_lanes: int) -> int:
    """Direct exact sign-selected quotient cleanup.

    Three flag-live passes perform the raw sum, quotient toggle and correction.
    Four all-lane passes add sign*c to the surviving addend, compare, undo it,
    and phase-safely clean the temporary overflow.  The four controlled-c
    traversals contribute 4*6 extra quadratic carry CCXs in each of their sum
    and boundary-replay halves, i.e. 48 total.
    """
    flag = carry_pass_ccx(clean_lanes - 1)
    all_lanes = carry_pass_ccx(clean_lanes)
    return 3 * flag + 4 * all_lanes + 48


def fallback_forward_call_ccx(clean_lanes: int) -> int:
    return WIDTH * fallback_signed_add_ccx(clean_lanes) + (WIDTH - 1) * modular_double_ccx(clean_lanes)


def fallback_inverse_call_ccx(clean_lanes: int) -> int:
    return WIDTH * fallback_signed_add_ccx(clean_lanes) + (WIDTH - 1) * modular_halve_ccx(clean_lanes)


def pct(delta: int, base: int) -> str:
    return f"{float(Fraction(100 * delta, base)):+.9f}%"


def main() -> None:
    rows = []
    for name, lanes in (("ordinary", 68), ("square", 69), ("tight", 25)):
        rows.append(
            (
                name,
                lanes,
                carry_pass_ccx(lanes - 1),
                carry_pass_ccx(lanes),
                modular_signed_add_ccx(lanes),
                modular_double_ccx(lanes),
                modular_halve_ccx(lanes),
                forward_call_ccx(lanes),
                inverse_call_ccx(lanes),
            )
        )

    of = forward_call_ccx(68)
    oi = inverse_call_ccx(68)
    sf = forward_call_ccx(69)
    si = inverse_call_ccx(69)
    tf = forward_call_ccx(25)
    ti = inverse_call_ccx(25)
    new_ccx_per_window = 2 * of + oi + sf + si + 2 * tf + ti
    old_ccx_per_window = 8 * OLD_CALL_CCX
    delta_t = WINDOWS * (new_ccx_per_window - old_ccx_per_window) * CCX_PRICE
    new_t = BASE_T + delta_t
    base_score = QUBITS * BASE_T
    new_score = QUBITS * new_t

    assert base_score == 7_259_679_541_664
    assert new_ccx_per_window == 5_419_265
    assert delta_t == -401_939_884
    assert new_t == 8_078_994_160
    assert new_score == 6_915_619_000_960

    print("site,lanes,A(flag),A(all),M,D,H,forwardCCX,inverseCCX,forwardT,inverseT")
    for row in rows:
        print(",".join(map(str, row + (CCX_PRICE * row[-2], CCX_PRICE * row[-1]))))
    print(f"old CCX/window: {old_ccx_per_window}")
    print(f"new CCX/window: {new_ccx_per_window}")
    print(f"delta T: {delta_t}")
    print(f"projected: {QUBITS} x {new_t} = {new_score}")
    print(f"vs leader: {pct(new_score - base_score, base_score)}")

    fof = fallback_forward_call_ccx(68)
    foi = fallback_inverse_call_ccx(68)
    fsf = fallback_forward_call_ccx(69)
    fsi = fallback_inverse_call_ccx(69)
    ftf = fallback_forward_call_ccx(25)
    fti = fallback_inverse_call_ccx(25)
    fallback_per_window = 2 * fof + foi + fsf + fsi + 2 * ftf + fti
    fallback_delta_t = WINDOWS * (fallback_per_window - old_ccx_per_window) * CCX_PRICE
    fallback_t = BASE_T + fallback_delta_t
    fallback_score = QUBITS * fallback_t
    assert fallback_per_window == 8_356_097
    assert fallback_delta_t == -61_267_372
    assert fallback_t == 8_419_666_672
    assert fallback_score == 7_207_234_671_232
    print("\nphase-safe fallback")
    print(f"ordinary F/I: {fof}/{foi}")
    print(f"square F/I: {fsf}/{fsi}")
    print(f"tight F/I: {ftf}/{fti}")
    print(f"CCX/window: {fallback_per_window}")
    print(f"projected: {QUBITS} x {fallback_t} = {fallback_score}")
    print(f"vs leader: {pct(fallback_score - base_score, base_score)}")


if __name__ == "__main__":
    main()
