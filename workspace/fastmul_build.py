#!/usr/bin/env python3
"""Brief 22: exact fast-multiplier pricing on leader 32b7d38.

The circuit decomposition and chunk schedules come from Brief 20.  This file
changes only the integration constants: the current leader has 29 corrected
windows and its two compiler layers price every eligible unconditional source
CCX as four literal P rotations.
"""

from fractions import Fraction

from fastmul_feasibility import (
    carry_pass_ccx,
    forward_call_ccx,
    inverse_call_ccx,
    modular_double_ccx,
    modular_halve_ccx,
    modular_signed_add_ccx,
)

WINDOWS = 29
QUBITS = 856
BASE_T = 8_480_934_044
OLD_CALL_CCX = 1_110_533
CCX_PRICE = 4


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
    assert new_ccx_per_window == 5_390_896
    assert delta_t == -405_230_688
    assert new_t == 8_075_703_356
    assert new_score == 6_912_802_072_736

    print("site,lanes,A(flag),A(all),M,D,H,forwardCCX,inverseCCX,forwardT,inverseT")
    for row in rows:
        print(",".join(map(str, row + (CCX_PRICE * row[-2], CCX_PRICE * row[-1]))))
    print(f"old CCX/window: {old_ccx_per_window}")
    print(f"new CCX/window: {new_ccx_per_window}")
    print(f"delta T: {delta_t}")
    print(f"projected: {QUBITS} x {new_t} = {new_score}")
    print(f"vs leader: {pct(new_score - base_score, base_score)}")


if __name__ == "__main__":
    main()
