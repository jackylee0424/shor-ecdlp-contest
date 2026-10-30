#!/usr/bin/env python3
"""Exact arithmetic and exhaustive n=8 data for Brief 24.

This calculator separates kernel-backed/exhaustive small-instance facts from
the still-conditional 256-bit circuit projection.  It does not enumerate
256-bit inputs.
"""

from dataclasses import dataclass
from math import gcd


N_SMALL = 8
HORIZON = 590
SECP_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
HULL_590_LIMIT = 0x101C840FAED222B9EF3BFE933011B277F84EE3D3F6DC8B496D8CD75B8315AFEC2

LEADER_Q = 856
LEADER_T = 8_480_934_044
LEADER_SCORE = LEADER_Q * LEADER_T
WINDOWS = 29
WRAPPERS = 4 * WINDOWS
NON_EEA_T = 1_175_358_444
LOWERED_T_PER_CCX = 4


@dataclass(frozen=True)
class State:
    delta2: int  # twice Bernstein--Yang delta; starts at 1
    f: int
    g: int
    # 2^ticks [f;g] = [[a,b],[c,d]] [f0;g0]
    a: int
    b: int
    c: int
    d: int
    ticks: int


def init(f: int, g: int) -> State:
    return State(1, f, g, 1, 0, 0, 1, 0)


def step(s: State) -> State:
    """Selected hddivstep recurrence, with absorbing g=0 padding."""
    if s.g == 0:
        return s
    if s.g % 2 == 0:
        return State(s.delta2 + 2, s.f, s.g // 2,
                     2 * s.a, 2 * s.b, s.c, s.d, s.ticks + 1)
    if s.delta2 > 0:
        return State(2 - s.delta2, s.g, (s.g - s.f) // 2,
                     2 * s.c, 2 * s.d, s.c - s.a, s.d - s.b, s.ticks + 1)
    return State(s.delta2 + 2, s.f, (s.g + s.f) // 2,
                 2 * s.a, 2 * s.b, s.c + s.a, s.d + s.b, s.ticks + 1)


def walk(f: int, g: int, horizon: int = HORIZON) -> State:
    s = init(f, g)
    for _ in range(horizon):
        s = step(s)
    return s


def stopping_time(f: int, g: int) -> int:
    s = init(f, g)
    while s.g:
        s = step(s)
    return s.ticks


def signed_width(x: int) -> int:
    """Smallest two's-complement width containing x."""
    width = 1
    while not (-(1 << (width - 1)) <= x < (1 << (width - 1))):
        width += 1
    return width


def small_audit() -> dict[str, int]:
    max_steps = 0
    max_abs_value = 0
    max_abs_matrix = 0
    total_output_ones = 0
    valid_rows = 0
    coprime_rows = 0
    worst_f = worst_g = 0
    for f in range(1, 1 << N_SMALL, 2):
        for g in range(f):
            valid_rows += 1
            s = init(f, g)
            while s.g:
                max_abs_value = max(max_abs_value, abs(s.f), abs(s.g))
                max_abs_matrix = max(max_abs_matrix, abs(s.a), abs(s.b), abs(s.c), abs(s.d))
                s = step(s)
            max_abs_value = max(max_abs_value, abs(s.f), abs(s.g))
            max_abs_matrix = max(max_abs_matrix, abs(s.a), abs(s.b), abs(s.c), abs(s.d))
            if s.ticks > max_steps:
                max_steps, worst_f, worst_g = s.ticks, f, g
            assert s.g == 0
            assert abs(s.f) == gcd(f, g)
            assert (1 << s.ticks) * s.f == s.a * f + s.b * g
            assert (1 << s.ticks) * s.g == s.c * f + s.d * g
            if g and gcd(f, g) == 1:
                coprime_rows += 1
                inv = pow(g, -1, f) if f != 1 else 0
                decoded = (s.b * s.f * pow(pow(2, s.ticks, f), -1, f)) % f
                assert decoded == inv
            # Output fields for the exact n=8 truth-table oracle: terminal
            # signed f (9 bits), scaled transition coefficient b (12 bits),
            # and the absorbing walk's actual tick count (5 bits).
            total_output_ones += (s.f % (1 << 9)).bit_count()
            total_output_ones += (s.b % (1 << 12)).bit_count()
            total_output_ones += s.ticks.bit_count()
    return {
        "valid_rows": valid_rows,
        "coprime_rows": coprime_rows,
        "max_steps": max_steps,
        "worst_f": worst_f,
        "worst_g": worst_g,
        "max_abs_value": max_abs_value,
        "value_signed_width": signed_width(max_abs_value),
        "max_abs_matrix": max_abs_matrix,
        "matrix_signed_width": signed_width(max_abs_matrix),
        "oracle_output_ones": total_output_ones,
    }


def oracle_receipt(stats: dict[str, int]) -> dict[str, int]:
    """Receipt for a 16-control clean-v-chain n=8 truth-table oracle.

    Each admissible row computes its equality flag once, fans that flag out to
    all asserted output bits with Clifford CNOTs, and uncomputes the equality.
    Each equality v-chain uses 29 CCX; fourteen clean path wires and the flag
    are restored.  This is an exact but exponential small-instance witness,
    not the scalable divstep cell requested for n=256.
    """
    controls = 2 * N_SMALL
    scratch = controls - 2
    ccx_per_asserted_bit = 2 * scratch + 1
    forward_ccx = 2 * ccx_per_asserted_bit * stats["valid_rows"]
    # 16 input + (9 f + 12 b + 5 ticks) output + flag + 14 path wires.
    support = controls + 26 + 1 + scratch
    return {
        "controls": controls,
        "scratch": scratch,
        "ccx_per_equality": ccx_per_asserted_bit,
        "forward_ccx": forward_ccx,
        "forward_reverse_ccx": 2 * forward_ccx,
        "support": support,
    }


def projection(ticks: int, width: int = 340, h_bits: int = 11, qubits: int = 952) -> dict[str, int]:
    ccx_per_tick = 2 * width + 2 * h_bits + 1
    wrapper_ccx = ticks * ccx_per_tick
    total_t = NON_EEA_T + WRAPPERS * LOWERED_T_PER_CCX * wrapper_ccx
    return {
        "ticks": ticks,
        "ccx_per_tick": ccx_per_tick,
        "wrapper_ccx": wrapper_ccx,
        "total_t": total_t,
        "qubits": qubits,
        "score": qubits * total_t,
    }


def pct(score: int) -> str:
    return f"{100 * (score - LEADER_SCORE) / LEADER_SCORE:+.9f}%"


def main() -> None:
    assert SECP_P < HULL_590_LIMIT
    stats = small_audit()
    receipt = oracle_receipt(stats)
    print("external hull threshold")
    print(f"  590-step M limit = {HULL_590_LIMIT}")
    print(f"  secp256k1 p      = {SECP_P}")
    print(f"  margin           = {HULL_590_LIMIT - SECP_P}")
    print("n=8 exhaustive model")
    for key, value in stats.items():
        print(f"  {key:24s} {value}")
    print("n=8 truth-table oracle receipt (exact, exponential, not scalable)")
    for key, value in receipt.items():
        print(f"  {key:24s} {value}")
    print("conditional 256-bit packed screens")
    for ticks in (590, 724, 742):
        p = projection(ticks)
        print(
            f"  {ticks}: {p['wrapper_ccx']:,} CCX/wrapper; "
            f"Q={p['qubits']:,}; T={p['total_t']:,}; "
            f"QxT={p['score']:,}; {pct(p['score'])}"
        )


if __name__ == "__main__":
    main()
