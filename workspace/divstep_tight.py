#!/usr/bin/env python3
"""Brief 27: fixed-width modular divstep cofactors and replay pricing.

The arithmetic model mirrors ``DivstepTight.lean``.  The resource table is an
explicit conservative-screen model inherited from Brief 26; it is not a
``Straight`` receipt.  In particular, it does not add a physical cost for
canonical modular halving, so its score is optimistic.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
import argparse


LEADER_Q = 856
LEADER_T = 8_480_934_044
LEADER_SCORE = 7_259_679_541_664
NON_EEA_T = 1_175_358_444
WRAPPERS = 116
LOWERED_T_PER_CCX = 4
OLD_EEA_ROLES = 580


@dataclass(frozen=True)
class State:
    delta2: int
    f: int
    g: int
    B: int
    D: int
    ticks: int


def canon(p: int, x: int) -> int:
    return x % p


def half_mod(p: int, x: int) -> int:
    return (((p + 1) // 2) * x) % p


def init(p: int, x: int) -> State:
    return State(1, p, x, 0 % p, 1 % p, 0)


def branch(s: State) -> str:
    if s.g == 0:
        return "zero"
    if s.g % 2 == 0:
        return "even"
    if s.delta2 > 0:
        return "swap"
    return "add"


def step(p: int, s: State) -> State:
    tag = branch(s)
    if tag == "zero":
        return s
    if tag == "even":
        return State(s.delta2 + 2, s.f, s.g // 2,
                     s.B, half_mod(p, s.D), s.ticks + 1)
    if tag == "swap":
        return State(2 - s.delta2, s.g, (s.g - s.f) // 2,
                     s.D, half_mod(p, s.D - s.B), s.ticks + 1)
    return State(s.delta2 + 2, s.f, (s.g + s.f) // 2,
                 s.B, half_mod(p, s.D + s.B), s.ticks + 1)


def unstep(p: int, tag: str, s: State) -> State:
    if tag == "zero":
        return s
    if tag == "even":
        return State(s.delta2 - 2, s.f, 2 * s.g,
                     s.B, canon(p, 2 * s.D), s.ticks - 1)
    if tag == "swap":
        return State(2 - s.delta2, s.f - 2 * s.g, s.f,
                     canon(p, s.B - 2 * s.D), s.B, s.ticks - 1)
    if tag == "add":
        return State(s.delta2 - 2, s.f, 2 * s.g - s.f,
                     s.B, canon(p, 2 * s.D - s.B), s.ticks - 1)
    raise ValueError(tag)


def trace(p: int, x: int, horizon: int) -> tuple[State, list[str]]:
    s = init(p, x)
    tags: list[str] = []
    for _ in range(horizon):
        tags.append(branch(s))
        s = step(p, s)
    return s, tags


def replay(p: int, s: State, tags: list[str]) -> State:
    for tag in reversed(tags):
        s = unstep(p, tag, s)
    return s


def collision_receipt() -> None:
    post = State(1, 1, 1, 1, 1, 1)
    predecessors = {
        "even": State(-1, 1, 2, 1, 2, 0),
        "swap": State(1, -1, 1, 4, 1, 0),
        "add": State(-1, 1, 1, 1, 1, 0),
    }
    assert all(branch(s) == tag for tag, s in predecessors.items())
    assert all(step(5, s) == post for s in predecessors.values())
    assert len(set(predecessors.values())) == 3


def exhaustive(n: int) -> dict[str, int]:
    rows = coprime_nonzero = max_steps = 0
    max_value = max_coeff = max_delta2 = 0
    for p in range(1, 1 << n, 2):
        for x in range(p):
            rows += 1
            s = init(p, x)
            tags: list[str] = []
            while s.g:
                assert s.f & 1
                assert 0 <= s.B < p and 0 <= s.D < p
                assert (s.f - s.B * x) % p == 0
                assert (s.g - s.D * x) % p == 0
                max_value = max(max_value, abs(s.f), abs(s.g))
                max_coeff = max(max_coeff, s.B, s.D)
                max_delta2 = max(max_delta2, abs(s.delta2))
                tag = branch(s)
                old = s
                s = step(p, s)
                assert unstep(p, tag, s) == old
                tags.append(tag)
            max_steps = max(max_steps, s.ticks)
            assert replay(p, s, tags) == init(p, x)
            assert abs(s.f) == gcd(p, x)
            if x and gcd(p, x) == 1:
                coprime_nonzero += 1
                assert ((s.B * s.f) * x) % p == 1
    return {
        "rows": rows,
        "coprime_nonzero": coprime_nonzero,
        "max_steps": max_steps,
        "max_abs_value": max_value,
        "max_unsigned_coeff": max_coeff,
        "max_abs_delta2": max_delta2,
    }


N12_RECEIPT = {
    "rows": 4_194_304,
    "coprime_nonzero": 3_398_952,
    "max_steps": 28,
    "max_abs_value": 4_095,
    # Filled by the exhaustive run; asserted in main.
    "max_unsigned_coeff": 4_094,
    "max_abs_delta2": 23,
}


def signed_width_for_abs(bound: int) -> int:
    width = 1
    while (1 << (width - 1)) - 1 < bound:
        width += 1
    return width


def tick_width(horizon: int) -> int:
    return horizon.bit_length()


def cell_ccx(value_width: int, coeff_width: int, delta_width: int) -> int:
    return 9 * value_width + 8 * coeff_width + 4 * delta_width - 13


def best_parity_checkpoint_history(horizon: int, delta_width: int) -> tuple[int, int]:
    """Abstract parity-log replay storage.

    Retain one parity bit per tick, delta checkpoints at noninitial block
    boundaries, and one reusable block of sigma bits.  This proves a storage
    tradeoff only; a physical decoder/count theorem remains absent.
    """
    return min(
        (
            horizon
            + (((horizon + block - 1) // block) - 1) * delta_width
            + block,
            block,
        )
        for block in range(1, horizon + 1)
    )


@dataclass(frozen=True)
class Projection:
    n: int
    horizon: int
    history_mode: str

    @property
    def value_width(self) -> int:
        return self.n + 1

    @property
    def coeff_width(self) -> int:
        return self.n

    @property
    def delta_width(self) -> int:
        return signed_width_for_abs(2 * self.horizon + 1)

    @property
    def cell_ccx(self) -> int:
        return cell_ccx(self.value_width, self.coeff_width, self.delta_width)

    @property
    def clean_wrapper_ccx(self) -> int:
        return 2 * self.horizon * self.cell_ccx

    @property
    def state_lanes(self) -> int:
        return (
            2 * self.value_width
            + 2 * self.coeff_width
            + self.delta_width
            + tick_width(self.horizon)
        )

    @property
    def history_lanes(self) -> int:
        if self.history_mode == "two-bit-local":
            return 2 * self.horizon
        if self.history_mode == "parity-checkpoint":
            return best_parity_checkpoint_history(
                self.horizon, self.delta_width
            )[0]
        if self.history_mode == "impossible-tag-free-sensitivity":
            return 0
        raise ValueError(self.history_mode)

    @property
    def scratch_lanes(self) -> int:
        return max(self.value_width + 1, self.coeff_width + 1,
                   self.delta_width - 1)

    @property
    def support(self) -> int:
        return self.state_lanes + self.coeff_width + self.history_lanes + self.scratch_lanes

    @property
    def projected_q(self) -> int:
        return LEADER_Q - OLD_EEA_ROLES + self.support

    @property
    def total_t(self) -> int:
        return NON_EEA_T + WRAPPERS * LOWERED_T_PER_CCX * self.clean_wrapper_ccx

    @property
    def score(self) -> int:
        return self.projected_q * self.total_t


def pct(score: int) -> str:
    return f"{100 * (score - LEADER_SCORE) / LEADER_SCORE:+.9f}%"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exhaustive-n12", action="store_true")
    args = parser.parse_args()

    collision_receipt()
    n8 = exhaustive(8)
    assert n8["rows"] == 16_384 and n8["max_steps"] == 19
    print("n=8 exhaustive modular-cofactor receipt")
    for key, value in n8.items():
        print(f"  {key:22s} {value:,}")

    if args.exhaustive_n12:
        n12 = exhaustive(12)
        print("n=12 exhaustive modular-cofactor receipt (recomputed)")
    else:
        n12 = N12_RECEIPT
        print("n=12 receipt (use --exhaustive-n12 to recompute)")
    assert n12 == N12_RECEIPT
    for key, value in n12.items():
        print(f"  {key:22s} {value:,}")

    print("three-way collision: even/swap/add -> one post-state (local tag-free inverse impossible)")
    print("fixed n=256 registers: f=257s, g=257s, B=256u, D=256u, delta=12s, ticks=10u")
    print("pricing is optimistic: fixed-width Brief-26 skeleton, no physical modular-half surcharge")
    print("N | history | history lanes | block | CCX/cell | CCX/clean wrapper | Q | T | QxT | vs leader")
    for horizon in (590, 724, 742):
        hist, block = best_parity_checkpoint_history(horizon, 12)
        for mode in (
            "two-bit-local",
            "parity-checkpoint",
            "impossible-tag-free-sensitivity",
        ):
            p = Projection(256, horizon, mode)
            block_text = str(block) if mode == "parity-checkpoint" else "-"
            print(
                f"{horizon} | {mode} | {p.history_lanes:,} | {block_text} | "
                f"{p.cell_ccx:,} | {p.clean_wrapper_ccx:,} | {p.projected_q:,} | "
                f"{p.total_t:,} | {p.score:,} | {pct(p.score)}"
            )


if __name__ == "__main__":
    main()
