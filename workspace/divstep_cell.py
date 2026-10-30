#!/usr/bin/env python3
"""Exact arithmetic for Brief 26's proved replay model and extrapolated circuit.

The recurrence, branch replay, and conservative lane inequalities mirror
``DivstepCellReplay.lean``.  Circuit/resource rows are intentionally labelled
``extrapolated``: the Lean work does not yet contain the corresponding
``Straight`` constructor or its coherence theorem.
"""

from dataclasses import dataclass
from math import gcd


LEADER_Q = 856
LEADER_T = 8_480_934_044
LEADER_SCORE = LEADER_Q * LEADER_T
NON_EEA_T = 1_175_358_444
WRAPPERS = 116
LOWERED_T_PER_CCX = 4
OLD_EEA_ROLES = 580


@dataclass(frozen=True)
class Core:
    delta2: int
    f: int
    g: int
    b: int
    d: int
    ticks: int


def init(f: int, g: int) -> Core:
    return Core(1, f, g, 0, 1, 0)


def branch(s: Core) -> str:
    if s.g == 0:
        return "zero"
    if s.g % 2 == 0:
        return "even"
    if s.delta2 > 0:
        return "swap"
    return "add"


def step(s: Core) -> Core:
    tag = branch(s)
    if tag == "zero":
        return s
    if tag == "even":
        return Core(s.delta2 + 2, s.f, s.g // 2,
                    2 * s.b, s.d, s.ticks + 1)
    if tag == "swap":
        return Core(2 - s.delta2, s.g, (s.g - s.f) // 2,
                    2 * s.d, s.d - s.b, s.ticks + 1)
    return Core(s.delta2 + 2, s.f, (s.g + s.f) // 2,
                2 * s.b, s.d + s.b, s.ticks + 1)


def unstep(tag: str, s: Core) -> Core:
    if tag == "zero":
        return s
    if tag == "even":
        return Core(s.delta2 - 2, s.f, 2 * s.g,
                    s.b // 2, s.d, s.ticks - 1)
    if tag == "swap":
        return Core(2 - s.delta2, s.f - 2 * s.g, s.f,
                    s.b // 2 - s.d, s.b // 2, s.ticks - 1)
    if tag == "add":
        return Core(s.delta2 - 2, s.f, 2 * s.g - s.f,
                    s.b // 2, s.d - s.b // 2, s.ticks - 1)
    raise ValueError(tag)


def trace(f: int, g: int, horizon: int) -> tuple[Core, list[str]]:
    s = init(f, g)
    tags: list[str] = []
    for _ in range(horizon):
        tags.append(branch(s))
        s = step(s)
    return s, tags


def replay(s: Core, tags: list[str]) -> Core:
    for tag in reversed(tags):
        s = unstep(tag, s)
    return s


def signed_width_for_abs(bound: int) -> int:
    """Bits for every integer in [-bound,bound]."""
    assert bound >= 0
    width = 1
    while (1 << (width - 1)) - 1 < bound:
        width += 1
    return width


def value_width(n: int) -> int:
    # Values remain in [-(2^n-1), 2^n-1].
    return n + 1


def coeff_width(step_index: int) -> int:
    # Lean proves |b|,|d| <= 2^ticks and ticks <= step_index.
    return step_index + 2


def delta_width(step_index: int) -> int:
    # Lean proves |delta2| <= 2*ticks+1.
    return signed_width_for_abs(2 * step_index + 1)


def raw_cell_ccx(v: int, c: int, h: int) -> int:
    """Conservative literal skeleton target, matching Lean ``cellCCX``."""
    return 9 * v + 8 * c + 4 * h - 13


def mbu_cell_ccx(v: int, c: int, h: int) -> int:
    """Conditional MBU target if every listed carry/path erase is proved.

    This is not an achieved count.  It replaces v-chain and ripple reverse
    sweeps by X-measure/reset plus Clifford phase repair.
    """
    return 6 * v + 6 * c + 2 * h - 6


@dataclass(frozen=True)
class Projection:
    n: int
    horizon: int
    mbu: bool = False

    @property
    def v(self) -> int:
        return value_width(self.n)

    @property
    def c(self) -> int:
        return coeff_width(self.horizon)

    @property
    def h(self) -> int:
        return delta_width(self.horizon)

    @property
    def per_cell_ccx(self) -> int:
        fn = mbu_cell_ccx if self.mbu else raw_cell_ccx
        return fn(self.v, self.c, self.h)

    @property
    def forward_ccx(self) -> int:
        return self.horizon * self.per_cell_ccx

    @property
    def clean_wrapper_ccx(self) -> int:
        # Compute, Clifford-copy the terminal scaled coefficient, replay.
        return 2 * self.forward_ccx

    @property
    def support(self) -> int:
        registers = self.h + 2 * self.v + 2 * self.c
        output = self.c
        # The literal skeleton exposes active/e/sigma.  A proved two-bit branch
        # encoder would save one history wire per cell but is not counted here.
        history = 3 * self.horizon
        scratch = max(self.v + 1, self.c + 1, self.h - 1)
        return registers + output + history + scratch

    @property
    def projected_q(self) -> int:
        # Layout screen only: replace the leader's 580 EEA roles by standalone
        # support.  Sharing with the passenger/address bank is not proved.
        return LEADER_Q - OLD_EEA_ROLES + self.support

    @property
    def total_t(self) -> int:
        return NON_EEA_T + WRAPPERS * LOWERED_T_PER_CCX * self.clean_wrapper_ccx

    @property
    def score(self) -> int:
        return self.projected_q * self.total_t


def exhaustive_small(n: int) -> dict[str, int]:
    """Regression for every admissible unsigned pair; intended for n<=8."""
    rows = coprime = max_steps = 0
    max_value = max_coeff = max_delta = 0
    for f in range(1, 1 << n, 2):
        for g in range(f):
            rows += 1
            s = init(f, g)
            tags: list[str] = []
            while s.g:
                max_value = max(max_value, abs(s.f), abs(s.g))
                max_coeff = max(max_coeff, abs(s.b), abs(s.d))
                max_delta = max(max_delta, abs(s.delta2))
                tags.append(branch(s))
                old = s
                s = step(s)
                assert unstep(tags[-1], s) == old
            max_steps = max(max_steps, s.ticks)
            assert replay(s, tags) == init(f, g)
            assert abs(s.f) == gcd(f, g)
            if g and gcd(f, g) == 1:
                coprime += 1
                # Same scaled-coefficient decoder as DivstepMath.
                assert (s.b * s.f * pow(pow(2, s.ticks, f), -1, f)) % f == pow(g, -1, f)
    return {
        "rows": rows,
        "coprime_nonzero": coprime,
        "max_steps": max_steps,
        "max_abs_value": max_value,
        "max_abs_coeff": max_coeff,
        "max_abs_delta2": max_delta,
    }


def pct(score: int) -> str:
    return f"{100 * (score - LEADER_SCORE) / LEADER_SCORE:+.9f}%"


def main() -> None:
    small = exhaustive_small(8)
    assert small["rows"] == 16_384
    assert small["max_steps"] == 19
    print("proved-model n=8 exhaustive regression")
    for key, value in small.items():
        print(f"  {key:20s} {value:,}")
    print("structural envelope (Lean theorem; applies to all n=8 and n=12 inputs)")
    for n, horizon in ((8, 19), (12, 31)):
        print(
            f"  n={n}: V={value_width(n)}, C_t=t+2 (C_N={coeff_width(horizon)}), "
            f"H_N={delta_width(horizon)} at illustrative N={horizon}"
        )
    print("extrapolated conservative Bennett projections (not Straight receipts)")
    print("N | mode | V/C/H | CCX/cell | CCX/clean wrapper | support | Q screen | T screen | QxT | vs leader")
    for horizon in (590, 724, 742):
        for mbu in (False, True):
            p = Projection(256, horizon, mbu)
            mode = "raw" if not mbu else "MBU-unproved"
            print(
                f"{horizon} | {mode} | {p.v}/{p.c}/{p.h} | {p.per_cell_ccx:,} | "
                f"{p.clean_wrapper_ccx:,} | {p.support:,} | {p.projected_q:,} | "
                f"{p.total_t:,} | {p.score:,} | {pct(p.score)}"
            )


if __name__ == "__main__":
    main()
