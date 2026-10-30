#!/usr/bin/env python3
"""Exact arithmetic projection for Brief 30's WEX-portable trim census.

This is a source-audit projection, not a certificate.  The portable delta keeps
the U/H mechanisms in c3f340a..0b650bb and removes the six effects whose final
implementation specializes topology, a wire, or derived constants to C.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Resources:
    toffoli: int
    measurements: int
    qubits: int

    def __sub__(self, other: "Resources") -> "Resources":
        return Resources(
            self.toffoli - other.toffoli,
            self.measurements - other.measurements,
            self.qubits - other.qubits,
        )


# Public ECDSAAdd bounds at the endpoints of the requested range.
DONOR_BASE = Resources(2_214_318, 1_554_854, 1_898)  # c3f340a
DONOR_FINAL = Resources(2_155_232, 1_501_195, 1_594)  # 0b650bb

# Net effects present in the final source but forbidden by WEX's fixed-shape
# field-bit-hole interface.  The DH row combines the +14-T/-1-Q host with the
# later measured erasure (-6 T, +6 M).  The fast-constant row's +1 Q and the DH
# row's -1 Q cancel in the donor endpoint delta; WEX's own old/new interface
# wire counts are used below instead of transporting that accidental pairing.
SPECIALIZED = {
    "compare-first derived-constant cells": Resources(-1_540, -1_535, +1),
    "shared affine input pivot": Resources(-256, -257, 0),
    "shared affine output pivot": Resources(-256, -257, 0),
    "kx(C) DH host plus measured erase": Resources(+8, +6, -1),
    "fused division entry derived masks": Resources(-254, -254, 0),
    "flipped-square derived offset": Resources(-256, -255, 0),
}

# WEX f1518daf ledger.  The arithmetic/record counts include WEX's +2,045
# one-row/literal adaptation relative to the donor's c3f340a bounds.
WEX_ADDER_BASE = Resources(2_216_363, 1_556_899, 1_899)
LEADER_QUBITS = 1_932
LEADER_T = 348_877_454
LEADER_SCORE = 674_031_241_128
ADDITIONS = 29
FIRST_LOAD_CCX = 65_535
LOOKUP_TRAVERSALS = 24
CCX_PER_TRAVERSAL = 32_767
OUTER_NEGATION_CCX = 2_044
FOURIER_T = 56_774

# Source-size/memory observations used only for a linear risk screen.
WEX_LINES = 159_214
WEX_REPLAY_GIB = 64.839897
REPLAY_GATE_GIB = 78.0
DONOR_ENTRANT_BASE_LINES = 2_288
ONE_BANK_LINES = 13_889
FIVE_TRIT_LINES = 27_685
MATURE_UNIFORMISH_LINES = 47_335


def add_all(xs: list[Resources]) -> Resources:
    return Resources(
        sum(x.toffoli for x in xs),
        sum(x.measurements for x in xs),
        sum(x.qubits for x in xs),
    )


def t_after_four_p(body_ccx: int) -> int:
    return 4 * (FIRST_LOAD_CCX + ADDITIONS * body_ccx) + FOURIER_T


def projected_memory(extra_lines: int) -> float:
    return WEX_REPLAY_GIB * (WEX_LINES + extra_lines) / WEX_LINES


def main() -> None:
    donor_delta = DONOR_FINAL - DONOR_BASE
    specialized_delta = add_all(list(SPECIALIZED.values()))
    portable_delta = donor_delta - specialized_delta

    assert donor_delta == Resources(-59_086, -53_659, -304)
    assert specialized_delta == Resources(-2_554, -2_552, 0)
    assert portable_delta == Resources(-56_532, -51_107, -304)

    portable_adder = Resources(
        WEX_ADDER_BASE.toffoli + portable_delta.toffoli,
        WEX_ADDER_BASE.measurements + portable_delta.measurements,
        # The direct-swap interface uses 1,899 old sites.  Reverting the one
        # specialized kx(C) host leaves 1,595, hence a 304-site reduction.
        1_595,
    )
    assert portable_adder == Resources(2_159_831, 1_505_792, 1_595)

    delta_q_adder = WEX_ADDER_BASE.qubits - portable_adder.qubits
    projected_qubits = LEADER_QUBITS - delta_q_adder
    body_ccx = (
        portable_adder.toffoli
        + LOOKUP_TRAVERSALS * CCX_PER_TRAVERSAL
        + OUTER_NEGATION_CCX
    )
    t_model = t_after_four_p(body_ccx)
    score = projected_qubits * t_model
    pct = 100 * (score - LEADER_SCORE) / LEADER_SCORE

    assert delta_q_adder == 304
    assert projected_qubits == 1_628
    assert body_ccx == 2_948_283
    assert t_model == 342_319_742
    assert score == 557_296_539_976

    print(f"donor endpoint delta:         {donor_delta}")
    print(f"specialized net removed:      {specialized_delta}")
    print(f"portable U/H delta:           {portable_delta}")
    print(f"portable adder:               {portable_adder}")
    print(f"body CCX:                     {body_ccx:,}")
    print(f"projected WEX:                {projected_qubits:,} Q x {t_model:,} T")
    print(f"projected score:              {score:,} ({pct:+.6f}% vs leader)")
    print(f"clears 10%:                   {score * 10 <= LEADER_SCORE * 9}")

    for label, lines in (
        ("one-bank", ONE_BANK_LINES),
        ("five-trit", FIVE_TRIT_LINES),
        ("mature uniform-ish", MATURE_UNIFORMISH_LINES),
    ):
        growth = lines - DONOR_ENTRANT_BASE_LINES
        print(
            f"{label:24s} net +{growth:,} lines -> "
            f"~{projected_memory(growth):.2f} GiB linear screen"
        )
    assert projected_memory(ONE_BANK_LINES - DONOR_ENTRANT_BASE_LINES) < REPLAY_GATE_GIB
    assert projected_memory(FIVE_TRIT_LINES - DONOR_ENTRANT_BASE_LINES) < REPLAY_GATE_GIB
    assert projected_memory(MATURE_UNIFORMISH_LINES - DONOR_ENTRANT_BASE_LINES) > REPLAY_GATE_GIB


if __name__ == "__main__":
    main()
