#!/usr/bin/env python3
"""Source-formula audit of the 2607_13816 batched Straight producer.

Run: python3 workspace/streaming_costs.py [--json]
These are analytical counts / bounds, NOT a scored Challenge certificate.
Sources are relative to ~/shorecdlp/ShorECDLP/Submission/2607_13816.
The formula audit deliberately does not enumerate billions of gate constructors.
"""
from dataclasses import dataclass
import json
import sys

TRIALS, ODD_WINDOWS = 56, 28
MEASUREMENT_CAP = 47_471_340_504
GATE_CAP = 4_000_000_000_000_000
TABLE_CAP = 983_040
CANDIDATE_CAP = 56 * (2**49 + 2)


@dataclass(frozen=True)
class Counts:
    t: int
    m: int

    def __add__(self, other):
        return Counts(self.t + other.t, self.m + other.m)

    def scale(self, n):
        return Counts(n * self.t, n * self.m)


# Window/RawCounts: preparedRawProgram_counts (raw, without zero wrappers).
raw = Counts(7 * 72_884_182, 30_272_702)
# Window/LookupPrimitiveCounts: signedCoordinatePrimitives uses 35,152,647
# Toffolis in EACH zero-allowed field block, versus RawResources' 35,151,629.
coordinate = raw + Counts(2 * 7 * (35_152_647 - 35_151_629), 0)
# Window/LookupPrimitiveCounts: negative_point_primitive (also ConstantResourceCounts).
negate = Counts(7 * 3062, 1022)
# Challenge/BatchedEndpoint, BatchPlacement, BatchCost: 14 queries, 16 swaps.
nodes = 2**15 - 1
batch = Counts(14 * 7 * nodes + 16 * 35_826, 14 * nodes)
first = Counts(7 * (2**16 - 1), 2**16 - 1)
# OuterResources.outer_feedback_overhead and Outer.axisCount.
fourier = Counts(54_168, 29 * 16)
window = coordinate + negate.scale(2) + batch

# Challenge/Reset + WindowBody. Distinct support includes 837, touched by
# fig15ZeroPrepare/Restore in coordinate even though absent from resetWires.
reset = list(range(837)) + [838] + list(range(855, 871))
batched_reset = reset + list(range(1024, 3589)) + list(range(4102, 4614))
support = set(batched_reset) | {837}
assert len(batched_reset) == len(set(batched_reset)) == 3931
assert len(support) == 3932 and 837 not in batched_reset
assert max(support) == 4613  # dense-label bound 4614 is unnecessarily large.


def total(body, reset_count):
    return (first + body.scale(ODD_WINDOWS) + fourier + Counts(0, reset_count)).scale(TRIALS)


current = total(window, len(batched_reset))
legacy = total(raw, len(reset))
excess = current.m - MEASUREMENT_CAP
# Cheapest within the uniform "7 T per replaced AND erase" class with resets
# unchanged: ceiling the per-window deficit. Partial query-node replacement
# needs a new compiler/coherence proof; whole coherent queries already have
# a unitary mathematical model (BatchExecution.batchUnitary).
per_window_conversion = (excess + TRIALS * ODD_WINDOWS - 1) // (TRIALS * ODD_WINDOWS)
uniform_repair = total(Counts(window.t + 7 * per_window_conversion,
                             window.m - per_window_conversion), len(batched_reset))
# Cancelling the adjacent last signed-coordinate negate and pre-batch negate
# removes two entire negations (NegativeControl.negativeModularNegateState_involution).
# Branch instruments are not equal after removing measurements; prove coherent
# semantics / marginalized Fourier law, then recompute chronological positions.
fused_window = Counts(window.t - 2 * negate.t, window.m - 2 * negate.m)
# Prune 3077 endpoint/auxiliary resets only after clean-frame invariant is proved.
# Then all 14 correction queries can use coherent uncompute (one extra CCX/node).
fused_coherent = Counts(fused_window.t + 7 * batch.m, fused_window.m - batch.m)
recommended = total(fused_coherent, len(reset))

# Optional tighter reset: only 513 accumulator wires need fresh rounds after
# address measurement and arithmetic cleanup. Omit final reset as well. This
# allows retaining 19,609 measured erasures over the complete program. This
# is a further conditional optimization, not the selected next producer.
accumulator_resets = (TRIALS - 1) * 513
reset_savings = TRIALS * len(reset) - accumulator_resets
minimal_resets = Counts(recommended.t - 7 * reset_savings, MEASUREMENT_CAP)

# Slot screening, NOT the unproved windowSlots lemma. Each ordinary/recorded
# primitive slot is bounded by the componentwise all-enabled primitive vector.
# Payload upper bound uses 256 bits/query, independently of Q. Double the entire
# gate-vector bound to cover both polarities of any conditional recorded repair.
# Exact Straight.gateSlots composition still belongs to milestone M2.
# pointLookupAdderPrimitives computed from ConstantPrimitiveCounts formulas.
p = 2**256 - 2**32 - 977
k = 2**256 - p
bits = [(k >> i) & 1 for i in range(256)]
adder_extra = 8 * bits[0] + 10 * sum(bits[1:255]) + bits[-1]
ge_extra = 7 * bits[0] + 9 * sum(bits[1:])
adder_vector = (516 + 512 + ge_extra + 1022, 1024 + 1020,
                2048 + 1537 + 1276 + adder_extra, 1282 + 767 + 764)
lookup_slots = 2 * (10 * nodes + 256 * 2**15) + sum(adder_vector)
negate_slots = 3070 + 4088 + 12983 + 3062
field_slots = 41769233 + 30986444 + 70649616 + 35152647
square_slots = 1896393 + 2091012 + 5630143 + 2223879
xnegate_slots = negate_slots - 2
coordinate_slots = 5 * lookup_slots + 4 * negate_slots + 2 * field_slots + square_slots + xnegate_slots
# registerEqualCircuit on 513 bits = 2*513 CX + 2*513 X + (2*513-3) CCX.
# batchOpCircuit has four equalities + two CCX/bit = 13326 slots.
swap_slots = 4 * (4 * 513 + (2 * 513 - 3)) + 2 * 513
# Two queries carry 5 words; twelve carry 1: 22 words, <=513+1 slots/word.
batch_slots = 14 * 10 * nodes + 22 * 514 * 2**15 + 16 * swap_slots
window_slot_screen = 2 * (coordinate_slots + 2 * negate_slots + batch_slots + 60)
first_slot_screen = 2 * (10 * (2**16 - 1) + 513 * 2**16)
# round_slots_le uses max over all 29 windows; use that conservative shape.
slot_screen = TRIALS * (29 * max(window_slot_screen, first_slot_screen) + 54634)


def row(c):
    return {"qubits_support": len(support), "t_model_bound": c.t,
            "measurements": c.m, "measurement_margin": MEASUREMENT_CAP - c.m,
            "q_times_t_bound": len(support) * c.t}


result = {
    "status": "analytical source formulas; full producer certificate pending",
    "components": {"raw_window": vars(raw), "coordinate": vars(coordinate),
                   "extra_negation_each": vars(negate), "correction_batch": vars(batch),
                   "current_odd_window": vars(window)},
    "legacy_reference": {"qubits_bound": 854, **vars(legacy)},
    "current_batched": row(current),
    "overflow": excess,
    "repair_uniform_unchanged_resets": {"conversions_per_window": per_window_conversion,
                                        **row(uniform_repair)},
    "repair_fuse_negations_coherent_batch_reset_854": row(recommended),
    "optional_accumulator_only_resets": {"retained_measured_erases": reset_savings,
                                         **row(minimal_resets)},
    "slot_screen_bound_pending_Lean": slot_screen,
    "slot_screen_margin": GATE_CAP - slot_screen,
    "table_rows": 2**16 + 28 * 2**15,
    "table_margin": TABLE_CAP - (2**16 + 28 * 2**15),
    "candidate_checks": CANDIDATE_CAP,
    "candidate_margin": 0,
}
assert coordinate == Counts(510_203_526, 30_272_702)
assert batch == Counts(3_784_382, 458_738)
assert window == Counts(514_030_776, 30_733_484)
assert legacy == Counts(800_005_504_760, MEASUREMENT_CAP)
assert current == Counts(806_028_979_896, 48_194_018_992)
assert recommended.m == MEASUREMENT_CAP
assert uniform_repair.m <= MEASUREMENT_CAP
assert slot_screen < GATE_CAP
if __name__ == "__main__":
    print(json.dumps(result, indent=2) if "--json" in sys.argv else
          "\n".join(f"{key}: {value}" for key, value in result.items()))
