# Brief 10 — flag-only endpoint correction: 3,932 → 855 qubits (Q×T ≈ 7.37e13)

Read `AGENTS.md`, `work-notes/HANDOFF.md` and **`docs/SPOOKY-ON-09.md` §6 (design) and §7 (paper check: go)**. Numbers:
`python3 workspace/spooky_endpoint.py` (including `paper_check()`).

## Start state

- Live in the bench, and the accepted best: `entrants/20261029-1215-rounds6`, 3,932 × 86,360,247,846 = 339,568,494,530,472 (6 rounds, our uniform
  acceptance ≥ 0.546). Modular sources/scripts: `workspace/port_upstream.py`, `workspace/apply_uniform_acceptance.py`, `workspace/package_streaming.py`.
  Every Entrant file must be git-tracked, so the final form goes into the four existing files (`Main`, `Trial`, `Success`, `WindowMass`).
- Brief 09 (stopped, superseded) left dirty-chain work in `workspace/DirtyMCX.lean` and `workspace/DirtyBatch.lean`. Reuse the DirtyMCX
  induction (dirty-borrowed MCX: donors restored, no phase garbage, 4(k−2) CCX) for the zero tests.

## Design (from §6/§7)

On a valid accumulator acc = F(P) (`SignedBatchReady`, from `batchedWindow_coordinate_ready`), the endpoint correction is "if acc = sₖ then tₖ"
for the row's columns s₀..s₃ = F(0), F(C), F(−C), F(−2C) and t₀..t₃ = enc(C), enc(2C), enc(0), enc(−C) (`exceptionalEndpointWords`,
`fixedMatching_comp`, `fixedExceptionSwaps_correct`). Replace the five-word batch (`batchSchedule`, words at 1024–3588, chain 4102–4613) with:
1. **Flags:** for k = 0..3, XOR the column into acc with an ordinary unary table query (leaf CX targeting acc wires, chained s₀, s₀⊕s₁, …),
   zero-test into one-hot flag fₖ.
2. **Update:** for each k, a flag-controlled XOR of (sₖ ⊕ tₖ) into acc.
3. **Clear:** zero-test against tₖ with chained queries; every flag returns to 0 (T injective; s distinct, since 2C, 3C ≠ 0).
   That is 13 queries and 8 zero tests. Each zero test is a clean AND chain on 257 bits, then a dirty chain on the other 256 plus one ancilla, borrowing
   255 first-half accumulator wires (1,276 CCX). It uses 4 flags + temporaries within 260 of the 310 labels that are clean at that point.
- Infinity rows (C = 0): `normalizedEndpointWords_infinity` makes all eight words zero, so the scheme acts as the identity (no special case).
  They are also unreachable for Q ≠ 0 (`windowPoint_ne_zero`).
- New small lemma: C ≠ 0 → 2C ≠ 0 ∧ 3C ≠ 0 (`order_prime`, `generator_nsmul_eq_zero`, Mathlib `addOrderOf_eq_prime`).

Expected: support **855** (the core, including 837; no label ≥ 1024), T **3,053,253 per window**, total **86,237,418,174**,
records 5,158,465,644 (−863,208 per round), so **855 × 86,237,418,174 ≈ 7.373e13**. Recompute exactly before declaring bounds.

## Work plan

1. New Entrant correction model (`Entrant/Streaming/Challenge/FlagCorrection*.lean` in the modular tree): flag invariants, the query-chain
   XOR lemma, the zero-test lemma (from DirtyMCX + `MeasuredAnd` where useful), the action on `SignedBatchReady` inputs, and clean scratch/flags at exit.
   Reuse `unaryAction_coherent`, `tableXorGates`, `endpointSelectGates_source`, `readEndpointWords_correct` and `fixedMatching_comp`.
2. Swap it into the window (`batchedWindowSegments` analogue in Entrant) and redo `BatchedWindowCoherent` / `WindowValidity` under the
   stronger readiness predicate. Then redo records, stride, positions/layout, `UniformT`, slots, the support lemmas (`CompleteSupport` = 855) and
   the resource assembly. Transport the acceptance proof unchanged.
3. Develop and check in `workspace/` first (`formal-tools/check.sh`), then package, `build.sh`, `axioms.sh`, `boundary.sh`, `score.sh`,
   then `snapshot.sh flag855 "<score>"`.

If the full swap stalls, ship nothing half-done: leave the bench at the rounds6 entrant (`formal-tools/restore.sh 20261029-1215-rounds6`) and
document exactly which obligation blocks.

## Record

Experiment note `work-notes/experiments/2026-10-29-flag855.md`, a SCOREBOARD row, LOG, and HANDOFF. Keep the upstream attribution in
`Main.lean` and add a line for this contribution (flag-only endpoint correction, ours). Do not submit, push, or commit.
