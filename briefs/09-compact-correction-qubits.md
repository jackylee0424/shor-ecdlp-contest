# Brief 09 — compact the correction component: dirty comparator + 310 wire loans (3,932 → ~3,111 qubits)

Brief 08 has landed: start from `entrants/20261029-1215-rounds6` (6 rounds, 3,932 × 86,360,247,846 = 339,568,494,530,472), which is live in the bench. Target ≈ 3,111 × ~86.44e9 ≈ 2.7e14. Read `AGENTS.md`, `work-notes/HANDOFF.md`,
`docs/CONTRIBUTIONS-PLAN.md` §1 (310-label correction-only relabel, 3,622 Q) and `docs/ECDSAFAIL-TRICKS.md` "Top three" §1
(dirty-borrowed MCX comparator, 3,421 Q; combined 3,111 Q). Calculators: `workspace/streaming_t_breakdown.py`, `workspace/ecdsafail_tricks_costs.py`.

## Goal

Starting from the best accepted snapshot (Brief 08's 6-round entrant if it landed, otherwise `entrants/20261029-1149-streaming26`), reduce the
certified qubit bound with no change to the acceptance argument:

1. **Dirty comparator (do first, ×1.148).** Replace the 511 clean equality-chain scratch wires (4103–4613) in the batched endpoint correction with a
   dirty-borrowed multi-controlled-X (algorithm reference: `/mnt/c/code/secp256k1-point-add-spooky/.workspace/lowq-lineage/bk666/src/point_add/mask.rs::mcx_dirty`;
   reference only, not a trusted proof). Prove by induction that it implements MCX for arbitrary donor/control/target values, restores donors,
   leaves no phase garbage, is well formed, and costs 4(k−2) CCX. Lift it with `Quantum.run_ket_agrees_classical`, re-prove the equality flag
   action and `endpointTransposition_correct` with the replacement, and preserve `batchModel_data` / `batchModel_clean`. Rebuild the correction builder,
   reset list, support (`BatchSupport`, `CompleteSupport`), counts/stride, positions/layout, `UniformT` and the resource assembly. The removed labels
   must be absent from every reset and window. Expected: 3,421 Q, T per round +0.089 %.
2. **310 loans (×~1.09 more).** Apply a correction-only bijective relabel that borrows 310 arithmetic-workspace labels that are clean at the correction
   boundary (keeping the accumulator, bank, query control and path fixed). Recheck it against the new comparator support. Expected: ~3,111 Q.

The protected definitions cannot be edited: define new Entrant terms that wrap the protected builders (`relabelCompiled`, `AdaptiveCircuit.relabel`).
Develop modularly (see `entrants/*-modular` and `workspace/port_upstream.py`), then package with `workspace/package_streaming.py`.

## Verify and record

Ship step 1 as soon as it is accepted (`build.sh`, `axioms.sh`, `boundary.sh`, `score.sh`, `snapshot.sh compact-dirty`), then step 2.
For each: an experiment note, a SCOREBOARD row, LOG and HANDOFF. Keep the attribution header in `Main.lean` and add a line naming this contribution
(the dirty-comparator technique comes from our ecdsa.fail low-qubit work). Do not submit.

## Resume note (2026-10-29)

A first attempt (Codex gpt-6.1-sol) was stopped by the provider's cyber classifier after drafting `workspace/DirtyMCX.lean`
(dirty sweep definitions and early lemmas, unverified). Continue from that draft: check it with `formal-tools/check.sh workspace/DirtyMCX.lean`
first. The bench Entrant was left untouched and still equals `entrants/20261029-1215-rounds6`.
A concurrent read-only analysis may write `docs/SPOOKY-ON-09.md` and `workspace/spooky_endpoint.py`; do not edit those.
