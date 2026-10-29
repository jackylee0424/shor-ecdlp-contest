# Brief 13 — exact fast modular multiplier for the streaming windows (lever C8, ≈ −10 % T)

Read `AGENTS.md`, `work-notes/HANDOFF.md`, **`docs/LEVERS.md`** (row C8), **`docs/ECDSAFAIL-855.md`** (L1/L2; projections in
`workspace/ecdsa855_levers.py`), `docs/CONTRIBUTIONS-PLAN.md` §3 and `docs/EEA-INVENTORY.md` (brief 12 found no cheaper multiply cell).

## Your bench: `~/shorecdlp-m` (NOT `~/shorecdlp`)

Brief 12 is building in `~/shorecdlp`; never touch it, nor `~/shorecdlp-a` / `~/shorecdlp-c`. `~/shorecdlp-m` is at the frontier
commit `93051d2` (e-man07 `ff1bf8d`: **855 × 86,239,836,030 = 73,735,059,805,650**) and is built. Prefix every formal-tools command with
`BENCH=/home/gitzard/shorecdlp-m`, and pass the bench path to any lab script. Lab file ownership: brief 12 owns `workspace/EEA*.lean`
and `workspace/eea_inventory.py`; name your files `workspace/Mul*.lean` / `workspace/mul_*.py`.

## Goal

Replace the six Horner multiply/unmultiply calls and the square calls per addition window (46,642,386 + part of 15,567,153 T/window today; 4,344
Toffoli per bit) with an **exact** uncontrolled signed-digit Horner multiplier with a merged pseudo-Mersenne fold (p = 2²⁵⁶ − 2³² − 977), modelled on the
`modp_ft` multiplier used by the ~850q ecdsa.fail entries (sources: `/mnt/c/code/secp256k1-point-add-spooky/.workspace/routes/sub870-v1/lp-variants/c77-final/src/point_add/frogtail_batch/modp_ft.rs`
and the notes cited in ECDSAFAIL-855). Use it as an algorithm reference only; its rate-based windows are **not** acceptable. Every carry, fold and
correction must be exact for all inputs, with a worst-case count. Target 600–1,000 Toffoli per bit, about −10 % total T, **Q×T ≈ 6.6–6.7e13 at 855 qubits**.

## Steps

1. **Feasibility first (stop if it fails):** at every multiply/square call site in the window, list the labels that are provably clean there, using the frontier's
   support/cleanliness lemmas. The design needs about 70 clean lanes. Write `docs/MUL-PLAN.md` with the call sites, free lanes, exact algorithm,
   exact worst-case Toffoli/T per call, and the projected total and Q×T. Qubits must stay ≤ 855 (any extra label costs 0.12 %/qubit).
2. **Prove the multiplier** (Entrant-side, Straight/Adaptive builders): functional correctness mod p for all inputs, clean scratch, well-formedness, exact
   counts and support. Reuse the bench Arithmetic lemmas (`GidneyCarry`, `SourceInPlace`, measured erasure, ...).
3. **Swap it in** for the protected Horner calls via Entrant terms. Redo the window counts/records/stride/positions, `UniformT`, slots, support and resource
   assembly; the acceptance chain is unchanged.
4. Package into the frontier's **tracked** Entrant files (`Main.lean`, `Streaming/{Certificate,Correction,Resources,Semantics}.lean`). You can't commit, and
   new untracked Lean files fail the source gate. Then `build.sh`, `axioms.sh`, `boundary.sh`, `score.sh`, `snapshot.sh mul-<slug> "<score>"`.

## Submission threshold (human policy)

We only submit a cut of **more than 10 %** against the leader at submission time (today that means Q×T < 66,361,553,825,085). Report the exact
projected and achieved percentage. If the multiplier alone falls short, say by how much, so it can be stacked with brief 12's EEA savings.

## Constraints and record

Only `~/shorecdlp-m/ShorECDLP/Submission/Entrant/` may change. No sorry/axiom/native_decide/bv_decide. Linter-clean (`--wfail`). Do not submit, push, or
commit. Record: `work-notes/experiments/2026-10-29-mul.md`, SCOREBOARD row if scored, LOG, HANDOFF; update the C8 row status in `docs/LEVERS.md`.
Attribution: keep the existing upstream/ArthurOstapenko/e-man07 credits in `Main.lean`, and add our multiplier (algorithm inspired by the ecdsa.fail modp_ft lineage).
