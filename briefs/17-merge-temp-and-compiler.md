# Brief 17 — merge public work: dadon's measurement-assisted Toffoli compiler onto spariev's 30-window entrant (stack patch 10)

Read `AGENTS.md`, `stack/README.md` (patch contract) and `docs/LEVERS.md`. **Speed matters:** this merge is obvious to other teams.

## The two public parents (both promoted, Apache-2.0 lineage, credit them)

- **spariev `070b740`** (bench commit `a72f4af`): 855 × ? = 13,046,991,502,320. It is dadon `c6a88fc`'s single trial with a 263-bit left axis and a 224-bit physical right axis
  rounded to a 203-bit `wrappedShift` word (1 direct + 30 corrected windows), plus verified EEA literal cancellation on all four EEA occurrences per window (`c5e75ef`)
  and a further small trim. **This is your base program.**
- **dadon `bcad5b2`** (bench commit `7bc69a7`, the current leader): 856 × 12,747,275,522 = **10,911,667,846,832**. It adds a **verified compiler** that lowers every
  unconditional literal CCX to Gidney's temporary logical-AND (4 T + 1 S = 5 P), a CNOT, then an X-basis measure/reset and a record-controlled CZ (H·CX·H). That is −2 T-model per CCX,
  with one reusable clean ancilla (+1 qubit) and +1 record per lowered CCX, and the decoder layout is remapped through the compiler's record map. Proven generic: "the compiler
  applies to the complete certified parent program" and transports the success certificate exactly. **But its parent is the older 263/263, 33-window entrant.**
  Read its note: `yukon submission-note bcad5b2` (from `~/shorecdlp-a`).

## Goal

Apply dadon's compiler to spariev's program. Projection: ≈ 856 × (0.75 × 15.26e9) ≈ 9.8–9.9e12 (≈ −9.6 % vs 10,911,667,846,832). Compute the exact numbers.

## Bench and steps

Bench **`~/shorecdlp-m`**. Reset it to `a72f4af` (`git fetch origin; git reset --hard a72f4af; git clean -fd -- ShorECDLP/Submission/Entrant`). Prefix formal-tools with
`BENCH=/home/gitzard/shorecdlp-m`. Don't touch `~/shorecdlp` (brief 15) or `~/shorecdlp-c` (restack).

1. Extract the compiler development from `git show 7bc69a7:<Entrant files>`: the temporary-AND identity, the record map, the expectation evaluator, the resource theorems and the
   layout remapping. Identify exactly how it hooks the parent program/certificate.
2. Install it on spariev's program as **`stack/10-temp-and-compiler/`**: `apply.sh` must work on a fresh `a72f4af` checkout, install the compiler into the
   **tracked** Entrant files (`Main.lean` and the existing `Streaming/*` / `Single/*` modules: package as needed; no new untracked files), and exit 3 if the base already contains it.
3. Re-derive the bounds: qubits (expect 856), T-model (exact, from the per-CCX −2 theorem and the base's eligible CCX count), measurements (≤ cap), and slots. Build with
   `--wfail`, then axioms, boundary, score. Snapshot `merge-tempand`, and write `PATCH.md` with the exact score and the % against the leader.
4. Then check that it also applies on top of the current leader tip `7bc69a7` (`apply.sh` should exit 3 there, since the leader already has it), and note in `PATCH.md` that
   the stack's base is `a72f4af`, not the leader tip.

## Constraints and record

No sorry/axiom/native_decide/bv_decide. Don't submit or commit. Experiment `work-notes/experiments/2026-10-29-merge-tempand.md`, SCOREBOARD row, LOG/HANDOFF, and a LEVERS row (F1).
Attribution in `Main.lean`: upstream VerifiedQC + ArthurOstapenko + dadon (`c6a88fc`, `bcad5b2`) + spariev (`c5e75ef`, `070b740`) + e-man07, plus our merge.
