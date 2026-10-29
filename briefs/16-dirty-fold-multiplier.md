# Brief 16 — stack patch: exact fast multiplier with a dirty-borrowed fold (≈ −6 to −10 %)

Read `AGENTS.md`, **`stack/README.md`** (the patch contract), `docs/LEVERS.md` (row C8), **`docs/MUL-PLAN.md`** (why brief 13 stopped: three post-EEA call
sites have only 25 proved-clean lanes; "What would reopen C8"), `docs/ECDSAFAIL-855.md` (L1/L2) and `workspace/MulClean.lean`, `workspace/mul_feasibility.py`.

## Base and bench

The leader is dadon `c6a88fc` (bench commit `c13a293`; 263-bit left, 224-bit physical right rounded to a 203-bit wrappedShift word, 1 direct load + 30 corrected windows): **single trial**, 855 qubits, Q×T 13,137,279,297,120 (855 × 15,365,238,944); submission bar for the whole stack: < 11,823,551,367,408. Your bench is
**`~/shorecdlp-m`** (clean at `c13a293`). Prefix every formal-tools command with `BENCH=/home/gitzard/shorecdlp-m`. Don't touch `~/shorecdlp` (brief 15) or
`~/shorecdlp-c` (restack). Re-derive the call-site inventory on this base first: the single-trial entrant may differ from the streaming base brief 13 audited.

## Goal

An **exact** fast modular multiplier for the window's multiply and square calls (signed-digit Horner with merged pseudo-Mersenne fold for p = 2²⁵⁶ − 2³² − 977),
correct for all inputs with a worst-case count, **fitting the 25-lane sites** by borrowing dirty donors (restored, no phase garbage). Reuse our proved dirty MCX
(`workspace/flag855-wip/Dirty/DirtyMCX.lean`) and the bench measured-erasure lemmas. Qubits must stay at 855. Use a hybrid if it helps: the fast cell at the
68–69-lane sites and a dirty-fold variant at the 25-lane sites.

Steps: (1) **gate:** redo the clean-lane inventory on `c13a293` and price the hybrid and dirty-fold designs exactly (`docs/MUL-PLAN.md` §single-trial). Stop if the best
exact design saves < 3 % total T. (2) Prove the multiplier (correctness mod p, clean donors/scratch, well-formedness, counts, support). (3) Swap it in and redo the
window/program resource chain. (4) Deliver as `stack/30-fast-multiplier/` (`apply.sh` idempotent on a fresh `c13a293`, `src/`, `PATCH.md`, `ENABLED` once it scores).
Validate: reset to `c13a293`, run `apply.sh`, then `BENCH=... formal-tools/{build,axioms,boundary,score}.sh`.

## Submission policy

We submit only a whole stack > 10 % below the leader. Report this patch's exact % alone, so the orchestrator can combine patches.

## Constraints and record

No sorry/axiom/native_decide/bv_decide. Linter-clean. Don't submit or commit. Experiment `work-notes/experiments/2026-10-29-dirtyfold-mul.md`, SCOREBOARD row if scored,
LOG/HANDOFF, LEVERS row C8. Attribution: the leader's credits plus ours (algorithm inspired by the ecdsa.fail modp_ft lineage; dirty MCX from our ecdsa.fail low-qubit work).
