# Brief 19 — port patch 20 (width-specialized 15-bit lookup trees) onto the temporary-AND compiler program

Read `AGENTS.md`, `stack/README.md`, **`stack/20-lookup-trees/PATCH.md`** (accepted on `c13a293`: −13,418,496 T), `stack/10-temp-and-compiler/PATCH.md`.

## Situation

The leader is **dadon `96fdd4d` (bench `3fbf1a8`): 856 × 11,515,397,984 = 9,857,180,674,304**. It is dadon's temporary-AND compiler (every unconditional literal CCX →
4 T + 1 S, measured erase, +1 ancilla) applied to spariev's 30-window `c5e75ef`. Our patch 10 (brief 17, in `~/shorecdlp-m`) applies the same compiler to spariev's
later `070b740` (`a72f4af`). Our submission will be **patch 10 + patch 20**.

## Goal

Make `stack/20-lookup-trees/apply.sh` work **on top of the compiler program**, re-deriving the counts for the compiler-transformed program. Smaller lookup trees change
the set and number of eligible CCX, so the saving is now ≈ 5/7 of the pre-compiler ΔT plus the measurement/record changes. Exact counts only.

- Bench: **`~/shorecdlp`**. It currently has patch 20 applied on `c13a293`. Reset it to the leader `3fbf1a8`
  (`git fetch origin; git reset --hard 3fbf1a8; git clean -fd -- ShorECDLP/Submission/Entrant`. If `.git` is read-only for you, reverse-apply as before or ask the orchestrator).
- Extend `apply.sh` to detect whether the base contains the compiler (`3fbf1a8`, or `a72f4af` + patch 10) and apply the compiler-aware variant, keeping the pre-compiler variant
  working for `c13a293`. Package into tracked files only.
- Validate on `3fbf1a8`: build (`--wfail`), axioms, boundary, official score. Report the exact Q×T and the % against 9,857,180,674,304.
- Write in `PATCH.md` that the final stack target is `a72f4af` + patch 10 + patch 20, and that the orchestrator will run the restack once brief 17 lands.

Don't touch `~/shorecdlp-m` (brief 17) or `~/shorecdlp-c` (brief 18 reads it). Don't submit or commit. Update the experiment note `2026-10-29-precision262.md`, LOG/HANDOFF and the LEVERS E5 row.
