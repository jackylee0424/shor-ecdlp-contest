# Brief 14 — feasibility of a uniform per-round acceptance ≥ 0.602 (5 rounds), read-only analysis

Read `AGENTS.md`, `docs/LEVERS.md` (row A3), `docs/CONTRIBUTIONS-PLAN.md` §2 (formula, where mass is lost), and
`work-notes/experiments/2026-10-29-uniform-acceptance.md` (our 546/1000 proof). Calculators: `workspace/round_mass.py`, `workspace/acceptance_check.py`.

## Why

Leader: 855 × 86,239,836,030 = 73,734,038,237,970-ish, at 6 rounds (per-round bound 27/50 there, 546/1000 ours). **5 rounds (T × 5/6) is −16.7 %**,
the only single lever that clears our > 10 % submission bar. It needs `1 − (1−p)^5 ≥ 0.99`, i.e. **p ≥ 0.601892829…** uniformly over every nonzero secret d.
(4 rounds would need p ≥ 0.6838; 3 rounds p ≥ 0.7846. Report those too.)

## Key observations to verify, not assume

1. The present route keeps only the **nearest pair** of bins per character and combines the axes with `uv ≥ u+v−1`. Its ceiling is ≈ 2·0.7737 − 1 ≈ 0.547. **Dead for 5 rounds.**
2. Even the exact nearest-pair mass under independent phases is ≈ 0.7737² ≈ 0.5986 (continuum; finite-L slightly higher). Brief 05's samples gave
   0.60035 ± 0.00092 at d = 1. **Nearest-pair-only cannot certify 0.602 for generic d.**
3. Therefore 5 rounds is only possible if the protected decoder **accepts more outputs than the nearest pair**. `wrappedShift` (256/208 bits) emits up to
   `2·(order / 2^rightBits + 2)` candidates per trial and accepts the first with `c•G = Q`, so neighbouring bins on at least one axis may be accepted.
   Upstream's `reducedCoverageMass_lower` drops all of them.

## Tasks

1. **Exact accepted set.** From `ShorECDLP/Challenge/Decoder.lean` (`wrappedShift`, `candidates`, `decodeTrial`) and the bridge
   (`reducedCoverageMass`, `reducedVerifiedMass_eq`, `DecoderBridge.wrappedIdeal_mass_eq`), characterize exactly which output pairs (a, b) put d in the
   candidate list, as a function of the residuals (δ₁(k), δ₂(k)) and d. Read with `git -C ~/shorecdlp-m show origin/master:<path>` and the frontier Entrant
   in `~/shorecdlp-m` (read-only).
2. **True mass.** In `workspace/five_round_mass.py`, compute the accepted mass of the full accepted set for many d: random d, d = 1, small d, d near
   powers of 2 such as 2⁴⁸, and adversarial d (search for minimizers, e.g. lattice structure of (2²⁵⁶, 2²⁰⁸·d) mod r). Use exact peak functions f_L.
   Report the minimum found, with uncertainty. Use the small-prime full enumeration as a sanity check, as brief 05 did.
3. **Provable bound.** If the minimum is comfortably above 0.602, design a uniform proof: which extra bins to keep (for example ±1 neighbours on the shifted axis),
   a lower bound on their mass that survives correlation between the axes (the residual marginals are uniform, but the joint is not), and how to avoid
   needing independence. Estimate the margin, and price the Lean effort (S/M/L/XL), naming the lemmas to reuse (`average_peak_sextic`,
   `polynomial_marginal`, `coverage_of_average`, `reducedVerifiedMass_averaged`, ...).
4. **Verdict.** Go / no-go for 5 rounds (and 4 rounds), with the reasons, numbers and risks.

## Constraints

Read-only on all bench checkouts. Never touch `~/shorecdlp` (brief 12 builds there). For Lean scratch use
`BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/FiveRound*.lean` only. No submissions or commits.

## Output

`docs/FIVE-ROUND.md` (a verdict first, then the accepted-set characterization, the numerics table, the proof design and effort), `workspace/five_round_mass.py`,
a LOG line, and the A3 row status in `docs/LEVERS.md`.
