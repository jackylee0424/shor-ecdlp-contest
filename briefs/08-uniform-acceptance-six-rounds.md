# Brief 08 — prove a uniform per-round acceptance ≥ 0.546 and cut the entrant to 6 rounds

Read `AGENTS.md`, `work-notes/HANDOFF.md`, and **`docs/CONTRIBUTIONS-PLAN.md` §2** (the math is designed there). Reproduce the numbers with
`python3 workspace/round_mass.py`.

## Starting point

Accepted entrant: `entrants/20261029-1149-streaming26`, which is live in the bench: 3,932 × 374,227,740,666 = 1,471,463,476,298,712, 26 rounds.
Modular sources: `entrants/20261029-1140-streaming26-modular`. Port and packaging scripts: `workspace/port_upstream.py --rounds N` and
`workspace/package_streaming.py`. **Source policy:** every Entrant Lean file must be git-tracked and reachable, and you cannot commit, so the final
form must be packaged into the four existing tracked files (`Main.lean`, `Trial.lean`, `Success.lean`, `WindowMass.lean`), as Brief 04 did.

## Goal

Replace the per-round bound 163/1000 with **546/1000** (uniform over every nonzero secret d), reduce rounds to **6**
(`1 − (454/1000)^6 = 0.99124… ≥ 0.99`), and get the official benchmark to accept
**3,932 × 86,360,247,846 = 339,568,494,530,472** (measurements 6 × 860,607,482 = 5,163,644,892).

## Proof plan (from CONTRIBUTIONS-PLAN §2; adjust as needed)

1. **Analytic minorant.** For |x| ≤ 1/2: `sinc(x)^2 ≥ 1 − π²x²/3 + 2π⁴x⁴/45 − π⁶x⁶/315`, through `sin² t = (1 − cos 2t)/2` and the one-sided
   cosine Taylor bound of degree 8 (check Mathlib: `Real.cos_bound`, `Real.cos_le_…`, `Real.one_sub_sq_div_two_le_cos`, etc.). Also the finite-L
   peak `f_L(δ) = (sin πδ / (L sin(πδ/L)))² ≥ sinc(δ)²` (likely already in protected `OrderFinding/PeakMass` as a lemma; reuse it).
2. **Uniform marginals.** For nonzero d and odd prime r, the residual of each axis over the nonzero characters k is uniform on `{j/r}` (multiplication
   by d, by 2^256 and by 2^208 permute ℤ/r). Hence the average of the nearest-peak mass on each axis equals a fixed finite sum.
3. **Finite even moments.** Sum the polynomial over j/r, |j| ≤ (r−1)/2, with Faulhaber closed forms. With π ∈ (3.1415, 3.1416) (Mathlib
   `Real.pi_gt_3141592`, `Real.pi_lt_3141593`), get `a ≥ 0.77314…`.
4. **Combine.** On the retained nearest-pair subset, `f_N f_M ≥ f_N + f_M − 1`, so mass ≥ `2a − 1 − 1/r ≥ 546/1000`. Connect this to the existing
   chain at the point where upstream uses `secpSuccessBound_numeric` / `reducedPeak_mass` (`DecoderBridge.wrappedIdeal_mass_lower`), so that
   `streamingRound_success` becomes `546/1000 ≤ …`.
5. **Six rounds.** Regenerate with `workspace/port_upstream.py --rounds 6` (or the shared round constant), update `FinalCertificate` to
   `(99:ℝ)/100 ≤ independentRetrySuccessProbability (546/1000) 6`, recompute `streamingBounds`, then package, build, and check axioms and the boundary.

Develop the analytic and finite-sum lemmas first as `workspace/Acceptance*.lean` scratch with `formal-tools/check.sh`. They only need protected
modules. Integrate into Entrant once they elaborate. Keep proofs kernel-friendly: no `native_decide`, and avoid huge `decide` on big numerals.
Exact rationals and `norm_num` are fine.

If 0.546 / 6 rounds proves too hard, ship the strongest intermediate that is proved (for example 0.40 → 10 rounds, or 0.30 → 13): any accepted
round reduction is a win. Record which.

## Verify and record

`formal-tools/build.sh`, `axioms.sh`, `boundary.sh`, then `score.sh`, then `snapshot.sh rounds6 "<score>"`.
Write the experiment note `work-notes/experiments/2026-10-29-uniform-acceptance.md`, a SCOREBOARD row, LOG, and HANDOFF. Credit: the
acceptance theorem is **our contribution**; the construction is upstream VerifiedQC (keep the attribution header in `Main.lean`, and add a line for this change).
Do not submit.
