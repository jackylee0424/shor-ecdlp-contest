# 2026-10-29 — uniform acceptance, six rounds (Brief 08)

- **Agent:** Codex.
- **Hypothesis:** prove secret-uniform per-round acceptance ≥546/1000, retaining the upstream circuit body and reducing 26 repetitions to six.
- **Starting snapshot:** `entrants/20261029-1149-streaming26`, accepted 3,932 × 374,227,740,666 = 1,471,463,476,298,712.
- **Credit:** the uniform acceptance theorem is our contribution. The streaming construction and physical/reset/retry proofs are from VerifiedQC/ShorECDLP `lamport/challenge-final-certificate` @ `b46e3371587f2f947c833b665b2636a863b7d85f` (Apache-2.0). The packaged file headers retain both attributions.

## Proof

`python3 workspace/round_mass.py` reproduced the proposed conservative polynomial average 0.773140157141 and pair bound 0.546280314281. The final proof certifies the requested rational bound, rather than relying on the numerical calculation.

The scratch proof `workspace/AcceptanceCheck.lean` elaborates against protected modules only (approximately 6 seconds). Regenerate it with `python3 workspace/acceptance_check.py`. Its components are `Acceptance{Analytic,Taylor,Moments,Residues,Peak,Mass,Sextic,Bridge}.lean`. `AcceptanceQuadratic.lean` preserves the compiling quadratic intermediate; it is not used as the final acceptance theorem. `AcceptanceAPI.lean` contains the local API probes.

The actual analytic route differs from the suggested sinc comparison:

1. Expand the exact finite squared Fourier amplitude as a normalized double sum of cosines (`geometric_normSq`).
2. Prove the global lower Taylor bound `1-x²/2+x⁴/24-x⁶/720 ≤ cos x` by successive derivative inequalities, starting from Mathlib's quadratic cosine bound. No infinite series or integration is needed (`cos_lower_six`).
3. Prove exact first-through-sixth power sums by induction. From these derive the second, fourth and sixth moments of pairwise differences and centered residues (`difference_sum_4/6`, `centered_second`, `centered_4/6`). The generator `workspace/acceptance_moments.py` writes explicit algebraic proofs; Lean checks every identity with `ring`.
4. Sum the cosine polynomial over the two Fourier indices. For the nearest-bin residual δ, obtain
   `normSq amplitude ≥ 1-π²δ²/3+2π⁴δ⁴/45-π⁶δ⁶/315` (`geometric_sextic`). The finite-size correction is nonnegative: writing `z=π²δ²≤3`, `w=L⁻²`, it is
   `w*z*((3-z)/9+w*z*(3-z)/45+(14+10*w²)*z²/945)`.
5. For odd r, prove the raw rounding formula `(2^n*k+r/2)/r`, and identify δ with `(residualIndex.val-r/2)/r`. Multiplication by the nonzero Fourier size and translation by r/2 permute the residues (`residualIndex_bijective`, `raw_residual`). Raw and wrapped endpoint masses agree.
6. Exact centered moments show the discrete marginal is at least
   `a₀=1-π²/36+π⁴/1800-π⁶/141120`. Its finite-r correction is also nonnegative (`polynomial_marginal`). Mathlib's actual bound names in this checkout are `Real.pi_gt_d6` / `Real.pi_lt_d6`, not the names suggested in the brief. Rational interval arithmetic proves `a₀≥7731/10000` (`marginal_numeric`).
7. For nonzero d, `paperCharacterProduct d` is bijective. Each peak probability is ≤1 by protected normalization. Thus `u*v≥u+v-1`, with no independence assumption. Retain each nonzero character's own exact peak contribution, using protected decoder completeness and peak injection (`coverage_exact_peak_lower`, `coverage_of_average`). Removing character zero costs at most 1/r.
8. Therefore coverage ≥`2*a₀-1-1/r ≥546/1000` for secp256k1 (`secpCoverage_546`). Nonzero public point implies nonzero residue of d via protected candidate correctness (`secpVerified_546`).

`DecoderBridge.wrappedIdeal_mass_lower` now uses `secpVerified_546` after the protected physical-to-mathematical mass equalities. `FinalCertificate` propagates 546/1000 to `streamingRound_success` and checks six independent retries with exact rational arithmetic:

`1-(454/1000)^6 = 15488178249291111/15625000000000000 = 0.9912434079546311… ≥99/100`.

## Reproduction

From the lab:

```bash
python3 workspace/acceptance_moments.py
python3 workspace/acceptance_check.py
formal-tools/check.sh workspace/AcceptanceCheck.lean
python3 workspace/port_upstream.py --rounds 6
python3 workspace/apply_uniform_acceptance.py
python3 workspace/package_streaming.py
formal-tools/build.sh
formal-tools/axioms.sh
formal-tools/boundary.sh
formal-tools/score.sh
formal-tools/snapshot.sh rounds6 "3932 × 86360247846 = 339568494530472; uniform p≥0.546"
```

`port_upstream.py` now accepts round counts 1–56 and computes both T and measurement totals from the unchanged per-round counts. Low round counts require a corresponding acceptance proof before their final certificate will compile. `apply_uniform_acceptance.py` installs the scratch proof as one modular contribution and changes the two acceptance interfaces. `package_streaming.py` folds it into the four existing tracked files, preserving source policy. Re-running the port overwrites local modular changes, so always apply the contribution before packaging.

## Verification and result

- Packaged build: passed, **98 seconds**, `logs/build-20261029-120446.log`.
- `formal-tools/axioms.sh`: exactly `propext`, `Classical.choice`, `Quot.sound`.
- `formal-tools/boundary.sh`: passed; only the four existing tracked Entrant Lean files differ.
- Official source/kernel-disable policy: passed (631 reachable sources).
- First official attempt (`logs/score-20261029-120638.log`) stopped at the warning-failing build: 16 new linter warnings (unused simp arguments/variable and redundant tactic sequencing). Proof elaboration succeeded, but `lake --wfail` correctly rejected the warnings. Removed the causes without suppressing linters; the cleaned combined scratch check passes with no warnings (`logs/acceptance-clean.log`).
- Cleaned packaged build: passed, **60 seconds**, `logs/build-20261029-120938.log`; no warnings. Certificate axiom audit and boundary passed again.
- Final official benchmark: **accepted**, **217 seconds**, `logs/score-20261029-121115.log`. Warning-failing build, source gate (631 reachable sources), protected replay (8 Challenge + 1 Judge), Entrant replay (4 modules), and final judge all pass.
- Scored snapshot: `entrants/20261029-1215-rounds6` (four packaged Lean files, score.json and metadata).

| Qubits | T-model | Measurements | Q×T | Proved? | Snapshot |
|---|---|---|---|---|---|
| 3,932 | 86,360,247,846 | 5,163,644,892 | **339,568,494,530,472** | official acceptance and full kernel replay | `20261029-1215-rounds6` |

## Verdict

Adopt: full requested 0.546 / six-round result, a factor **13/3** improvement over streaming26. The live bench contains this accepted packaged entrant. The quadratic intermediate was superseded, rather than shipped. No submission, push, commit or Git metadata writes were performed by this agent (the brief explicitly disallows committing).
