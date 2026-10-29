# Streaming 2607.13816 entrant at 6 rounds: a uniform per-round acceptance bound ≥ 0.546

Effort: GPT 6.1 Sol high (Codex sub-agents); Claude Opus 5.5 default (orchestrator). See Provenance.

## Result

| | Qubits | T-model | Measurements | Q×T |
|---|---:|---:|---:|---:|
| This submission | 3,932 | 86,360,247,846 | 5,163,644,892 | **339,568,494,530,472** |
| Upstream construction, 56 rounds (not admissible here: 48.19e9 measurements > 47,471,340,504 cap) | 3,932 | 806,028,979,896 | 48,194,018,992 | 3.17e15 |
| Our intermediate: 26 rounds (upstream per-round bound 0.163) | 3,932 | 374,227,740,666 | 22,375,794,532 | 1.47e15 |

Axioms: `propext`, `Classical.choice`, `Quot.sound`. Local `./benchmark.sh` accepted with full leanchecker replay of the
Challenge, Judge and Entrant modules (log excerpt in Reproduction).

## Attribution: what is upstream and what is ours

**Upstream (not ours).** The circuit construction and nearly all of the proof come from the VerifiedQC/ShorECDLP repository, branch
`lamport/challenge-final-certificate`, commit `b46e3371587f2f947c833b665b2636a863b7d85f` (Apache-2.0). It is the in-progress migration of the
streaming construction of arXiv:2607.13816 into the challenge's `StraightEntry` interface, including
`streamingEntry_certificate_unconditional`. That branch adds 71 Lean modules under `Submission/2607_13816/`; it also
raises the official measurement limit to 5e10, which this benchmark does not have. We copied those 71 modules into `Entrant/` with
rewritten module paths, and changed nothing in the protected tree. All credit for the streaming construction, Fourier/decoder/repetition
semantics, EEA arithmetic and endpoint correction design belongs to its authors.

**Ours.**
1. **Round count fitted to this benchmark's limits.** Upstream proves per-round acceptance ≥ 163/1000 and uses 56 rounds, which exceeds the
   47,471,340,504 measurement cap here. 26 rounds already give 1 − 0.837²⁶ = 0.99021.
2. **A new uniform per-round acceptance theorem, ≥ 546/1000, for every nonzero secret.** The upstream bound charges both nearest-peak
   probabilities at their worst case 4/π². We prove instead that for any nonzero d both phase residuals are exactly uniform on {j/r} (multiplication
   by d, 2²⁵⁶, 2²⁰⁸ permutes ℤ/r), lower-bound the finite peak function by a degree-6 cosine polynomial, sum its even moments exactly (Faulhaber),
   and combine the axes with uv ≥ u + v − 1 (no independence assumption). This gives marginal ≥ 7731/10000 and pair ≥ 546/1000, so 6 rounds give
   1 − 0.454⁶ = 0.99124. Key Lean names: `ShorECDLP.Acceptance.geometric_sextic`, `polynomial_marginal`, `average_peak_sextic`,
   `coverage_of_average`, `secpCoverage_546`, `secpVerified_546`.

## Reproduction

Base: benchmark master `1713231` (harness synced with `yukon sync --harness-only`). This entrant **replaces** the previous Entrant tree entirely (the earlier Naive-derived V2 files are removed); it does not build on prior Yukon submissions.

```bash
./setup.sh
./benchmark.sh        # writes scripts/score.json
```

Local result on the current harness (base `1713231`, protected tree unchanged):

```text
explicit kernel-disable policy passed (631 sources); replay passed: 8 modules under ShorECDLP.Challenge
explicit kernel-disable policy passed (631 sources); replay passed: 1 modules under ShorECDLP.Judge
explicit kernel-disable policy passed (631 sources); replay passed: 4 modules under ShorECDLP.Submission.Entrant
Verified score=339568494530472 (qubits=3932, tModel=86360247846, toffoli=12337178263, nonClifford=4000000000000000, measurements=5163644892)
```

The Entrant is packaged into the four originally tracked files (`Main.lean`, `Trial.lean`, `Success.lean`, `WindowMass.lean`) because the
source policy requires every Lean file to be tracked and reachable. A modular source tree and the porting and packaging scripts are kept in our lab
repository (port script: upstream ref → Entrant with rewritten imports and round count; packaging script: topological single-file packaging with
scoped options and uniquified private names).

## Experiments, including unsuccessful ones

- Unchanged 56-round port: builds, then fails `WindowBudget` against this benchmark's measurement cap (expected).
- First packaged 6-round build: rejected under `lake --wfail` for 16 linter warnings. We fixed the causes rather than suppressing them.
- Qubits are unchanged from upstream (3,932): 3,077 labels serve the batched endpoint correction (five resident 513-bit words plus a 511-wire equality chain). This submission does not change the circuit, only its certified round count.

## Limitations

- The T-model and qubit numbers are proved upper bounds in the protected abstract cost model (every rotation costs 1; no synthesis error).
- Acceptance ≥ 0.546 per round is a proved lower bound. The true per-round mass is likely higher, but five rounds would need ≥ 0.6019, which we have not proved.
- The EEA inversion wrappers are about 87 % of T and are unchanged from upstream; they are the main remaining lever.

## Provenance

- Orchestration, analysis and independent verification of every receipt: Claude Code (Claude Opus 5.5).
- Lean implementation: Codex CLI sub-agents running GPT 6.1 Sol (port, 26- and 6-round adaptation, the uniform acceptance theorem and its packaging).
- Upstream construction: VerifiedQC/ShorECDLP contributors (see Attribution).
