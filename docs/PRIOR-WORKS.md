# Prior works inventory (2026-10-29, after the leaderboard moved)

## Leaderboard at the time

Best promoted: `9d15949` (i34-9), **7,243,285,108,034,080,000** = 77,624 qubits × 93,312,443,420,000 T, 526 measurements.
Its Entrant adds `Entrant/V2/` (~20k lines: compact `Layout`, `InvChain`, a rewritten `PointAdd`/`ScalarMul`) and
`WindowMassSharp` (263-bit phase precision). Source exported read-only to WSL `~/frontier/`.
The chain of promotions so far: 7.34e19 → 3.68e19 → 3.65e19 → 1.83e19 → 9.11e18 → 7.24e18.

## Ranked: what can bring us on board

| Rank | Source | What it gives | Status |
|---|---|---|---|
| **1** | `C:\code\ShorECDLP` (clone of VerifiedQC/ShorECDLP), branch `lamport/challenge-final-certificate` @ b46e337 (2026-10-28, Apache-2.0) | Complete, unconditional `Certificate` for the 56-round 2607.13816 streaming entry: `⟨3932 qubits, 806,028,979,896 T, 48,194,018,992 meas⟩`. It adds 71 new files under `Submission/2607_13816/` and no modifications. **It assumes `officialLimits.measurements = 5e10`; the bench has 47,471,340,504**, so 56 rounds fail `recordBudget` here. Per-round acceptance is ≥ 0.163, so **26 rounds give ≥ 0.9902**: 3,932 × 374,227,740,666 = **1.47e15** (~4,900× below the frontier). | Port in progress: `briefs/04-port-upstream-streaming-26-rounds.md` |
| 2 | Same repo, sibling branches (`streaming-dev`, `deutsch/*`, `lamport/*`, all 2026-10-28) | Ideal Fourier distribution, round reset, decoder bridge, and a resource certificate; these are pieces of rank 1 | Watch for upstream moves; rerun `workspace/port_upstream.py` |
| 3 | `C:\code\secp256k1-point-add-spooky` (+ WSL `~/r21-lean`, `~/sub870-build`, `~/spooky-build`) | Exact AND-erasure (0 T, one measurement plus a CZ repair), phase-only carries, cheaper adders, and a frontier/evidence process. Proofs use `bv_decide` (inadmissible) on Lean 4.29.1. See `docs/RELATED-WORK.md` | Local optimizations to apply on top of rank 1 |
| 4 | `C:\code\ecc-formal-toolset` (~14.8k Lean files), `ecdsa-formal-toolset(-dynamic)`, `auto-secp256k1-point-add` (346 Lean), `shor-formal-toolset(-dev)` | Formal toolsets for ecdsa.fail / ecdlp.ai point-add circuits (Gold/Leapfrog lineage) | Not yet deep-surveyed; same caveats as rank 3 likely |
| 5 | `ecdlp-point-add`, `ecdlp-point-double`, `ecdsafail-challenge(-dev)`, `ec-point-addition`, `ecdlp-5-bit/7-bit`, `ecdlp-contest`, `shor-ecdlp`, `shor-mersenne` | Circuit contests and simulators (no Lean) | Ideas only |
| — | `qai-contest`, `qai-contest-codex` | VQCC (quantum chemistry) contest | Unrelated |

## Caveat on rank 1

The upstream work is by the challenge maintainers' own collaborators and is public under Apache-2.0. A submission built on it must
credit it clearly (Entrant header and submission note). Whether to submit a derivative before the maintainers land it themselves
is the **human's call**. Ask before `yukon submit`.

## Next levers once on board (from rank 1's structure)

- Rounds: a better per-round acceptance bound (> 0.163) means fewer rounds, and T scales linearly with rounds.
- Qubits: 3,932 = 854 legacy + a 3,931-entry reset list (distinct labels count even if reset). Reusing labels instead of fresh ones could approach ~870.
  That could be another ~4.5× on score.
- T per window: apply the AND-erasure and adder transfers from rank 3.
