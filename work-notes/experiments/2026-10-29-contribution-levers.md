# 2026-10-29 — contribution-levers

- **Agent:** Codex, Brief 05
- **Hypothesis:** a uniform averaged Fourier-peak bound can cut repetitions to six, while correction-only scratch reuse reduces support to 3,622 labels.
- **Starting snapshot:** upstream b46e337; Brief 04 accepted `entrants/20261029-1149-streaming26` during this analysis.

## Plan

Read upstream and protected source via Git, quantify three levers with lab Python, and write an implementation plan without using or changing the bench toolchain.

## What happened

- Read AGENTS, HANDOFF, prior/related work and Brief 04. Exported upstream Lean source to `/tmp/brief05-upstream` using `git show`; no bench filesystem edits.
- `python3 workspace/round_mass.py` evaluates the existing analytic bound, finite moment formulas, round/candidate budgets, small-prime full masses and sampled secp256k1 nearest-pair subsets.
- `python3 workspace/streaming_t_breakdown.py` reproduces 14,393,374,641 T/round and 3,932 labels, constructs a correction-only swap involution giving 3,622 labels, and prices arithmetic sensitivities.
- Both scripts together took about 0.3 seconds. Additional exact-rational checks confirmed the moment formulas on five small odd moduli and that p=546/1000 gives >99% success in six trials. Python syntax checks passed. No Lean proofs/builds, benchmark or score run by this brief.
- Full report: `docs/CONTRIBUTIONS-PLAN.md`, including concrete logical module/proof outlines and the tracked-source packaging requirement discovered by Brief 04.

## Result

| Qubits | T-model | Q×T | Proved? | Snapshot |
|---|---|---|---|---|
| 3,932 | 86,360,247,846 | 339,568,494,530,472 | Proposed p≥0.546 proof, not Lean-checked | None |
| 3,622 | 374,227,740,666 | 1,355,452,876,692,252 | Explicit allocation, semantic/proof port pending | None |
| 3,622 | 86,360,247,846 | 312,796,817,698,212 | Conditional combination | None |

## Verdict

Continue with the uniform finite-moment mass proof first, correction-only borrowing second. The current analytic bound is 0.164255716…, still requiring 26 rounds. Reaching ~870 labels needs a new correction architecture: the existing five endpoint words cannot be removed by renaming. The naive streamed row-loop proxy has ~15.49 billion T/window and loses on score. EEA wrappers account for 86.66% of T; generic 0-T AND erasure is already used in QROM. Measured equality cleanup is a smaller concrete port (0.04453% T reduction), and phase-only EEA optimizations need cell-specific static accounting.
