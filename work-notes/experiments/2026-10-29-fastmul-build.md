# 2026-10-29 — fast multiplier build

- **Agent:** Codex
- **Hypothesis:** replace the leader's eight exact 1,110,533-CCX Horner/square calls per corrected window with the exact signed-digit, canonical-add, chunked-carry design at unchanged 856-wire support.
- **Starting snapshot:** leader spariev `c96133a`, bench commit `32b7d3859018ab352b61dca997a44fb39f86cd2a`

## M1 — current-leader audit and corrected repricing

Wall time: approximately 70 minutes including the circuit-level audit.

- Bench started clean at the required commit.  The source resource chain in `Entrant/Main.lean` still proves each `multiplyWorkProgram`, `multiplyDataProgram`, and `unmultiplyDataProgram` has at least 1,110,533 unconditional literal CCX; the square pair totals 2,223,879 CCX.  The current program uses 29 corrected windows and the same call mix: three ordinary calls (two forward, one inverse), two square calls (one each), and three post-EEA tight calls (two forward, one inverse).
- The first compiler turns each eligible source CCX into a five-P temporary AND; the catalyst layer removes its literal `P(.forward,2)`, so the final price is four P/T per eligible unconditional source CCX.  New comparator/carry CCXs must remain unconditional literals to retain this price.
- Rechecked clean widths: ordinary 68, square 69, post-EEA tight 25.
- The initial arithmetic-only replay reproduced Brief 20's projected cut, but building the first source cells exposed two omitted physical costs.  A modulo-`2^256` pass has 255 forward carry CCXs, not 256, and a flag-controlled public mask needs an extra quadratic carry CCX at each non-low set bit.  More importantly, the final signed quotient is not one fixed predicate: addition needs `[result < addend]`, while subtraction needs `[p ≤ result+addend]`.  Brief 20 priced one `A(L)` pass but supplied no circuit for selecting those predicates with a quantum sign.  Conditioning the terminal phase is non-Clifford and is not eligible for the leader's unconditional-literal 4-P lowering.
- The checked low-level builders give the following *optimistic lower bound*, not an exact complete-cell price:

| Site | Forward CCX | Inverse CCX | Forward T at 4P | Inverse T at 4P |
|---|---:|---:|---:|---:|
| ordinary, 68 lanes | 691,574 | 574,274 | 2,766,296 | 2,297,096 |
| square, 69 lanes | 690,040 | 572,995 | 2,760,160 | 2,291,980 |
| tight, 25 lanes | 776,966 | 644,876 | 3,107,864 | 2,579,504 |

- The direct exact phase-safe fallback uses conditional-add/compare/unadd plus an overflow cleanup for the sign-selected quotient.  Its exact structural price is 8,356,097 CCX/window: ordinary calls 1,043,318/926,018, square 1,041,016/923,971, and tight 1,170,182/1,038,092.  On this leader it projects **856 x 8,419,666,672 = 7,207,234,671,232**, only **-0.722413023%**.
- This is below the brief's mandatory 2% continuation threshold.  M1 therefore fails after circuit-level correction, and the build stops before bench mutation.  Reproduction: `python3 workspace/fastmul_build.py` (prints both the invalid optimistic lower bound and the phase-safe fallback).

## M2 — canonical signed modular add/sub (stopped)

Not promoted to the bench because corrected M1 failed.  Reusable checked scratch remains:

- `workspace/FastMulSigned.lean`: canonical transformed signed-add algebra, including the same `+q*c` correction for positive and complemented-negative representations.
- `workspace/FastMulCarry.lean`: exact chunk-add and coherent boundary-XOR builders; a 24-lane tight pass is 503 literal CCX.  It also contains the flag-controlled public-mask carry cell.  Its quadratic majority predicate is X-measure/reset with three Clifford CZ corrections; the local forward-computation, phase-correction, coherent-erasure, measurement and CCX theorems compile without warnings.

These do not constitute the requested full signed modular cell: the quantum-sign-selected final quotient erasure remains the missing, over-budget component.

## M3 — doubling/halving and 24-lane chunked carry (not reached)

Pending.

## M4 — full exact multiplier/squarer (not reached)

Pending.

## M5 — integration and resource chain (not reached)

Pending.

## M6 — stack packaging and official replay (not reached)

Pending.

## Result

| Qubits | T-model | QxT | Proved? | Snapshot |
|---:|---:|---:|---|---|
| 856 | 8,419,666,672 fallback projection | 7,207,234,671,232 fallback projection | checked local cells only; no complete signed cell | none |

## Verdict

**Stop at M1:** the exact phase-safe construction is only 0.722413023% below the leader, below the required 2%.  No Entrant file, stack patch, snapshot, score, submission, or commit was produced.  The bench stayed clean at `32b7d38`.
