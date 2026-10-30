# 2026-10-29 — fast multiplier build

- **Agent:** Codex
- **Hypothesis:** replace the leader's eight exact 1,110,533-CCX Horner/square calls per corrected window with the exact signed-digit, canonical-add, chunked-carry design at unchanged 856-wire support.
- **Starting snapshot:** leader spariev `c96133a`, bench commit `32b7d3859018ab352b61dca997a44fb39f86cd2a`

## M1 — current-leader audit and repricing

Wall time: approximately 8 minutes.

- Bench started clean at the required commit.  The source resource chain in `Entrant/Main.lean` still proves each `multiplyWorkProgram`, `multiplyDataProgram`, and `unmultiplyDataProgram` has at least 1,110,533 unconditional literal CCX; the square pair totals 2,223,879 CCX.  The current program uses 29 corrected windows and the same call mix: three ordinary calls (two forward, one inverse), two square calls (one each), and three post-EEA tight calls (two forward, one inverse).
- The first compiler turns each eligible source CCX into a five-P temporary AND; the catalyst layer removes its literal `P(.forward,2)`, so the final price is four P/T per eligible unconditional source CCX.  New comparator/carry CCXs must remain unconditional literals to retain this price.
- Rechecked clean widths: ordinary 68, square 69, post-EEA tight 25.  Exact per-call CCX counts are unchanged from Brief 20:

| Site | Forward CCX | Inverse CCX | Forward T at 4P | Inverse T at 4P |
|---|---:|---:|---:|---:|
| ordinary, 68 lanes | 686,976 | 572,481 | 2,747,904 | 2,289,924 |
| square, 69 lanes | 685,442 | 571,202 | 2,741,768 | 2,284,808 |
| tight, 25 lanes | 772,368 | 643,083 | 3,089,472 | 2,572,332 |

- Old/new recurring buckets are 8,884,264 / 5,390,896 CCX per window.  Over 29 windows, projected `Delta T = -405,230,688`.
- Projection: **856 x 8,075,703,356 = 6,912,802,072,736**, **-4.778137478%** versus **7,259,679,541,664**.  This clears the brief's 2% stop gate; continue to M2.
- Reproduction: `python3 workspace/fastmul_build.py`.

## M2 — canonical signed modular add/sub

In progress.

## M3 — doubling/halving and 24-lane chunked carry

Pending.

## M4 — full exact multiplier/squarer

Pending.

## M5 — integration and resource chain

Pending.

## M6 — stack packaging and official replay

Pending.

## Result

| Qubits | T-model | QxT | Proved? | Snapshot |
|---:|---:|---:|---|---|
| 856 | 8,075,703,356 projected | 6,912,802,072,736 projected | M1 arithmetic only | pending |

## Verdict

Continue: M1 exceeds the mandatory 2% threshold.
