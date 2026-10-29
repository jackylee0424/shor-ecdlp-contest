# Challenge summary (lab copy — the bench's `docs/CHALLENGE.md` is authoritative)

Benchmark: `eigenlabs/shorecdlp/lean` on Yukon (id `a721dbcb-4a80-4074-853c-53534959dcb8`),
repo `Layr-Labs/shor-ecdlp-lean`. Score is `Q×T = qubits × tModel`; lower is better.

## What the entrant defines (namespace `ShorECDLP.Entrant`, in `Entrant/Main.lean`)

| Name | Type |
|---|---|
| `entry` | `Challenge.StraightEntry`: coefficient table `[(aᵢ,bᵢ)]` + straight-line program |
| `layout` | `Challenge.DecodeLayout`: record positions + decoder kind (`nearestPair` / `wrappedShift`) |
| `bounds` | `Challenge.Bounds`: `qubits`, `tModel`, `measurements` (declared, proved upper bounds) |
| `certificate` | `Challenge.Certificate officialLimits layout entry bounds` |

The judge computes `Pᵢ = aᵢ•G + bᵢ•Q` and exposes `x, y, infinity, −x, −y, 3x (mod p)` as constant
fields. The program is straight-line over `X, H, CX, CCX, P(dir,k)` and X-basis measure-and-reset.
Gates can be optional only via `whenBit` (one bit of one constant field) or `recordGate` (one earlier
measurement bit). The decoder is protected: it accepts the first candidate `c` with `c•G = Q`.

`Certificate` fields: `gateBudget`, `recordBudget`, `tableBudget`, `candidateBudget`, `wellFormed`,
`resources` (∀ Q, qubits/tModel/measurements ≤ bounds), and
`success` (∀ Q ≠ 0, Q = d•G → 99/100 ≤ bornMass of runs where `verifiedCandidate` succeeds).

## Limits (`Challenge/Official.lean`)

| Limit | Value |
|---|---|
| gate slots (incl. untriggered optional) | 4,000,000,000,000,000 |
| measurements | 47,471,340,504 |
| coefficient rows | 983,040 |
| candidate checks | 56·(2^49+2) |

## Cost model

CCX = 7 T; every `P(dir,k)` = 1 T (any angle; Z = H·X·H is free); X/H/CX are free; qubits = distinct
wire labels used. Measurements are free in the score but limited. Reusing wires through
measure-and-reset is how qubits get saved.

## Reference points

| Construction | Qubits | T-model | Q×T | Status |
|---|---|---|---|---|
| Naive (bench `Submission/Naive`) | 206,624 | 8,918,039,383,771,648 | 1.84e21 | certified |
| Shipped Entrant (1 trial, 265-bit phase regs) | 206,642 | 355,060,161,799,520 | 73,370,341,954,576,411,840 | accepted by local `yukon run` |
| arXiv:2607.13816 Streaming (paper claim, 56 trials) | 854 | 800,005,504,760 | ≈6.8e14 | not certified; partial Lean in `Submission/2607_13816` |

## Admission pipeline

Source-boundary check (only `Entrant/` may differ) → isolated build → `leanchecker` replay → the
kernel type-checks `Judge.acceptance entry layout bounds` → metrics are kernel-reduced from `bounds`.
`benchmark.sh` also greps Entrant sources for forbidden tokens.
