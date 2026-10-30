# Qubits for gates: the patch-10 marginal curve

Brief 18 analysis, 2026-10-29. Reproduce the integer arithmetic with:

```sh
python3 workspace/qubits_for_gates.py
```

## Result

**Build `k = 0` additional wires.** No source-identified transformation in the
856--900-qubit range clears the marginal score cost. The compiler has no remaining
nonlinear conditional gate class to lower, the high-volume AND erasures are already
measurement-assisted, the target correction already uses clean adaptive v-chains, and a
17-bit lookup cannot remove a window under the coefficient-row cap.

The sole conditional exception is C8, the exact fast multiplier. At the donor sensitivity
point of 540 CCX/bit it would justify an independent 45-wire pool, but that gives **901**
qubits and still lacks the exact quotient-flag erasure and certified worst-case CCX count.
It is a reason to finish the C8 circuit, not a reason to add wires to patch 10 now.

All score changes below use patch 10's projected bound

`856 × 11,513,899,424 = 9,855,897,906,944`.

“Exact” means an integer consequence of an existing source count. “Conditional” means the
integer price is exact *if* the described replacement circuit exists; it is not a claim that
such a circuit has been proved. Score change is `new − patch10`, so negative is better.

## Candidate table

| Candidate | Wires | Exact/conditional ΔT | Δscore | Score vs patch 10 | Proof effort | Overlap |
|---|---:|---:|---:|---:|---|---|
| Lower another compiler gate class | +1 | **0 exact** | +11,513,899,424 | +0.116822% | S audit; XL for a genuinely controlled temporary-AND compiler | F1/patch 10 already lowers every literal CCX |
| Add both a second and third compiler scratch | +2 | **0 exact** | +23,027,798,848 | +0.233645% | same | F1 |
| Hold coherent carry/compare ANDs, one lane | +1 | 614,700 conditional | +10,987,101,524 | +0.111477% | L | arithmetic part of C8, but does not require a new multiplier |
| Hold coherent carry/compare ANDs, 44 lanes | +44 | 27,046,800 conditional | +482,269,454,656 | +4.893207% | XL | C8 |
| Hold every carry/compare AND in a 256-lane pool | +256 | 157,363,200 conditional | +2,772,570,374,144 | +28.131078% | XL | C8; outside requested range |
| Re-measure B/E/G/H EEA cells | +0 | **0 exact** | 0 | 0% | none | C2; already done |
| Hold an unmeasured A/D/F EEA product | unknown | **0 established** | — | — | L/XL: no repeated product with a proved clean donor was found | C3/C4 are the only locally priced EEA products and overlap the parent's cancellation pass |
| Replace dirty correction/comparator MCX with clean v-chain | +1…+44 | **0 exact in this target** | at least +11,513,899,424 for +1 | at least +0.116822% | S audit | B2/B3 target an older correction; patch 10 uses IPX |
| Give unary lookup more workspace | +1…+44 | **0 exact** | positive wire cost only | worse | M/XL for a different QROM | E5 changes tree width without adding workspace |
| Introduce a 17-bit bank wire | +1 | **0 exact** (no window removed) | +11,513,899,424 | +0.116822% | L/XL | E1b/E2/E3 |
| C8 multiplier at 540 CCX/bit, independent lane pool | +45 | 1,166,751,600 conditional | **−533,117,717,520** | **−5.409124%** | XL; exact circuit is blocked | C8/Briefs 13 and 16 |

The exact condition for `k` added wires is

`(856+k)(T−ΔT) < 856T`, equivalently `ΔT > kT/(856+k)`.

The prompt's `ΔT/T > k/856` is the conservative first-order form. The first exact integer
threshold is **13,435,122 T**, and the +44 threshold is **562,901,750 T**.

## 1. What the compiler leaves

Patch 10's `lower` transforms exactly `.gate (.literal (.CCX …))`. Its certificate subtracts
`2 × 1,872,869,880 T` using a proved lower bound on the number transformed; it does not claim
that this lower bound is the fully evaluated syntactic count. This distinction matters: a
tighter `added` theorem could improve the bound without adding a wire, whereas another scratch
wire cannot transform a literal CCX twice.

The reachable-constructor audit found:

- **0 record-controlled CCX.** The correction records H/CX/H for CZ; registered phase
  corrections are Clifford/phase gates.
- **0 `whenBit` CCX in the target lookup/control constructors.** The conditional lookup gates
  are X/CX. `constantStraight` only specializes CX; a CCX passing through it remains a literal
  CCX and is therefore lowered.
- **0 protected-builder exceptions.** Once a builder emits a literal CCX into the `Straight`
  program, `lower` sees it regardless of which definition built it.
- Measured-AND **computes** are literal CCX and are lowered. Their record-controlled cleanup is
  already Clifford and costs 0 T.

Thus a second or third reusable compiler ancilla has no remaining source class to attack. A
controlled temporary-AND construction would only become relevant after introducing a new
record/bit-controlled nonlinear gate; patch 10 has none.

## 2. Holding AND results

### Horner and square ladders

There are exactly 240 protected 1,110,533-CCX ladders:

| Subroutine | Calls | CCX | T after patch-10 lowering | Share of patch-10 T |
|---|---:|---:|---:|---:|
| Six Horner ladders × 30 signed windows | 180 | 199,895,940 | 999,479,700 | 8.680636% |
| Two square ladders × 30 signed windows | 60 | 66,631,980 | 333,159,900 | 2.893545% |
| **Total** | **240** | **266,527,920** | **1,332,639,600** | **11.574181%** |

Each ladder has 256 controlled modular add/sub stages. The square/subtract/square sequence also
has one retained modular subtraction per window, for

`30 × (6×256 + 2×256 + 1) = 61,470` stages.

At width 256, `controlledAddCarry` contains 256 MAJ/UMA compute-cleanup CCX pairs and
`controlledCompareLT` contains 256 majority/adjoint pairs. The chains are sequential, so a
256-lane clean pool can be reused between them. This gives an exact *opportunity census* of

`61,470 × 512 = 31,472,640` cleanup CCX,

with peak simultaneous holds 256. A hypothetical lane that can be threaded through both chains
saves two cleanup CCX per modular stage, hence only

`61,470 × 2 × 5 = 614,700 T/lane`.

This is 21.9 times too small even for the first wire. The optimistic linear envelope through 44
lanes saves 27,046,800 T while the exact score threshold is 562,901,750 T. A proof of the
chunked held-carry construction would therefore not change the build decision.

### Correction and lookup

Each signed-window IPX correction has 13 unary-tree queries and eight measured tests. After the
5-T compiler price, its nonlinear budget is

`13×32,767×5 + 8×768×5 = 2,160,575 T/window`,

or 64,817,250 T across 30 windows. The query nodes and test chains already use measured
erasure. Keeping them live longer cannot remove another coherent matching CCX.

The coefficient lookup likewise uses unary iteration: additional clean path wires can reduce
depth or expose parallelism, but the worst-case T count remains one compute per visited internal
node. No T-for-space exchange was found.

### EEA

The four wrappers per signed window already contain **6,961,844 measured erasures per wrapper**
in B/E/G/H and boundary constant arithmetic. Reapplying the same idea saves exactly zero.

The three largest not-already-priced classes are A, D and F:

| Coherent EEA census item | Raw CCX/signed window | 5× raw census/window |
|---|---:|---:|
| A terminal tests, padding and preshift | 5,870,880 | 29,354,400 |
| D quotient length/sign control | 3,604,728 | 18,023,640 |
| F postshift | 3,667,680 | 18,338,400 |
| **Total** | **13,143,288** | **65,716,440** |

These are pre-parent-cancellation census budgets, not removable pairs or a claim that every
listed CCX survives the parent's literal-cancellation patch. The existing inventory found no
source-compatible repeated product with a clean donor in A/D/F, so the established saving
remains zero. C3/C4's
Block-E middle/held products are the only exact local proposals; they need no added wire and
overlap the literal cancellation already present in the patch-10 parent, so they are not counted
again here.

## 3. Clean versus dirty multi-controls

The old endpoint correction had dirty-borrowed equality chains, but it is not the target program.
Patch 10's IPX correction supplies 255 clean scratch wires and calls the adaptive measured
v-chain. The protected EEA adaptive chains likewise already use clean scratch and measured
erasure. The remaining controlled comparisons are Cuccaro carry probes, not dirty-borrowed MCX.

Therefore the number of reachable dirty chains to which the proposed
`4(k−2) → 2(k−2)` substitution applies is **zero**. The generic formula would save 10 T per
clean lane per invocation after the compiler, but there is no target invocation to multiply it
by.

## 4. Wider lookup and fewer windows

The actual patch-10 table is not the invalid 263/203 layout's 786,432 rows. It is:

- direct 16-bit window: 65,536 rows;
- 30 signed windows covering the remaining 247 left bits and 224 right bits;
- **901,120 rows total**, leaving 81,920 below the 983,040 cap.

An exact dynamic program over signed widths 1…17 finds that 29 signed windows require at least
**1,245,184 rows**, 262,144 over the cap. The optimum needs seven 17-bit left windows; one extra
bank wire does not help. Workspace cannot relax the organizer's coefficient-row limit, so the
exact T saving from a 17-bit bank in this layout is zero.

## 5. Multiplier lane pool

The current eight-ladder budget is 1,332,639,600 T. Replacing every call by the donor sensitivity
point `540×256 = 138,240 CCX/call` would cost 165,888,000 T and save **1,166,751,600 T**.

With a separate 45-wire pool, patch 10 would become conditionally

`901 × 10,347,147,824 = 9,322,780,189,424`,

a 5.409124% score cut. The replacement only needs to be below **631,319 CCX/call** to beat patch
10 at 901 qubits, so the space trade would be generous *if an exact circuit existed*.

It does not yet exist. Brief 16 found that the donor's 540-CCX/bit point assumes exceptional-state
corrections; the exact quotient flag cannot currently be erased without reconstructing the word
and losing the priced gain. Three sites expose only 25 clean lanes, versus about 70 required.
Also, patch 10's temporary-AND scratch is live while compiling multiplier CCX, so independent
composition costs +45 beyond 856, not +44. Reusing that scratch as a held multiplier lane would
need a fused schedule and a new liveness proof.

## Marginal curve

For an *at-most-qubit* budget, the established frontier is flat:

| Available total qubits | Best established T | Best established score | Choice |
|---:|---:|---:|---|
| 856…900 | 11,513,899,424 | **9,855,897,906,944** | use 856; `k=0` |

The strongest small-workspace conditional envelope is the held-carry calculation. For
`Q = 856+k`, `0 ≤ k ≤ 44`, it is exactly

`T_hold(Q) = 11,513,899,424 − 614,700k`,

`score_hold(Q) = (856+k) × T_hold(Q)`.

It is worse than patch 10 for every point in the range:

| Q | Conditional T | Conditional score | Δscore |
|---:|---:|---:|---:|
| 856 | 11,513,899,424 | 9,855,897,906,944 | 0 |
| 860 | 11,511,440,624 | 9,899,838,936,640 | +43,941,029,696 |
| 870 | 11,505,293,624 | 10,009,605,452,880 | +153,707,545,936 |
| 880 | 11,499,146,624 | 10,119,249,029,120 | +263,351,122,176 |
| 890 | 11,492,999,624 | 10,228,769,665,360 | +372,871,758,416 |
| 900 | 11,486,852,624 | 10,338,167,361,600 | +482,269,454,656 |

The calculator prints all 45 integer points. The next possible discontinuity is the conditional
C8 point at Q=901, not a gradual small-ancilla improvement.

## Recommendation

Do not start a positive-qubit patch from any of candidates 1--4. Keep patch 10 at 856 qubits and
spend proof effort on zero-wire bound tightening or existing C3/C4-sized local rewrites.

Reopen the qubit trade only after C8 produces an exact worst-case circuit count. If that count is
at most 631,319 CCX/call and the three constrained sites still require the full lane pool, build
the **+45-wire / 901-qubit** variant. Until then, the recommended build is **`k=0`**.

## Source anchors

- `stack/10-temp-and-compiler/src/Main.lean`: `lower`, `added`, compiler resource theorem and
  projected patch-10 bound.
- `a72f4af:ShorECDLP/Submission/Entrant/{Main,Single/Physical}.lean`: target window schedule,
  correction and coefficient layout (read through the local object in `~/shorecdlp-a`; the
  requested `~/shorecdlp-c` checkout did not contain the historical object).
- protected arithmetic at the same object: `Arithmetic/{CarryAdd,Compare,HornerMul}.lean`.
- `docs/EEA-INVENTORY.md`, `docs/MUL-PLAN.md`, `docs/FEWER-WINDOWS.md`.

