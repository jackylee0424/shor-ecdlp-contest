# WEX frontier-adder swap feasibility

## Verdict: no-go for the direct W1 swap

The arithmetic projection is attractive but is **not a buildable projection of the
accepted `0b650bb` source**.  If its advertised 1,594-wire / 2,155,232-Toffoli
adder could be substituted without changing WEX's table transport, the result
would be **1,627 Q × 341,786,258 T = 556,086,241,766**, a **17.498447%** cut from
ArthurOstapenko `f1518daf`.  All scalar organizer-limit calculations pass.

The required premise is false.  `0b650bb` is a family `program C`, but its emitted
gate list is not a fixed family whose only `C` dependence is optional X/CX gates
controlled by individual protected table-field bits.  It specializes control flow,
gate order, and even a target wire from derived facts about `C`.  The two hard
seams are:

1. `affineInputWith` changes its recursive zero-chain/pivot schedule according to
   the first differing bits of two derived point codes.  It is used by both
   `inputClass` and `Edges.shared`.
2. `clrDH` selects the accumulator wire `point.x[kx C]`, where `kx C` is the first
   bit separating `C` from `dialogExceptionPoint C`.  This is a data-dependent
   wire identity, not a constant-bit X/CX hole.

The fast constant cells add a third, independent seam: their masks use derived
integers such as `c+k`, `k+1`, `(k+1+p) mod 2^256`, half-rounded words and a
threshold predicate.  Those are not fields exposed by the unchanged protected
`PointCoeff` reader.  The old WEX port deliberately rewrote even `cx+1` as “load
`cx`, then add literal 1” for exactly this reason.

Making these three mechanisms uniform would be a new adder design and proof, not
the requested frontier swap.  It would invalidate the 1,594-qubit and 2,155,232-
Toffoli receipts until new support/count theorems were proved.  Phase B therefore
did not start.  `/home/gitzard/shorecdlp-c` remains clean at `60ccc81`; no build,
score, snapshot, submission, push, commit, or bench edit was made.

## A.1 Exact provenance map of the WEX leader

The accepted WEX Entrant has 159,214 Lean lines:

| File | Lines | Provenance |
|---|---:|---|
| `ECDSAAdd/Part1.lean` | 39,958 | 207 modules from `c3f340a` |
| `ECDSAAdd/Part2.lean` | 48,300 | 346 modules from `c3f340a` |
| `ECDSAAdd/Part3.lean` | 16,612 | 156 modules from `c3f340a` |
| `ECDSAAdd/Part4.lean` | 15,166 | 139 modules from `c3f340a` |
| `Main.lean` | 39,178 | Streaming producer, WEX template/transport, compilers and certificate |

`ECDSAAdd/MODULES.txt` is the exact 848-module source-to-part manifest.  I parsed
each `-- source: <path>` section and compared it with
`git -C ~/research/ecdsafail-lean show c3f340a:<path>`.  After removing original
`import` lines, the sources contain 116,891 lines, the concatenated sections
118,300 lines, and 115,257 lines align unchanged.  Every module is mechanically
touched because the bundle adds section boundaries; other stated changes are
consolidated imports, expanded local syntax/macros, private-name repairs and
namespace qualification.  `ASSEMBLY.json` records 48 support-name qualifications
and eight vendor-comment edits.  Thus all four Part files are vendored source;
none is WEX arithmetic glue.

`Main.lean` divides as follows (line numbers refer to bench commit `60ccc81`):

| Lines | Role |
|---|---|
| 1–23,935 | unchanged body-parametric 29-addition Streaming producer, table, decoder and success proof |
| 23,936–25,672 | `ECDSAAdd.ShorPort`: adapted `c3f340a` finite-addend program and field-bit template |
| 25,673–28,253 | native ECDSAAdd semantics → Shor `Straight`/coherent bridge |
| 28,254–35,491 | WEX lookup compiler, specialization, parity sharing, negative-double corner and resource proofs |
| 35,492–36,001 | compact native→Streaming wire permutation/support proof |
| 36,002–38,272 | retained measured-AND/Y-catalyst compiler stages and 29-addition producer integration |
| 38,273–39,178 | WEX compiler credit, final bounds and certificate |

The important distinction is that `c3f340a` supplied the native theorem stack,
while the `ShorPort`, `Bridge`, `WEX`, `WEXCredit` and `WEXFinal` sections supply
the Shor-specific table and certificate glue.

### The interface WEX actually consumes

- **Program family:** native `finiteS L C cx cy`; table template
  `finiteT L row rowD`; WEX code `wFiniteOne`, optimized `wFiniteTight`,
  `rowAddCode`, and final `compactBody.program`.
- **Layout/ports:** `streamLayout` maps native control to 836, native finite flag
  (opposite polarity) to Streaming infinity 838, x to 263–518, y to 580–835,
  address to 855–869 and sign to 870.  `compactPerm` packs the remaining native
  sites while keeping those ports fixed.
- **`cx cy` parameterization:** `finiteS` is ordinary native code parameterized by
  the finite addend.  `finiteT` replaces every allowed constant mask by
  `TInstr.gated (ConstantBit row field bit) ...`.  Its `CliffordGated` proof says
  that only X and CX are optional.
- **Finite-addend invariant:** every selected row is a nonzero multiple of the
  prime-order generator.  `structural_enables` proves `cy ≠ -cy` and
  `exceptionBit C = true` from nonvanishing 2C and 3C.  `finiteT_eq/spec` then
  identify the specialized template with native `finiteS`.
- **Correctness/resource receipts:** `finiteT_spec`, `finiteT_counts`,
  `finiteT_supportQ`, `finiteT_physical`, `finiteT_gateSlots_le`,
  `finiteT_clifford`, `finiteT_encodes`, `finiteT_qubits_le`; WEX lifts these
  through `tight_stream_program_equiv`, the coherent row implementation,
  `compactBody_resource_ledger`, and `BodyCredit`.
- **Lookup holes:** a `TInstr.gated` constant X/CX becomes a `LookupPort`; a
  protected 15-bit unary traversal selects the row and its leaf emits the
  `whenBit` gate.  Literal arithmetic stays outside the lookup.  The leader's
  parity-sharing proof reduces this to 24 traversals while preserving a single
  coherent branch coefficient across all addresses.

## A.2 Uniformity audit of `0b650bb`

The final accepted path is
`program (.some cx cy) = Edges.wrapper layout C cy (genFFused layout cx cy)`.
The top-level signature alone does not imply a uniform gate list.
The source anchors below are all in donor `ECDSAAdd/Submission/Entrant/Main.lean`
at `0b650bb`: `fastConstAdd/fastConstNeg` at 9,431–9,434,
`affineInputWith/inputClass` at 16,478–17,094, `kx/cxk/clrDH` at
17,468–17,691, `Edges.shared` at 53,131, `EntryFuse.entry` at 54,464,
`fusedY` at 56,307 and the accepted `program` at 59,480.

| Location | Dependence on `C` | Fixed-shape WEX hole? |
|---|---|---|
| top-level `match C` | zero emits `[]`, finite emits the adder | Yes only because WEX separately proves every selected addend finite/nonzero and can discard the zero branch. |
| `cy ≠ -cy`, `exceptionBit C` structural enables | finite subgroup facts | Yes: as in the old port, both are true on nonzero prime-order rows. |
| direct `maskedConstant`, `xorConstant`, `maskedPointConstant` of protected C/−C/2C fields | individual field bits; only X/CX vary | Yes; this is the old WEX mechanism. |
| `bitTest`, `flipIf`, `parityControl` | one classical parity bit changes surrounding X/CX | Locally yes when that predicate is an exposed field bit. |
| `inputClass` | selects `affineInputWith` and then recursively follows equal code bits until a data-dependent pivot | **No.** Even after the structural enable fixes the outer branch, instruction order and pivot target vary with C and the exception point. |
| `Edges.shared` | same recursive specialization for C versus C+C | **No.** Same pivot/order problem, using doubled fields. |
| `DHClass.kx`, `DHClass.cxk`, `clrDH` | computes first separating bit and uses `point.x.getD (kx C)` as a gate wire; `DHGadget` also specializes four booleans | **No.** Existing holes switch gates on fixed targets; they cannot select the target wire. |
| `fastConstAdd`, `fastConstNeg` | masks of `c+k`, `k+1`, `2^n−1−k`, `(k+1+p) mod 2^n`, etc. | **No direct hole.** These derived integer bits are not protected point fields. They need a new algebraic decomposition or coherent computation. |
| `fusedY` / `EntryFuse.entry` | half-rounded tables, xor masks, parity and a derived threshold branch | **No direct hole.** Only the raw `−cy` bits are exposed; the derived masks/predicate are not. |
| `zrep` / `clrF` forced-input and known-output trick | fixed literal 5 and state invariants | Yes. It is independent of C and already has a fixed gate list. |
| square and one-bank arithmetic kernels | no C after constants are prepared | Yes; these are uniform literal arithmetic. |
| corner writes | C, −C, C+C and the exception/negative-double point | Yes in principle from the protected point/double fields; WEX already has the one-row corner transport. |

`affineInputWith` happens to prove constant worst-case counts, but equal counts are
not enough: Shor's submission syntax requires the `Straight` structure and record
cursor to be fixed before Q is known.  The current WEX template can ask whether
one protected field bit is zero or one; it cannot ask for the first index at which
two fields differ, branch a recursive measured chain on that derived predicate,
or use the resulting index as a wire.

Consequently, the accepted `program_toffoli`, `program_measurements` and
`program_qubits` theorems cannot simply be transported.  A universalized variant
would need new coherent semantics, support, physicality, record, slot, eligible-
CCX and compiler-credit proofs.  In particular, 1,594 Q relies on the specialized
wire omissions, so it is not a bound for an unbuilt universal circuit.

## A.3 Arithmetic projection and limits

`python3 workspace/wex_swap.py` checks the following exact hypothetical ledger:

```text
body CCX = 2,155,232 + 24 × 32,767 + 2,044 = 2,943,684
T = 4 × (65,535 + 29 × 2,943,684) + 56,773 + 1
  = 341,786,258
Q = 1,932 − (1,899 − 1,594) = 1,627
Q×T = 556,086,241,766  (−17.498447%)
```

Using the accepted 1,501,195-record bound as if it survived the port gives
2,289,647 source records per body and a 66,500,740 parent cursor.  The exact
one-record-per-lowered-CCX total would be 151,933,111.  Reusing WEX's deliberately
loose admission method gives 664,584,110 measurements and 104,354,177,530 slots.

| Organizer limit | Hypothetical bound | Result |
|---|---:|---|
| gate slots 4,000,000,000,000,000 | 104,354,177,530 | pass |
| measurements 47,471,340,504 | 664,584,110 | pass |
| coefficient rows 983,040 | 917,504 | pass |
| candidate checks `56 × (2^49+2)` | `55 × (2^49+2)` | pass |

These are arithmetic screens only, not certificate bounds, because the missing
uniform program can change all but the unchanged producer rows/checks.

## A.4 Build size, time and replay risk

The three `0b650bb` Entrant files contain 74,388 lines, but they are not a
self-contained replacement for the four old Parts.  Their recursive ECDSAAdd
import closure is 876 dependency files / 119,498 lines.  It overlaps 841 of the
848 old vendored modules, adds 35 modules (2,486 lines), and leaves only seven old
modules unused.  Including the three Entrant files, the donor closure is 879 files
/ 193,886 lines before the unchanged Streaming producer or any WEX adapter.

A straightforward source-gate-safe package is therefore about **225k–240k Lean
lines**, not 74k: roughly 119.5k dependency lines + 74.4k frontier proofs + 23.9k
producer + transport/compiler/final glue.  Selective pruning of the donor's many
intermediate variants is possible, but it is itself a proof-maintenance project.

For comparison, the current 159k-line WEX package took 357–683 seconds per module
under `--wfail` (about 46 minutes summed serially, about 11 minutes at peak
parallelism).  A packaged frontier port is estimated at **65–90 minutes serial**
or **15–30 minutes parallel** per cold strict build, with 54 GiB likely forcing
limited concurrency.  The intended validation would be per-module warning-failing
builds followed by `formal-tools/axioms.sh`; the full local `leanchecker` replay is
not viable on this 54 GiB host.

The official replay risk is high.  The smaller 159k WEX base already measured
64.839897 GiB.  A crude source-size scaling for 225k–240k gives about **92–98 GiB**,
above the 78 GiB gate.  Lean memory is not linear in lines, but the margin permits
only about 20% growth while the unpruned package grows 41–51%.  A viable redesign
would need both uniformization and aggressive declaration/source pruning before
an official replay attempt.

Estimated implementation effort is **XL, about 3–6 focused agent-weeks**: design a
fixed classifier/pivot circuit; decompose every derived constant into permitted
fields and literals; recover coherent specialization and transport; reprove exact
resources/support; then prune enough declarations to address replay memory.  The
best next experiment, if W1 is reopened, is a tiny parametric `affineInputWith`
replacement that proves a fixed program for two 8-bit table words.  Do not reopen
the full Entrant until that fixed-shape pivot and a protected-field implementation
of the fast constant cells both exist.

## Validation performed

- donor clone stayed read-only at `0b650bbf0704ddf4ead0b4c17760d1fc6fb3c585`;
- bench stayed clean at `60ccc81b86468327907715195f2a28680d9873f3`;
- module/import-closure and source-diff audits were read-only;
- `python3 workspace/wex_swap.py` passed all assertions;
- no Phase-B build, axioms, boundary, score or snapshot was run after the no-go verdict;
- needed bench `git add`s: none, because Phase B made no Entrant file;
- submissions remain on hold; no `yukon submit` was run.
