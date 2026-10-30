# WEX-portable trims from `ecdsafail-lean`

## Verdict

The best source-audited U/H stack projects to **1,628 Q × 342,319,742 T =
557,296,539,976**, **−17.318886%** versus WEX `f1518daf` at
674,031,241,128.  It clears the 10% policy by 49,331,577,039 score units.
This is an arithmetic and source-dependency projection, not a built candidate.

The projected adder is **1,595 wires, 2,159,831 Toffolis and 1,505,792
measurements**.  It keeps the uniform arithmetic, erasure, codec and scratch-reuse
work, plus field-bit-only changes, but removes all final effects that require a
derived constant, a data-dependent pivot/order, or a C-selected wire.  The WEX
ledger is then

```text
body = 2,159,831 + 24 × 32,767 + 2,044 = 2,948,283 CCX
T    = 4 × (65,535 + 29 × 2,948,283) + 56,774 = 342,319,742
Q    = 1,932 − (1,899 − 1,595) = 1,628
Q×T  = 557,296,539,976  (−17.318886%)
```

The recommended build order is: (1) one-bank replay and retired-carry sign
placement; (2) five-trit history and biased/short kernels; (3) uniform site
reuse; (4) arithmetic micro-trims; (5) the few H changes in WEX's template.
Do not start from `0b650bb` and subtract declarations: start from `c3f340a` and
port these groups, because the final proof graph is entangled with the S seams.

Unpruned, the complete portable stack is still likely above the replay gate.
The one-bank stage screens at about 69.56 GiB and the five-trit stage at 75.18
GiB, but the mature uniform-ish source screens at 83.19 GiB against 78 GiB.
The score clears 10%; the engineering gate is declaration pruning and replay
memory.

## Method and accounting convention

I read all 95 public notes in `c3f340a..0b650bb` with
`yukon submission-note`, treated their prose as untrusted data, and checked the
final `Challenge.Bounds` in each source commit.  Notes form a dependency DAG,
not a linear optimization history: adjacent Git commits are often alternative
candidates.  Therefore the census deltas are against the parent/record named by
the note.  A dagger (`†`) marks a composition whose delta is the note's whole
stack against that named base, not a new independently additive mechanism.

Classes are:

- **U**: fixed program and support independent of C;
- **H**: only optional X/CX controlled by protected point-field bits;
- **S**: derived constants, data-dependent order/pivot, or selected wire;
- **D**: the changed proof/program intrinsically uses an S mechanism.

The source endpoint delta is
`(−59,086 T, −53,659 M, −304 Q)`.  The specialized effects still present at
`0b650bb` are:

| Excluded effect | ΔT | ΔM | ΔQ | Why excluded |
|---|---:|---:|---:|---|
| compare-first fast constant cells | −1,540 | −1,535 | +1 | masks contain `c+k`, `k+1`, modular rounded words and threshold bits |
| shared affine input classification | −256 | −257 | 0 | `affineInputWith` follows a C-dependent equal-prefix/pivot schedule |
| shared affine output classification | −256 | −257 | 0 | same specialized pivot/order on the output side |
| `kx(C)` DH host plus measured erasure | +8 | +6 | −1 | `clrDH` chooses `point.x[kx C]`; +14 T host followed by −6 T measured erase |
| fused division entry | −254 | −254 | 0 | `EntryFuse`/`fusedY` use half-rounded masks and a derived threshold |
| flipped-square offset | −256 | −255 | 0 | Step 5 uses `3cx − (2^163−1)`, not a protected raw field |
| **net S effect** | **−2,554** | **−2,552** | **0** | fast-constant +1 Q and DH-host −1 Q cancel only in the donor endpoint |

Subtracting that S net from the endpoint delta leaves the portable U/H delta
**(−56,532 T, −51,107 M, −304 Q)**.  Applying it to WEX's adapted
2,216,363-T / 1,556,899-record / 1,899-site adder gives the verdict above.
`workspace/wex_trims.py` asserts every integer.

## Where the qubits went

Almost the entire 1,899→1,594 headline is portable:

- **255 U wires**: `12159df8` moves late integer signs into retired carry slots
  and runs field replay with one carry bank.
- **34 U wires in the accepted five-trit composition**: `216e92b5` replaces
  170 three-trit packets by 102 five-trit packets.  The note attributes 33 net
  sites to the checkpoint/placement itself; the composed support gains one more.
- **15 U/H wires**: flag lifetime reuse, dead-pool labels, selector hosting on
  fixed terminal history bits, finite-flag hosting, endpoint/square temporal
  scratch reuse, and dead arithmetic labels.
- **1 S wire**: `84721426`/`1c30cc8f` hosts pool site 1540 on `doubleSelect`
  only after `clrDH` clears flags through the C-selected wire `point.x[kx C]`.

Thus the best presently evidenced fixed-shape support is **1,595**, not 1,594.
The many dead-label and temporal-reuse cuts are real U cuts; the large qubit
gain is not inherently tied to the specialized classifier.

## WEX interactions

The projection deliberately retains WEX's **24 traversals**, its finite/X/low-Y
parity sharing, the finite/infinity polarity bridge, and the one-row
negative-double corner.  It also retains the current +2,045 arithmetic/record
adaptation over donor `c3f340a`; this is why the portable arithmetic is
2,159,831 rather than the donor-only 2,157,786.

- The one-bank, five-trit, kernel, codec, square-internal and fixed-label reuse
  changes do not alter lookup fields.  They should sit below `finiteT` and keep
  24 traversals.
- H changes to `pairEqual`, enable flags, and low-Y tails touch the same
  finite/X/low-Y leaves that WEX parity-shares.  Regenerate `wFiniteOne` and
  `wFiniteTight`; do not add their note deltas blindly.  The projection leaves
  WEX's existing parity ledger unchanged, so it does not claim a second saving.
- The one-row negative-double corner is outside the donor's ordinary finite
  program.  Keep WEX's corner and reprove its support against the smaller pool.
- The `kx(C)` host cannot be replaced by a lookup hole: holes may omit X/CX on
  fixed targets, not choose a target.  Its one-wire cut is excluded.
- Fast-constant, reflected-square/offset and fused-entry changes need derived
  masks not supplied by `PointCoeff`.  They are excluded even when their
  Toffoli count is attractive.

## Recommended build order and effort

| Phase | Source line | Expected result | Effort | Stop condition |
|---|---|---|---|---|
| 1 | `12159df8` one-bank replay | −255 adder wires; +265,710 T before later short kernels | **L, 4–7 days** | fixed-shape native program, support and counts compile under old WEX classifier |
| 2 | `216e92b5`, `013bbada`, `65eb65c4` | five-trit history, biased/short kernels; about −34 more wires and recover the one-bank T surcharge | **XL, 1–2 weeks** | strict modular build and projected replay below 78 GiB |
| 3 | selector hosts, finite spare, Q2/Q3/Q4/Q5 fixed scratch | approach 1,595 adder wires | **L, 4–7 days** | every host is a public fixed label; no `kx`, pivot or derived mask in the emitter |
| 4 | square, endpoint, terminal-tick, carry and codec trims | reach about 2,159,831 arithmetic Toffolis | **XL, 1–2 weeks** | exact resource ledger reproduces `workspace/wex_trims.py` |
| 5 | H tails/enables in WEX template | small T/support cleanup, possibly altered by parity sharing | **M, 2–4 days** | 24-traversal geometry and one-row corner rechecked |
| 6 | prune and replay | package only declarations in the certificate closure | **XL, 1–2 weeks** | measured replay <78 GiB with at least 3 GiB margin |

The first meaningful decision point is after Phase 2.  It already captures the
dominant qubit win and its unpruned linear memory screen is about 75.18 GiB.  If
that replay is not below roughly 74–75 GiB, the mature stack has no safe memory
path without more aggressive source splitting/pruning.

## Lean size and replay headroom

| Donor snapshot | Entrant lines | Net over `c3f340a`'s 2,288 | Linear WEX replay screen |
|---|---:|---:|---:|
| `12159df8` one-bank | 13,889 | +11,601 | 69.56 GiB |
| `216e92b5` five-trit | 27,685 | +25,397 | 75.18 GiB |
| `3f5db79f` mature uniform-ish composition | 47,335 | +45,047 | 83.19 GiB |
| `0b650bb` full frontier | 74,388 | +72,100 | 94.21 GiB linear; Brief 29's closure estimate was 92–98 GiB |

The linear screen uses 64.839897 GiB at 159,214 WEX lines.  It is only a risk
indicator—Lean memory is not linear—but it shows that the roughly 13 GiB
headroom can absorb the one-bank and probably the five-trit stages, not an
unpruned mature port.  A viable full U/H package should target **≤25–30k net new
lines**, replacing old vendored sections instead of retaining both variants.

## Per-commit census

`ΔT/ΔM/ΔQ` are note-relative as described above.  Compact dependency names are
submission/commit prefixes from the public notes.

| Commit | Author | Note title | ΔT | ΔM | ΔQ | Class | Reason / dependencies |
|---|---|---|---:|---:|---:|:---:|---|
| `b870b60a` | i34-9 | compare-first controlled constant adders | −1,540 | −1,535 | +1 | S | derived constant masks; base paired-comparison tree |
| `9c520f87` | i34-9 | tighter site certificate over compare-first generic | 0 | 0 | −1 | D | dead site proof is tied to S `FastConst`; `567d1308` |
| `5fe78bd4` | e-man07 | compare-first + 1,898-site + shorter comparisons | −4 | −4 | −1 | D | composite on `567d1308`; comparison part alone is H |
| `160bdd3b` | i34-9 | enable flags folded into control | 0 | 0 | −3 | D | structural flag cut built around S generic; `567d1308`, `7c5a6684` |
| `e2c22299` | e-man07 | sign-grouped streamed square | −4,080 | −4,080 | 0 | U | reorder fixed fold list; portable square kernel |
| `df1b5ff0` | e-man07 | sign-grouped square + finite-free comparisons | −4,084† | −4,084† | 0 | D | U square/H comparisons composed on S-enabled line |
| `910aec09` | i34-9 | relabelled arithmetic shares square pool site | 0 | 0 | −1 | U | fixed permutation and dead-label removal |
| `54279079` | kshitij-hash | one-Toffoli C/−C pair tail | −2 | 0 | 0 | H | only protected low-Y bits; needs WEX parity rebase |
| `6f871c1f` | i34-9 | square without final reflection | −255 | −255 | 0 | S | following step uses derived `3cx−1` |
| `0dc9d798` | e-man07 | accumulated folds in streamed square | −18,184 | −18,186 | 0 | U | fixed integer accumulator schedule |
| `6774aec9` | kshitij-hash | accumulated square + no reflection + fused tail | −257 | −255 | 0 | D | contains S reflected-constant step; H tail |
| `3a621ab3` | i34-9 | infinity flag shares generic-flag wire | +2 | 0 | −1 | U | fixed dynamic-flag lifetime reuse |
| `526de17e` | e-man07 | field endpoint conversions trimmed | −4,076 | −4,080 | 0 | U | zero/output invariants; literal arithmetic |
| `95ad6d99` | e-man07 | final reflection fused into `3cx` | −255 | −255 | 0 | S | derived `3cx−1` mask |
| `80ace126` | kaankolcu | endpoint trim + fused tails + reflection fusion | −257† | −255† | 0 | D | composite includes S reflection fusion |
| `d5b671c9` | kshitij-hash | endpoint trim + infinity/generic wire | +2 | 0 | −1 | U | disjoint U arithmetic and flag reuse |
| `0d5947ff` | e-man07 | infinity/generic wire on fused-reflection tree | +2 | 0 | −1 | D | support proof depends on S reflection tree |
| `687aaf5c` | kshitij-hash | flag re-encoding on no-reflection/fused-tail tree | +2 | 0 | −1 | D | candidate retains S no-reflection constant |
| `76498225` | e-man07 | measured erase of generic-select flag | −1 | +1 | 0 | U | predicate is dynamic finite/control state |
| `4a235894` | spariev | rotation-by-32 fold already canonical | −1,022 | −1,020 | 0 | U | uniform square range proof |
| `2f4863c1` | e-man07 | generic bit folded into `genericSelect` | 0 | 0 | −1 | U | fixed flag/lifetime relabelling |
| `62027093` | e-man07 | canonical rotation-by-32 on 1,893-site record | −1,022 | −1,020 | 0 | U | port of `c2f9a581` |
| `d9d1b9f3` | ercumentyildirim | finite-flag divisor repair | −1,020 | −1,016 | 0 | U | Clifford repair from dynamic finite flag |
| `d1ba8416` | spariev | canonical folds + seeded accumulators | −5,036 | −5,028 | 0 | U | fixed square arithmetic |
| `129669a7` | spariev | factor branch-B d corrections | −3,192 | −3,192 | 0 | U | fixed 33-bit temporary |
| `48524437` | ercumentyildirim | divisor repair + pool site 1804 removed | −1,020 | −1,016 | −1 | U | repair plus dead fixed label |
| `34bc4937` | e-man07 | 1,892-site + half endpoint + divisor repair | −2,042† | −2,036† | −1 | U | U composition on factored square |
| `d4614c55` | ercumentyildirim | site 1804 removed; single module | 0 | 0 | −1 | U | packaging/support-only fixed site cut |
| `5139f277` | e-man07 | 1,890-site + narrow field-cell fold | −1,020 | 0 | −1 | U | fixed label and cell-width trim |
| `ae69a0aa` | e-man07 | square order A,C,B | −255 | −255 | 0 | U | fixed branch permutation |
| `b66dbd8e` | kshitij-hash | LaneI + two square cuts | −511† | +1† | 0 | U | uniform lane/square composition |
| `c8e8854d` | e-man07 | first Karatsuba level in leaf squares | −8,230 | −8,486 | 0 | U | constant-independent square kernel |
| `a8094ab3` | e-man07 | measured branch-C Karatsuba sum | −256 | +256 | 0 | U | measured erasure with fixed correction |
| `e2125c44` | terrapinelf | last integer sign moves off own site | 0 | 0 | −1 | U | retired fixed carry slot |
| `eedbde06` | terrapinelf | last integer sign moves off own site (alternate) | 0 | 0 | −1 | U | same U support cut on alternate square |
| `3f1b530a` | e-man07 | 1,889-site + early-prefix accumulators | −264 | −264 | −1 | U | fixed early build plus dead sign site |
| `01c11910` | kshitij-hash | replay selectors on round-511 history bits | 0 | 0 | −2 | U | public fixed terminal labels |
| `fc9505c8` | kshitij-hash | narrowed integer passes + early-prefix square | −2,304 | −1,284 | 0 | U | fixed tick widths |
| `9fc17c5d` | e-man07 | second Karatsuba level | −3,134 | −3,134 | 0 | U | uniform leaf-square kernel |
| `95b00d20` | e-man07 | narrowed integer passes on K2 square | −2,040 | −1,020 | 0 | U | fixed tick widths |
| `4b5b430d` | ercumentyildirim | field selectors on idle labels 511/512 | 0 | 0 | −2 | U | fixed terminal-history hosts |
| `b917a63f` | ArthurOstapenko | one-bank field; late signs in retired carries | +265,710 | +265,196 | −255 | U | dominant portable Q cut; base 1,892-site line |
| `dc234327` | ArthurOstapenko | shared affine input classification | −256 | −257 | 0 | S | `affineInputWith` C-dependent pivot/order |
| `0d2f5fa4` | e-man07 | square/integer/site stack on one-bank tree | −11,563† | −11,043† | 0 | U | uniform square and integer composition on `12159df8` |
| `fe0a43dc` | kaankolcu | measured square + shared input classifier | −256 | −257 | 0 | D | composition includes S input classifier |
| `f017fde5` | e-man07 | selector hosted on label 511 | 0 | 0 | −1 | U | fixed idle history bit |
| `d5ede54c` | GordoAR | five-trit history with one-bank replay | +16,700† | −7,059† | −34 | U | 102 packets; composite versus `12159df8` |
| `dbdb358e` | e-man07 | Karatsuba square on five-trit record | −10,788 | −10,780 | 0 | U | uniform square transplant |
| `88c35de7` | ArthurOstapenko | biased single-bank kernels | −260,100 | −260,100 | 0 | U | recovers one-bank surcharge uniformly |
| `313e9b19` | e-man07 | biased kernels + Karatsuba square | −259,080† | −260,100† | 0 | U | composition on five-trit tree |
| `258df326` | e-man07 | narrowed integer passes on biased five-trit | −2,040 | −1,020 | 0 | U | fixed tick widths |
| `7ceb54db` | e-man07 | selectors on idle 511/1542 | 0 | 0 | −2 | U | fixed terminal-history hosts |
| `5733eeb6` | spariev | 34-T five-trit codec | −1,632 | 0 | 0 | U | remove two unreachable codec CCX on legal trits |
| `53dcb83c` | ercumentyildirim | transcript windows without enable bit | −2,040 | 0 | 0 | U | dynamic generic flag; fixed window program |
| `d542f4e1` | terrapinelf | 19-T measurement-free five-trit codec | −12,240 | 0 | 0 | U | reversible fixed codec |
| `e00099d3` | e-man07 | 19-T codec + selector-free windows | −2,040 | 0 | 0 | U | disjoint U merge |
| `f4e6a836` | jungjipdo | 13-T five-trit codec | −4,896 | 0 | 0 | U | fixed reversible codec |
| `72d11def` | e-man07 | 13-T codec + selector-free windows | −2,040 | 0 | 0 | U | disjoint U merge |
| `035936e9` | ercumentyildirim | finite flag hosts a pool site | +510 | +510 | −1 | U | dynamic finite flag; fixed host |
| `b49629e7` | ArthurOstapenko | integer repairs + low-half K2 | −3,096 | −925 | 0 | U | fixed walk and square arithmetic |
| `e854d2eb` | jungjipdo | 12-T coherent five-trit codec | −816 | 0 | 0 | U | SAT-found fixed reversible pack |
| `b1b1f5d9` | e-man07 | integer repairs + finite spare | −2,586† | −415† | −1 | U | `−3096/+510`, disjoint U merge |
| `ffcc90b1` | spariev | short biased fold/unfold kernels | −1,020 | −1,020 | −1 | U | 1,021-T kernels plus fixed unused-port proof |
| `8ce1de20` | e-man07 | repairs + finite spare + short kernels + codec12 | −4,422† | −1,435† | −1 | U | uniform composite |
| `a3eb7854` | spariev | codec12, short kernels, two pool removals | 0 | 0 | −1 | U | additional fixed dead-site removal |
| `f8f36b62` | spariev | temporal endpoint/square scratch reuse | 0 | 0 | −1 | U | disjoint lifetime reuse |
| `71480f0e` | ArthurOstapenko | measured 9/11-T codec | −1,633 | +2,449 | 0 | U | fixed measured codec/phase repair |
| `f4194e64` | ArthurOstapenko | measured 9/11-T codec (Q2 composition) | −1,633† | +2,449† | 0 | U | same codec on scratch-reuse line |
| `4c71d083` | ArthurOstapenko | shared affine output classification | −256 | −257 | 0 | S | data-dependent `affineInputWith` pivot/order |
| `6cd5d2b2` | ercumentyildirim | two dead top carries removed | −1,020 | 0 | 0 | U | fixed cell invariant |
| `9bb6a162` | spariev | reuse clean-one port; fourth dead arithmetic label | 0 | 0 | −2 | U | fixed ports and dead-label proof |
| `4e3bbf80` | akki-rock05 | clear D/H; host site 1540 on `doubleSelect` | +15 | 0 | −1 | S | `clrDH` targets `point.x[kx C]` |
| `27987ff6` | spariev | measured codec + Q3 scratch reuse | −1,633† | +2,449† | −1 | U | uniform composition |
| `466ed218` | akki-rock05 | site 1540 on `doubleSelect` on Q4 | +14 | 0 | −1 | S | same C-selected `kx` host |
| `68dc9388` | spariev | measured codec with four unused fields | −1,633† | +2,449† | −2 | U | measured codec plus fixed omissions |
| `43af82e5` | e-man07 | measured codec + label reuse + dead carries | −1,024† | −4† | −2 | U | uniform composition |
| `a0bdc8c4` | akki-rock05 | measured codec on 1,595-site DH tree | −1,632 | +2,448 | 0 | D | codec U, candidate depends on S host |
| `7cdde25c` | e-man07 | deeper K2 leaf square | −516 | −516 | 0 | U | fixed square kernel |
| `e6013ee7` | akki-rock05 | branch-B accumulator split/early prefix | −684 | −684 | 0 | U | fixed square arithmetic |
| `a2af67c2` | ercumentyildirim | Edges wrapper + TopReuse + half converters | −241† | −258† | −1 | D | contains S output classifier and `clrDH`; U kernel parts separable |
| `776284d0` | akki-rock05 | dead top carries + 255-bit half converters | −1,024 | −4 | 0 | U | fixed arithmetic invariants |
| `4728e03e` | ercumentyildirim | two square-stage savings | −1,200 | −1,200 | 0 | U | fixed square schedule |
| `2876f15a` | pepedesigner | measured erase of DH gadget ancillas | −6 | +6 | 0 | D | gadget exists only with S `clrDH` |
| `e941df5c` | terrapinelf | square branches C,A,B | −512 | −510 | 0 | U | fixed square permutation |
| `ecbf0066` | spariev | Q5 top-carry + square order + DH erase | −514† | −499† | −1 | D | composite includes S DH host/erase; Q5 carry reuse itself is U |
| `25111348` | e-man07 | square ends reflected | −256 | −255 | 0 | S | following constant becomes derived `3cx−1` |
| `fb8c8152` | ercumentyildirim | reflected square + 255-bit converters | −260 | −259 | 0 | D | −256 S reflection, −4 U converters |
| `5e8f293f` | ercumentyildirim | last multiplication swap only uncomputes | −256 | +256 | 0 | U | fixed measured erase |
| `9c2bcec1` | kaankolcu | measured last swap + forced terminal ticks | −268 | +256 | 0 | U | fixed public terminal states |
| `0a6022ae` | terrapinelf | copied-carry divide endpoint + terminal ticks | −266 | 0 | 0 | U | fixed endpoint invariants |
| `2863be67` | kaankolcu | fused division entry + endpoint/swap/ticks | −776† | +2† | 0 | D | only −254/−254 is S `EntryFuse`; remaining −522 T is U |
| `a9b9591e` | spariev | measured affine exit/entry fusion + ticks | −6 | −255 | 0 | D | fusion built on S `EntryFuse`/derived masks |
| `129f3642` | ercumentyildirim | every square fold uses reflected core | −256 | −255 | 0 | S | absorbs `2^163−1` into derived `3cx−offset` |
| `22a57ca3` | ArthurOstapenko | fused boundaries + terminal cleanup + carries | −804† | −550† | 0 | D | composite includes S fused boundary |
| `0b650bbf` | akki-rock05 | all 12 folds switch + copied diagonal carries | −298 | −297 | 0 | D | −256/−255 is S offset; −42/−42 leaf-carry trim is U |

## Reproduction and validation

- `python3 workspace/wex_trims.py` passes all exact assertions.
- Donor clone was read-only at `0b650bbf0704ddf4ead0b4c17760d1fc6fb3c585`.
- WEX bench was read-only and clean at `60ccc81b86468327907715195f2a28680d9873f3`.
- No Lean build, boundary check, score, snapshot, submission, push or commit was run.
- Submissions remain on hold.
