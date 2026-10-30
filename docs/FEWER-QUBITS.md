# Fewer qubits on `f7419f1`

## Verdict

**Do not build a fewer-qubit stack patch yet.**  The leader has no unused physical
owner at its binding arithmetic phase.  During either measured EEA wrapper, the
580-role EEA allocation, the 256-bit data bank, root 836, infinity 838, all 16
address/sign wires, and compiler ancilla 1024 account for all 855 wires.  The
groups that look idle by *point-add role* are already holding EEA roles then.

The only immediately constructible one-wire cut is to remove the temporary-AND
compiler and use its 854-wire parent.  Its certified bound is

`854 × 15,258,353,144 = 13,030,633,584,976`,

which is **32.380951297% worse** than the leader.  At 854 wires a competitive
build may add at most **13,480,811 T**, or 2,696,162 compiled CCX at 5 T each.
The parent adds 3,745,739,760 T.  Thus the downward marginal curve crosses the
economic limit on its first source-backed wire.

The ecdsa.fail techniques explain how 660--849-wire *different algorithms* were
made, but they do not supply an exact worst-case T receipt that can be pasted
onto this layout.  The local techniques which do transfer exactly--workspace
exchange, in-place divide/multiply, measured erasure, a borrowed flag, and one
persistent address/Fourier bank--are already present.  Packed rings, lane loans,
counter recoding, spooky checkpoints, and the v3 835-wire claim all require a
new EEA or a substantial source migration.  Assigning them a numerical T cost
would be fabrication.

Accordingly the recommended stack is unchanged: **zero Brief-21 patches**.  The
best next work is an XL feasibility branch for a genuinely smaller EEA, with the
per-qubit acceptance ceilings below used as hard stop conditions.

## Accounting convention

This note uses certified worst-case `tModel`, not ecdsa.fail's average executed
Toffoli metric.  A literal CCX retained under the leader's compiler is priced at
5 T.  Measurements and reset are priced at 0 T but still consume records.  The
challenge qubit metric is the union of labels, not the maximum number of
nonzero bits at a clock tick.  “Live” below therefore means that a label has a
coherent role whose clean/borrow contract would have to be proved before it can
be shared.

The exact integer calculations and census assertions are in
`workspace/fewer_qubits.py`.

## Wire census

### Physical union

The parent reset list is

```text
0..836, 838, 855..870                              854 wires
+ 1024 (temporary-AND compiler ancilla)              1 wire
                                                    ---------
                                                      855 wires
```

Wire 837 was the old zero flag and is absent after the root loan.  Logical
address/sign labels 839..854 are relocated to physical 855..870.  No other
label is in the final reset list.  The final reset itself touches all 854 parent
labels, so deleting gates without changing that list cannot lower Q.

There are two useful views of the same labels:

| Logical group | Physical labels | Count | Lifetime in a corrected window |
|---|---:|---:|---|
| accumulator x | 263..518 | 256 | From the direct first window through final reset.  It becomes an in-place EEA/multiply operand; it is not idle during arithmetic. |
| accumulator y | 580..835 | 256 | Same persistent interval.  It is the EEA data bank and is exchanged with the work bank where required. |
| accumulator infinity | 838 | 1 | Persistent point-state bit; also participates in the high 257-bit IPX zero test. |
| EEA phase/iteration/sign | 0..3 | 4 | Live throughout each 1,620-step EEA schedule; the same labels later become the four IPX flags. |
| EEA work1 | 4..262 | 259 | Allocated through EEA forward/reverse wrappers.  Label 4 later becomes the IPX half-test bit and 5..259 its scratch. |
| EEA work2 | 263..521 | 259 | Allocated through EEA.  It overlays x=263..518 and lookup-path labels 519..521. |
| EEA length T/Q/S/R′ | 522..557 | 4×9 = 36 | Live schedule metadata.  Labels 522..533 overlay the rest of the lookup path. |
| EEA aux/control/rotation | 558..579 | 22 | Control 558, shift epoch 559, source scratch 560..577, and repair suffix 578..579. |
| multiply work bank | principally 7..262 | 256 | Used by multiply-to-work and its inverse; no separate allocation.  At the tight sites only 25 clean lanes remain elsewhere. |
| multiply data bank | 580..835 | 256 | Used in place.  The other multiply sites have 68 clean lanes, but those are labels already required by EEA and point state. |
| lookup path | 519..533 | 15 | Live only inside a table traversal and clean around arithmetic; during EEA the labels are work2/length owners. |
| lookup root / borrowed arithmetic flag | 836 | 1 | Persistent enabled root around lookup.  `swap 836 837` makes it the division/multiplication zero flag, then restores the root. |
| IPX flags / half / scratch | 0..3 / 4 / 5..259 | 4+1+255 | Clean until the post-coordinate correction; used for four flag tests and cleaned afterward.  Every label is already an EEA owner at the peak. |
| address bank | 855..869 | 15 | Prepared before the window body, coherent through all lookups and arithmetic, inverse-Fourier transformed, then measured/reset. |
| sign / 16th Fourier lane | 870 | 1 | Same lifetime.  Width-15 windows leave physical 869 unused locally, but width-16 windows require it and Q counts the union. |
| compiler ancilla | 1024 | 1 | Clean between lowered literal CCX gadgets and active inside each gadget, including CCX in the EEA peak. |

The 513 accumulator labels are x (256), y (256), and infinity (1).  “EEA
work2” and “accumulator x” are intentionally overlapping descriptions: the
leader already implements the desired register sharing rather than keeping a
point register next to a disjoint arithmetic register.

### Window schedule and lifetimes

The outer program has one direct window followed by 30 corrected windows.  A
corrected window has this order:

1. prepare the 15/16-bit address-sign bank and apply signed-address encoding;
2. lookup `−x`, signed lookup `−y`, in-place division;
3. square/subtract, lookup `3x`, in-place multiplication;
4. x negate/lookup, y negate/lookup, then the flag-only IPX correction;
5. final y negate, undo signed-address encoding;
6. inverse Fourier on the same bank and measure/reset it.

The accumulator survives the entire 31-window round.  The address bank is live
from step 1 through step 6.  Lookup path labels are clean outside each lookup,
and IPX labels are clean before correction, but those same physical labels hold
EEA work and metadata in steps 2--3.

### Binding phase

The binding coherent allocation is an EEA wrapper inside division or
multiplication:

| Owner at the EEA phase | Count |
|---|---:|
| EEA roles 0..579 | 580 |
| live y/data bank 580..835 | 256 |
| borrowed flag/root 836 | 1 |
| live infinity 838 | 1 |
| coherent address/sign bank 855..870 | 16 |
| active compiler ancilla 1024 | 1 |
| **total** | **855** |

No whole group is idle.  The lookup *role*, IPX *role*, and Fourier operation
are idle, but their labels respectively hold EEA work/length state, EEA
phase/work state, and the still-coherent selected address.  This is the same
flat-cap lesson found in the spooky lab: freeing wires in only the multiply,
lookup, correction, or end-of-window phase does not lower the circuit union.

## Mapping the low-qubit techniques

“Incremental ΔQ” is relative to `5d39a5f`, not relative to an unshared textbook
layout.  “Exact T” is given only when the present source or an exact local gate
identity determines it.  Unknown is a result: the archived entries use a
different arithmetic algorithm, average cost, approximate cuts, or all three.

| Technique | Exact mapping to this leader | Incremental ΔQ | Exact worst-case ΔT | Verdict |
|---|---|---:|---:|---|
| Borrow an enabled/dirty flag | Already implemented: lookup root 836 is exchanged with removed flag 837 around division and multiplication. | 0 now; −1 already realized | 0 | Exhausted local win. |
| EEA/multiply register sharing | Already implemented by `eeaWorkspaceExchange`; x/work and y/data roles overlay rather than coexist. | 0 now; 256 labels avoided versus a disjoint design | 0 | Exhausted at this abstraction. |
| In-place arithmetic | Division and multiplication already consume/restore the point-data banks in place. | 0 | 0 | No separate result register to delete. |
| IPX correction owner reuse | Flags 0..3, half 4, scratch 5..259, path 519..533, root 836 and accumulator labels are all recycled EEA/lookup owners. | 0 | 0 | The prior “loan correction into arithmetic” proposal is already realized. |
| Clean MCX bank | Frogdrop adds 4--12 clean lanes to replace dirty chains.  The leader already has clean V-chain scratch when its equality runs; adding a dedicated bank is the opposite direction. | ≥0 | For k controls, clean is `2k−3` CCX and dirty is `4(k−2)`; the exact clean advantage is `(2k−5)×5 T` per *unitary* call. | Useful only as Q-for-T, not T-for-Q. |
| Replace clean equality scratch by dirty donors | IPX uses 255 scratch labels for 257-bit tests, but those labels remain mandatory EEA work1 owners.  Deleting the IPX use therefore deletes no physical label.  Its measured-uncompute schedule also is not the archived unitary dirty chain. | 0 | No applicable replacement; the unitary comparison alone is `509×5=2,545 T` per equality, not a price for the measured leader circuit. | Reject: positive T for zero Q. |
| Conditional lane loans / “borrow passenger lanes” | At the EEA peak the prospective passengers contain EEA state, the point data, the selected address, root, or infinity.  The 25/68 clean multiply-site counts are local and use labels needed elsewhere. | 0 established | Unknown for a new EEA; no legal current loan | Requires a new per-site dirty-borrow arithmetic proof. |
| Affine counter/length recoding | Could target the four 9-bit length registers or phase fields, but the 1,620-step reachable-state theorem uses the full current representation. | Unknown, plausibly single digits | Unknown | L/XL; prove range and all update/reverse contracts first. |
| Packed three-of-four Euclid state / packed cofactor rings | This is the core of the 660--700q lineage, not a relabeling of `indexedStepProductionRegisters`. | Unknown; potentially tens/hundreds | Unknown | XL algorithm replacement. |
| Half cofactor/value rings and reciprocal sessions | Frogdrop's ring258/Q128/payload geometry and column sessions do not correspond to the leader's 580-role fixed EEA. | Unknown | Unknown | XL migration; mean ecdsa.fail counts are unusable here. |
| In-place quotient sessions / junk parking | Already conceptually present where source invariants permit it.  Archived “active-shot clean” lanes are not uniformly clean for every challenge input. | 0 established | Unknown | Needs universal source invariant, not corpus evidence. |
| Measured erasure / MBU | Already used in EEA and IPX equality tails.  Additional erasure can lower T or records, but a measured bit is not a deleted physical owner unless all binding plateaus release it. | 0 established | 0 for each *proved* coherent AND erase; opportunity count unproved | Continue as a T lever, not a current Q lever. |
| Spooky measure-and-recompute | The spooky checkpoint saves 71--78 data wires in the archived multiply but adds about 65.2k model T there; its divide remains the peak.  This leader has a different EEA and the same structural problem: division already fills the cap. | 0 on the full circuit | No transferable exact count | Reject as a patch; reopen only after a divide-width cut. |
| Address-bank folding | One 16-wire bank is already reused by every axis/window.  It must remain coherent during the EEA.  Wire 869 is locally clean in 15-bit windows but used in 16-bit windows. | 0 | No legal cut | A new mixed-radix/window schedule and decoder proof would be XL. |
| Fourier-bank reuse | Fourier acts after coordinate arithmetic, but the bank stores the address during arithmetic.  Arithmetic scratch cannot host it at the binding phase. | 0 | No legal cut | Already maximally time-shared. |
| Repair-suffix loans (578..579) | The two labels are a certified-remainder repair suffix, but no currently unique group is idle exactly over all their live sites; removing a use without removing reset/support does not change Q. | 0 established | Unknown | Small search target, not a priced build. |
| Temporary-AND compiler removal | Exact parent build: remove physical 1024 and do not lower the parent entry. | **−1** | **+3,745,739,760 T** in the certified bound | Exact but catastrophically past the 13,480,811-T budget. |
| Dynamic compiler-ancilla loan | Would need a clean or suitably dirty owner at every lowered literal CCX.  The EEA census shows none at the binding sites. | Unknown; target −1 | Unknown; must be ≤13,480,811 T total | XL and unlikely without changing EEA. |
| v3 advertised 835-wire layout | Not present as an exact entrant on this checkout; the bench pins the v2 construction. | Unverified target −19/−20 | Unknown | Separate XL source/proof migration, not a stack patch. |
| Approximate top-bit/carry/window cuts | The low-q entries often rely on corpus failure rates, average cost, or unsupported window containment. | Not admissible | Not admissible | Excluded by the all-secret ≥99% certificate. |

The exact identity behind the MCX rows remains useful for a future design, but
it must not be multiplied by an archived average call count.  In particular,
the low-q notes' 660/664/668/675 results and the 815/825/849 results certify
their own benchmark streams, not this circuit's worst-case Straight program.

## Downward marginal curve

For each q, the table gives:

- the largest integer T bound with `q×T` *strictly* below the leader score;
- the total T premium permitted over 11,512,613,384;
- the score if T could remain unchanged.

The last column is the best status supported by an actual current-source
construction.  “Unestablished” does not claim impossibility; it refuses to turn
an algorithm sketch into a score.

| q | Strict T ceiling | Added-T budget | Score at unchanged T | Best substantiated point |
|---:|---:|---:|---:|---|
| 855 | 11,512,613,383 | −1 | 9,843,284,443,320 | leader itself |
| 854 | 11,526,094,195 | 13,480,811 | 9,831,771,829,936 | parent: 13,030,633,584,976 |
| 853 | 11,539,606,615 | 26,993,231 | 9,820,259,216,552 | unestablished |
| 852 | 11,553,150,755 | 40,537,371 | 9,808,746,603,168 | unestablished |
| 851 | 11,566,726,725 | 54,113,341 | 9,797,233,989,784 | unestablished |
| 850 | 11,580,334,639 | 67,721,255 | 9,785,721,376,400 | unestablished |
| 849 | 11,593,974,609 | 81,361,225 | 9,774,208,763,016 | unestablished |
| 848 | 11,607,646,749 | 95,033,365 | 9,762,696,149,632 | unestablished |
| 847 | 11,621,351,172 | 108,737,788 | 9,751,183,536,248 | unestablished |
| 846 | 11,635,087,994 | 122,474,610 | 9,739,670,922,864 | unestablished |
| 845 | 11,648,857,329 | 136,243,945 | 9,728,158,309,480 | unestablished |
| 844 | 11,662,659,293 | 150,045,909 | 9,716,645,696,096 | unestablished |
| 843 | 11,676,494,001 | 163,880,617 | 9,705,133,082,712 | unestablished |
| 842 | 11,690,361,571 | 177,748,187 | 9,693,620,469,328 | unestablished |
| 841 | 11,704,262,120 | 191,648,736 | 9,682,107,855,944 | unestablished |
| 840 | 11,718,195,765 | 205,582,381 | 9,670,595,242,560 | unestablished |
| 839 | 11,732,162,626 | 219,549,242 | 9,659,082,629,176 | unestablished |
| 838 | 11,746,162,820 | 233,549,436 | 9,647,570,015,792 | unestablished |
| 837 | 11,760,196,467 | 247,583,083 | 9,636,057,402,408 | unestablished |
| 836 | 11,774,263,688 | 261,650,304 | 9,624,544,789,024 | unestablished |
| 835 | 11,788,364,602 | 275,751,218 | 9,613,032,175,640 | unestablished |
| 834 | 11,802,499,332 | 289,885,948 | 9,601,519,562,256 | unestablished |
| 833 | 11,816,667,999 | 304,054,615 | 9,590,006,948,872 | unestablished |
| 832 | 11,830,870,725 | 318,257,341 | 9,578,494,335,488 | unestablished |
| 831 | 11,845,107,633 | 332,494,249 | 9,566,981,722,104 | unestablished |
| 830 | 11,859,378,847 | 346,765,463 | 9,555,469,108,720 | unestablished |
| 829 | 11,873,684,491 | 361,071,107 | 9,543,956,495,336 | unestablished |
| 828 | 11,888,024,689 | 375,411,305 | 9,532,443,881,952 | unestablished |
| 827 | 11,902,399,568 | 389,786,184 | 9,520,931,268,568 | unestablished |
| 826 | 11,916,809,253 | 404,195,869 | 9,509,418,655,184 | unestablished |
| 825 | 11,931,253,870 | 418,640,486 | 9,497,906,041,800 | unestablished |
| 824 | 11,945,733,547 | 433,120,163 | 9,486,393,428,416 | unestablished |
| 823 | 11,960,248,412 | 447,635,028 | 9,474,880,815,032 | unestablished |
| 822 | 11,974,798,592 | 462,185,208 | 9,463,368,201,648 | unestablished |
| 821 | 11,989,384,218 | 476,770,834 | 9,451,855,588,264 | unestablished |
| 820 | 12,004,005,418 | 491,392,034 | 9,440,342,974,880 | unestablished |
| 819 | 12,018,662,323 | 506,048,939 | 9,428,830,361,496 | unestablished |
| 818 | 12,033,355,065 | 520,741,681 | 9,417,317,748,112 | unestablished |
| 817 | 12,048,083,773 | 535,470,389 | 9,405,805,134,728 | unestablished |
| 816 | 12,062,848,582 | 550,235,198 | 9,394,292,521,344 | unestablished |
| 815 | 12,077,649,623 | 565,036,239 | 9,382,779,907,960 | unestablished |
| 814 | 12,092,487,031 | 579,873,647 | 9,371,267,294,576 | unestablished |
| 813 | 12,107,360,938 | 594,747,554 | 9,359,754,681,192 | unestablished |
| 812 | 12,122,271,481 | 609,658,097 | 9,348,242,067,808 | unestablished |
| 811 | 12,137,218,795 | 624,605,411 | 9,336,729,454,424 | unestablished |
| 810 | 12,152,203,016 | 639,589,632 | 9,325,216,841,040 | unestablished |
| 809 | 12,167,224,280 | 654,610,896 | 9,313,704,227,656 | unestablished |
| 808 | 12,182,282,726 | 669,669,342 | 9,302,191,614,272 | unestablished |
| 807 | 12,197,378,492 | 684,765,108 | 9,290,679,000,888 | unestablished |
| 806 | 12,212,511,716 | 699,898,332 | 9,279,166,387,504 | unestablished |
| 805 | 12,227,682,538 | 715,069,154 | 9,267,653,774,120 | unestablished |
| 804 | 12,242,891,098 | 730,277,714 | 9,256,141,160,736 | unestablished |
| 803 | 12,258,137,538 | 745,524,154 | 9,244,628,547,352 | unestablished |
| 802 | 12,273,421,999 | 760,808,615 | 9,233,115,933,968 | unestablished |
| 801 | 12,288,744,623 | 776,131,239 | 9,221,603,320,584 | unestablished |
| 800 | 12,304,105,554 | 791,492,170 | 9,210,090,707,200 | unestablished |

The frequently quoted 13.46M T/wire is the tangent at 855.  The exact strict
budget grows slightly with each removed wire; the calculator uses integer
division against the fixed leader score.

## Build recommendations

There are no 1--3 defensible scoring builds yet.  The following is the ordered
decision list, including exact stop conditions rather than speculative scores.

| Priority | Candidate | Exact projected/certified result | Effort | Recommendation |
|---:|---|---|:---:|---|
| 1 | Empty Brief-21 stack on `5d39a5f` | **855 × 11,512,613,384 = 9,843,284,443,320**; 0% change | S | Keep.  This is the only competitive exact point. |
| 2 | Remove compiler ancilla (Parent comparison build) | **854 × 15,258,353,144 = 13,030,633,584,976**; **+32.380951297%** | S | Do not add to stack; useful only as a regression/control. |
| 3 | New 854-wire EEA/compiler co-design | Must prove `T ≤ 11,526,094,195`, giving score at most **9,843,284,442,530** (790 below leader).  No current construction meets this. | XL | Research branch only; stop as soon as its exact premium exceeds 13,480,811 T. |

If the v3 835-wire layout is obtained and its total compiled bound can be kept
at the current T, its conditional score would be 9,613,032,175,640
(2.339181287% below the leader).  That is a target, not a projection: it has a
total added-T allowance of 275,751,218, and no migrated term or certificate is
present.  It should be considered only after acquiring exact source and support
proofs.

## Evidence trail

The census is anchored in the bench definitions and support proofs:

- `Challenge/Reset.lean`: `resetWires` and its length 854;
- `EEA/IndexedStep.lean`: the dense 580-role production allocation;
- `EEA/WorkspaceReuse.lean`: the work/data exchange;
- `Window/PointStages.lean` and `Window/AddressBank.lean`: lookup path,
  address bank, and relocation;
- entrant `Streaming/Resources.lean`: `windowBaseSupport`, IPX labels and
  tests, arithmetic support, reset/complete support, and the root loan;
- entrant `Main.lean`: parent bound, compiler-added lower bound, final
  `lowerEntry 1024`, and the 855/11,512,613,384 certificate.

Technique mapping used the named ecdsa.fail notes summarized in
`ECDSAFAIL-TRICKS.md` and `ECDSAFAIL-855.md`, plus `SPOOKY-ON-09.md`,
`RELATED-WORK.md`, and the spooky lab's `docs/spooky-theory.md` and R005
profile.  Those sources are evidence for mechanisms and failure modes, not a
license to transfer their average or approximate resource figures.
