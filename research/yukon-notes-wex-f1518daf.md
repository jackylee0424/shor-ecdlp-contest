

Model: gpt-6.1-terra
Harness: Codex

# Sharing parity with the finite/X lookup

## Change

A corrected WEX addition tests whether its accumulator matches a selected
finite table point or its negative. Each of the two paired equalities first XORs
the row's infinity and X fields into the accumulator, computes a zero chain,
tests the low Y bit twice, erases the zero chain and restores the finite/X
fields. The preceding parity-sharing cut applies X when the positive-Y low bit is false before the first test, inserts a
literal X between the two tests, and applies X when the negative-Y low bit is
false after the second test. Each pair still uses four full
15-bit lookup traversals: two for finite/X and two for parity.

This candidate adds the first parity operation to the first finite/X lookup
leaf, and the last parity operation to the second leaf. The finite flag, X
word, and low Y bit are distinct targets under the existing window layout.
Every leaf continues to use the same permitted individual constant-field bits
and polarities, so no table field or protected lookup rule is changed. The
remaining zero-chain tail contains the same two CCX tests and intervening X.

Moving the parity operations outward crosses the zero-chain compute and its
measured erase. The low Y wire is disjoint from the chain's control, inputs and
workspace. It is also disjoint from the finite/X mask. The proof uses a
measured-program commutation lemma for disjoint supports: the same measurement
list can be used on both sides, including the corrections for every record.
The two orderings therefore have identical execution on every basis state and
every measurement list, not merely on a sampled point or a typical branch.
The paired test is still used only on the finite-addend invariant, where the Y
and negative-Y low bits are complementary. Their complement is proved from odd
field characteristic and nonzero Y; the enable assumptions exclude Y = 0.

Each paired equality now uses two traversals rather than four. There are two
such equalities per corrected addition, so this removes four more traversals
per addition, leaving **24**. No extra workspace wire is needed. The other
components remain four short-equality traversals, ten constant-load traversals,
and six corner point-mask traversals. The unchanged protected producer retains
29 corrected additions, its 266/208-bit samples, 55 wrapped-shift candidates,
and its success theorem for every nonzero secret.

## Proof method

The program is expressed in the same whole-mask WCode intermediate used by
WEX. The new combined leaf specializes to the old finite/X template followed
by the appropriate conditional parity X. A structural zero-chain decomposition
separates its compute prefix, final tests, and measured-erase suffix. The
component proof establishes that the parity wire is absent from each segment
from the inherited no-duplicate layout theorem. Conditional-X operations are
moved across these segments and the finite/X mask using the disjoint-program
commutation theorem. The comparison covers the whole arithmetic state,
including phase, and holds for arbitrary measurement lists.

At the pair level the specialized old and new programs have equal measurement
counts and identical execution for every state and record. The proof composes
both pair replacements with the remaining finite-addend schedule. On valid
rows the specialized tight program has the same execution and measurement
count as `finiteOneS`. This lets the inherited normalization theorem and the
lookup compiler's source simulation prove the same coherent point write across
all addresses and histories. The proof does not replace a coherent address
superposition by a classical single-address test: the compiler supplies a
single normalized coefficient family shared across the valid address bank.

Static placement is checked using the existing short-mask hypothesis, since the
new combined leaf has the same finite, X, and low-Y targets as that mask. Every
literal segment of the new row is also a literal segment of the preceding
28-traversal row; its physicality and support facts can be transported. The
literal slot sums and total leaf-port counts of the two rows agree. A structural
port-count proof computes exactly 7,702 leaf ports in the wrapped row. Its
record-cursor proof is factored through an abstract wrapper lemma to avoid
expanding the full concrete program during elaboration.

## Resource ledger

The arithmetic remains 2,216,363 literal CCX and 1,556,899 literal records per
corrected addition. The 24 lookups contribute 24 * 32,767 = 786,408 CCX and
records. Two signed-Y conjugations add 2,044 of each. Thus the complete body
has a raw upper ledger of 3,004,815 CCX and 2,345,351 records, and costs at
most 12,019,260 T after the global four-P lowering. Before lowering, the row
alone has 2,343,307 records and 21,019,397 T; the signed body has an unlowered
T upper bound of 21,033,705.

| Quantity | WEX parent | 28-traversal cut | This entry |
| --- | ---: | ---: | ---: |
| Traversals per addition | 32 | 28 | 24 |
| CCX upper ledger per body | 3,266,951 | 3,135,883 | 3,004,815 |
| Body records | 2,607,487 | 2,476,419 | 2,345,351 |
| Parent cursor | 75,718,100 | 71,917,128 | 68,116,156 |
| Unlowered source T bound | 663,706,571 | 637,099,767 | 610,492,963 |
| Final qubit bound | 1,932 | 1,932 | 1,932 |
| Final T bound | 379,285,230 | 364,081,342 | 348,877,454 |
| Measurement upper bound | 739,424,671 | 709,016,895 | 678,609,119 |
| Qubits × T | 732,779,064,360 | 703,405,152,744 | 674,031,241,128 |

Each additional removed traversal saves 32,767 eligible CCX and records. Four
removed traversals across 29 bodies save 4 * 29 * 32,767 * 4 = 15,203,888 T
and 29,373,911,616 in the score at 1,932 qubits. The final T formula is
`4 * (65535 + 29 * 3004815) + 56773 + 1 = 348877454`. The initial load,
Fourier/feedback allowance, catalyst preparation, and compact support bound
remain as in the WEX parent. The declared measurement bound is conservative:
it adds the source cursor and a source-T-based upper bound on inserted records.

## Provenance

The source descends from the compact WEX finite-addend assembly, promoted as
submission `6ee2945a-78ea-4d50-bb26-b2f9210b70d8`, and its local
28-traversal parity-sharing derivative. The finite point-addition arithmetic is
ECDSAAdd, an Apache-2.0 development pinned at
[c3f340a](https://github.com/Layr-Labs/ecdsafail-lean/tree/c3f340af8ef1cd0e25487e457fe1778c99f0beb9).
The Streaming producer and unary lookup descend from
[VerifiedQC/ShorECDLP](https://github.com/VerifiedQC/ShorECDLP/pull/551) and
[arXiv:2607.13816](https://arxiv.org/abs/2607.13816). The fixed 266/208-bit
producer and its 55-neighbor success proof descend from public submission
`c96133a0-eda7-4ce6-b4de-087f8588011a`. The rounding-window proof includes
public submission `da06e7d1-069a-4b86-9b8a-e55a4624c243`. The inherited global
compiler uses the measured-AND and Y-state lineage, including
`bcad5b2d-7db1-49b8-8fa6-9d9c92c80124` and
`791100e1-d660-48fa-a6cb-7c1bc7eaa62b`. Original notices are retained.

## Validation and reproduction

The complete five-module candidate passed a strict warning-as-error build. The
component checks establish two-traversal pair equivalence for arbitrary states
and records, complete finite-row equivalence, coherent normalized point-write,
literal support and slot bounds, the 2,343,307 row cursor, and the 7,702 leaf-port
count. The fast check result for the final committed tree is recorded below.

```text
Verified score=674031241128 (qubits=1932, tModel=348877454, measurements=678609119)
```

The fast check validates source hygiene, warning-free incremental compilation,
the acceptance type, permitted axioms and declared bounds. It does not run the
kernel judge or the Entrant-prefix replay. The five-module WEX base passed a
separate capped replay at 64.839897 GiB peak RSS with 32 workers, zero swaps and
exit zero; this is not a replay-memory measurement for the changed candidate.
Reproduction uses the locked Lean version and dependencies, a strict build of the
five Entrant modules and the protected challenge benchmark. The compiled resource
claims use the challenge T model and are not wall-clock or fault-tolerant
hardware estimates.

