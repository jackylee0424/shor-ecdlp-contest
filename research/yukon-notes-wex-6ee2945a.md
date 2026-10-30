

Model: gpt-6.1-sol
Harness: Codex

# WEX: one-row finite-addend arithmetic with a 29-addition Streaming producer

This entry replaces the corrected-window arithmetic in the certified Streaming
producer with a coherently selected finite-addend point-addition body. It applies
the reusable measured-AND compiler and Y-state kickback to the complete parent
program. The public point-addition contract, protected decoder, success threshold,
coefficient fields and cost model remain unchanged. The source is organized as
four unchanged vendored ECDSAAdd parts plus Main: five Entrant modules in total.

## Mechanism

The physical producer follows the c96133a0 construction: one 266-bit left sample,
one 208-bit right sample, 29 corrected additions and 55 explicitly declared
wrapped-shift decoder trials. The right trials are the center word and its 27
positive and 27 negative neighboring residues, all sharing the same left sample.
The success proof applies to their joint sample and does not assume independent
trials. It proves the protected verified-candidate success probability is at
least 99/100 for every nonzero query point Q = d G.

The schedule consists of a 16-bit first load, ten signed 16-bit and six signed
15-bit windows on the left, and thirteen signed 16-bit windows on the right.
The coefficient table uses exactly 65,536 + 23*32,768 + 6*16,384 = 917,504 rows,
within the 983,040-row limit. The signed windows share a 15-bit physical address
bank. The 15-bit logical signed windows reuse table rows through reindexing while
retaining that same physical lookup tree. The sign is on wire 870, low address
bits on 855 through 869, and persistent query control on 836. Accumulator x and y
remain on 263 through 518 and 580 through 835, with infinity flag on 838.

The WEX window uses the one-row finite-addend family from the ecdsa.fail arithmetic
integration. Its table-dependent constants come only from permitted field-bit
lookups. Each window performs 32 protected unary traversals. Literal arithmetic
comes from the vendored finite-addend program; the one-row negative-double corner
uses a modular Y negation before its masked point XOR. Two additional outer Y
negations conjugate the selected addition to the required signed action. Their
flag preparation and cleanup, point-polarity inversions, root inversions and
signed-address reflection use free Clifford instructions under the metric.

The body implements the coherent point write on the stated valid-input invariant.
The proof covers arbitrary address superpositions and every measurement record,
including the exceptional input points. It provides a shared branch coefficient
across addresses, which is needed for interference in the outer Fourier circuit.
The adapter satisfies the frozen Single.WindowBody contract, including activation,
point-write readiness, address-write readiness, first-load readiness, static
support, well-formedness and resource evidence. The producer consumes that contract
without changing its table, digit offsets, Fourier chain or protected decoder.

The compact export physically relabels the body without adding gates. Its sharp
source inventory has 1,898 native arithmetic sites, sixteen address/sign sites
and sixteen path/root sites. The 530 persistent point/control/address labels are
fixed. An explicit involution sends the remaining 1,400 source sites into clean
workspace labels 0–262, 519–579, 837, 839–854 and 871–1929. The first 325 of these
reuse the skeleton's clean work bank. The body restores that bank before return.
Its readiness predicate is the pullback of the original predicate through this
permutation, with all original readiness obligations proved. Protected physical
relabeling preserves every branch coefficient, the coherent point write, T cost,
record cursor and gate-slot count. The compact support is List.range 1930; fresh
compiler wires 1930 and 1931 bring the final support upper bound to 1,932. The
compiler-credit bridge proves that physical relabeling also preserves the zero
residue and exact eligible literal-CCX count.

## Compiler credit

Every charged body instruction is an unconditional literal CCX. Literal arithmetic
has no P instruction. Constant-field lookup leaves and measured corrections have
zero charged cost. The protected traversal contributes one literal CCX per
internal node, exactly 32,767 for a 15-bit tree. Sign adapters are either Clifford
or instances of the same measured modular-negation program.

WEXCredit proves zero structural residue and exact eligible-CCX counts for these
components, independently of the constant reader and incoming history. Append,
record-span cast and coefficient reindexing lemmas compose those facts. The final
body witness uses the actual normalized counts. Normalization can replace a CCX
with repeated controls by a CX, so the raw ledger is used only as an upper bound;
it is not used as a lower credit for the normalized program.

The global measured-AND compiler replaces each eligible literal CCX by four T or
inverse-T rotations plus an S rotation and a measured Clifford correction. It
reuses one clean ancilla, redirects every original record-controlled operation,
and maps all 55 decoder position vectors through the same record map. The
Y-state compiler then replaces the selected S rotations by Clifford kickback into
one shared catalyst. Its initial H and S preparation is charged once, at one
P-model unit. Each lowered CCX therefore costs four charged rotations. Both fresh
wires and all inserted records and gate slots are included in the certificate.

The generic transport preserves the full protected verified-candidate Born mass.
It applies after assembling the complete parent, including first load, Fourier
feedback, reset and neighboring-word suffix. The body contract and readiness
obligations are unchanged. The assembly glue is separate from WEX.body, and its
qubit bound is expressed through the compact body's proved 1,930-wire support.

## Resource ledger

The raw one-row finite arithmetic has 2,216,363 Toffolis. Thirty-two traversals add
32*32,767 = 1,048,544. The two outer modular Y negations add 2*1,022 = 2,044.
Thus a complete window has at most 3,266,951 eligible CCX after normalization.
At four charged rotations per eligible CCX, its compiled cost is at most
13,067,804 T-model units. The table-controlled leaves and sign/address adapters
add no charged P instruction outside that count.

| Quantity | Certified ledger or upper bound |
| --- | ---: |
| Raw arithmetic CCX per addition | 2,216,363 |
| Lookup traversals per addition | 32 |
| CCX per 15-bit traversal | 32,767 |
| Outer-negation CCX per addition | 2,044 |
| Complete-window CCX upper bound | 3,266,951 |
| Compiled T per addition | 13,067,804 |
| Corrected additions | 29 |
| First-load eligible CCX | 65,535 |
| Parent eligible CCX upper ledger | 94,807,114 |
| Fourier/feedback T allowance | 56,773 |
| Shared Y-state preparation T | 1 |
| Final T upper bound | 379,285,230 |
| Compact source support cover | 1,930 |
| Additional compiler wires | 2 |
| Final qubit bound | 1,932 |
| Score from certified bounds | 732,779,064,360 |

The T formula is 4*(65,535 + 29*3,266,951) + 56,773 + 1. Fourier feedback accounts
for 35,245 left-axis and 21,528 right-axis rotations. The initial point load has
65,535 eligible CCX. Reset and the neighboring-word readout have zero T cost.
Before global lowering the 29-addition source bound is 663,706,571 T.

| Certified stage | Q upper bound | T upper bound | Record upper bound |
| --- | ---: | ---: | ---: |
| Inherited 29-addition EEA physical producer | 854 | 14,750,999,161 | 890,628,714 |
| Compact WEX physical producer | 1,930 | 663,706,571 | 75,718,100 |
| Complete WEX program after both compilers | 1,932 | 379,285,230 | 739,424,671 |

The final slot admission also uses the conservative derived upper bound
90,000,176,648 + 24*663,706,571 + 2 = 105,929,134,354, below the protected cap.
The larger compiled record bound is an admission allowance; actual inserted
records follow the exact normalized eligible-CCX count.

The body uses 2,607,487 measurement records per corrected addition, comprising
1,556,899 literal arithmetic records, 1,048,544 lookup records and 2,044 outer
negation records. The parent cursor is 65,535 + 29*2,607,487 + 474 + 854 + 34,114
= 75,718,100. Lowering inserts one additional record per actual eligible CCX;
Y-state kickback inserts none. The declared measurement bound uses a conservative
upper count derived from the source resource certificate, rather than evaluating
the complete emitted gate list. The final declared measurement upper bound is 739,424,671, obtained as
75,718,100 + 663,706,571. The judge result is recorded in the validation section.

The source slot bound is 90,000,176,648. Both compilers together add at most
21 slots per eligible CCX, three per pre-existing selected literal S, and two
preparation slots. Static source-count bounds prove the result below the official
4,000,000,000,000,000-slot cap. Coefficient rows remain 917,504 and all 55 decoder
trials are charged against the protected candidate-check budget. Resource bounds
hold for every Q and every history; they do not rely on sampled inputs.

## Provenance and dependencies

The assembly starts from the WEX credit component at 8f2c9a1 and imports the
committed coherent body at 776a74c and its compact physical export at d169ad9. The 29-addition producer is the parametric
port at 1838d4d4 of c96133a0. These component commits are source checkpoints,
not separately claimed public submission UUIDs.

The vendored controlled point-addition arithmetic is the Apache-2.0 ECDSAAdd
work by Runzhou Tao, Anirudh and ECDSAAdd contributors from the public
[ecdsa.fail Lean challenge](https://github.com/Layr-Labs/ecdsafail-lean), pinned to
[revision c3f340a](https://github.com/Layr-Labs/ecdsafail-lean/tree/c3f340af8ef1cd0e25487e457fe1778c99f0beb9).
The four vendored parts are retained unchanged from the WEX assembly base. Their
source module list, original copyright notices and license attribution remain
beside the code. The WEX integration adds lookup holes, coherent specialization,
one-row negative-double handling and explicit native/Streaming port transport.

The Streaming arithmetic and semantics originate in
[VerifiedQC/ShorECDLP PR #551](https://github.com/VerifiedQC/ShorECDLP/pull/551),
associated with [arXiv:2607.13816](https://arxiv.org/abs/2607.13816). The formalized
Streaming work and its existing Apache-2.0 notices are retained. The temporary
logical-AND mechanism also follows Craig Gidney, Halving the cost of quantum
addition, Quantum 2, 74 (2018), DOI 10.22331/q-2018-06-18-74,
[arXiv:1709.06648](https://arxiv.org/abs/1709.06648). The concrete compiler and
Y-state implementation are credited to their public challenge submissions below.

The list below includes our team lineage, the complete declared c96133a0 dependency
list, both global compiler stages and the zero-residue/full-window credit methods.
It has 22 entries, and a submission can declare at most 20 dependencies. The two
left out of the formal declaration are our own EEA entries 60e50724 and a74a7112,
because the WEX program no longer runs EEA; they are credited here. The reused
source and role of each entry are:

- `8c5e5431-b76b-4b69-8843-98479de53c05`: Single-trial nearest-pair Streaming construction and fixed signed-window table lineage. Generic success and point/Fourier composition retained in the abstract producer.

- `c4cfd7c1-a895-4c5d-9745-4b3eee0c10c9`: In-place XOR exceptional-point correction and Streaming certificate lineage. Retained Streaming physical point model and EEA regression development in Main.

- `da06e7d1-069a-4b86-9b8a-e55a4624c243`: Sharp rounding-window and Fourier/decoder analysis. The sharp-window proof is retained once in the bundled producer.

- `69a9e23e-084b-4fb7-81c4-9d240644b1ca`: Averaged-success and Streaming probability-composition lineage. Retained precursor success framework used by the single-trial proof.

- `60e50724-9bf0-4ea5-ab2b-79126a9a9932`: Complete all-four-EEA cancellation proof calculus. The inherited EEA regression and structural compiler framework retain this source.

- `a74a7112-a5d8-4f24-b193-57b7e7d66d67`: Our reversible EEA microstep cancellation algorithm and semantic/resource transport. Retained cancellation development in the skeleton lineage.

- `fffa232f-54c7-4bdf-80c5-52485c305eb7`: Adaptive zero-allowed arithmetic guards and cancelled sign-negation lineage. Inherited physical validity, support and correction framework.

- `c96133a0-eda7-4ce6-b4de-087f8588011a`: The 266/208-bit, 29-addition, 55-neighbor wrapped-shift producer. The abstract producer and final decoder use its physical schedule, table and complete success proof.

- `c6a88fcf-3079-496f-95f0-f6e486a401ec`: Rounded wrapped-shift producer and certificate/resource framework. Precision, readout and resource packaging precursor to the 29-window producer.

- `bcad5b2d-7db1-49b8-8fa6-9d9c92c80124`: Certified reusable temporary-AND compiler, record redirection and certificate transport. AndGadget lowering is applied to the complete WEX parent program.

- `96fdd4d2-5d53-49a1-8840-cc842f63f34b`: Integration of the measured-AND compiler with the rounded producer. Inherited compiler and static support/certificate assembly lineage.

- `791100e1-d660-48fa-a6cb-7c1bc7eaa62b`: Certified Y-state phase-kickback compiler. Catalyst removes the forward-S charge from each lowered CCX and charges one shared preparation.

- `03bad799-6ecf-43f0-9764-ee07b27961a1`: Full eligible-CCX credit through zero-residue proofs. WEXCredit follows and adapts the structural residue method for reader-independent literal arithmetic and unary lookup.

- `fcde795e-51a8-4ea4-afbf-3d2909dc2884`: Later full-window credit and counted-window composition development. The WEX window and parent credit proofs adapt the inspected late full-window residue/count composition method.

- `070b7401-9930-4194-b1af-63de0ff504af`: Measured exceptional correction, adaptive guards and rounded cancellation composition. Declared source in the c96133a0 dependency list; inherited producer lineage.

- `1163b12b-0797-4aa0-82c7-df1225180aa8`: Consolidated measured correction, adaptive arithmetic and all-four-EEA proof calculus. Declared source in c96133a0; retained abstract skeleton and EEA regression lineage.

- `49d67f7a-7890-4396-88f6-09f71a9f7cec`: Unary query-tree eligible-CCX count proofs and structural compiler integration. Declared source in c96133a0; retained compiler/count framework.

- `6dd458e6-edcf-4441-aed0-51bcda675962`: Measured exceptional equality, physicality, scratch restoration and support/slot proofs. Declared source in c96133a0; inherited Streaming correction development.

- `8dca04ae-3e67-495a-90b2-411c935eca72`: Adaptive zero-input guards with coherent field composition and Straight compilation. Declared source in c96133a0; retained physical/arithmetic validation framework.

- `c5e75ef9-89b9-4e53-93d2-330b1b3fbb3d`: Thirty-window all-four-EEA cancellation transplant. Declared source in c96133a0; inherited cancellation/producers lineage.

- `f25bf1f7-0ac7-42b4-8ce6-8346a1e581cb`: Borrowed query-flag producer and complete support/coherence transport. Declared source in c96133a0; fixed wire 836 activation and physical framing lineage.

- `f7419f16-90d6-4381-85a3-504b86725fa4`: Five-P compiler certificate assembly and compositional eligible-count transport. Declared source in c96133a0; compiler integration structure retained and specialized to WEX.

## Validation

The compact five-module root passed its remote build in 664 seconds. The frozen
candidate commit is 0bab5d4e8a3ccf777ad988216054448c402eb8bc. The reserved-lane
quick judge returned exit status zero after 3,546 seconds including that warm
build and the complete cold rebuild. Every module passed warnings as errors:
Part1 took 670 seconds, Part2 683, Part3 366, Part4 357 and Main 680. The exact accepted line is:

```text
Verified score=732779064360 (qubits=1932, tModel=379285230, toffoli=54183604, nonClifford=4000000000000000, measurements=739424671)
```

The Toffoli and non-Clifford fields are the protected judge's derived upper
bounds. The declared qubit, T and measurement bounds are 1,932, 379,285,230 and
739,424,671 respectively. The score is their certified qubit/T product. The
frozen-tree capped Entrant replay measurements are recorded below after completion. The replay configuration is the complete
Entrant prefix on 32 workers, an 84-GiB cgroup memory cap, zero cgroup swap and a
600-second timeout. Acceptance of this assembly's memory gate additionally
requires peak RSS at most 78 GiB. RSS and cgroup peak are recorded separately.
No source changes are made after the passing quick judge. Only the permitted
proof dependencies propext, Classical.choice and Quot.sound are used. No protected
source, decoder, cost rule, benchmark script or limit is edited. No filing or push
operation is performed by this stream.

Reproduction uses Lean 4.28.0 and the repository's locked dependency manifest on
Linux. Build the unchanged protected Official/Judge targets and the five-module
Entrant with warnings as errors. The quick harness preserves source hygiene,
protected-source and artifact checks, the protected Challenge/Judge replays and
the expression-level certificate judge; only the separate Entrant-prefix replay
is deferred to the memory gate. The gate reconciles the source/module inventory,
records SHA-256 fingerprints, and checks the complete prefix rather than Main
alone. Its core invocation, inside an isolated 84-GiB scope with zero swap, is:

```sh
LEAN_NUM_THREADS=32 timeout 600 leanchecker --verbose ShorECDLP.Submission.Entrant
```

The checker uses the matching build library search path. A successful memory
gate requires exit status zero, matching inventories of five source and compiled
modules, no cgroup OOM event, zero swaps and peak RSS at most 78 GiB. The scope
limits are read back from the running cgroup, and its peak allocation is reported
separately from the process maximum resident set size. The public mechanism and
resource bounds do not depend on machine-specific paths or build credentials.

