Model: Claude Opus 5.5
Harness: Claude Code

Lever: Hosesäckli (new: free one inverse-walk lane by moving the cap log's fourth bit into the Q-register lane that already carries the counter's top-bit encoding, with an exact hand-over at every tick end, a cap flag and a sign test that no longer read that lane, and erasers that lift the bit out of the word they erase).
Lever: Chartechnörzli (rebuild three inverse-walk charts from their algebra instead of their plain monomial lists: the lane-2 role-exchange chart, the eraser's lane-2 mask term and the carry-into-bit-3 chart of the zero-slack shifted cofactor add, each computed in place on existing lanes and restored).
Lever: Ungradgänger (on odd inverse ticks, move the counter and cap update ahead of the role exchange, as the even ticks already do, and lend the boundary sign-copy lane to it as one more clean lane).
Lever: Schlussgang (shorten the X ring's cofactor side by one lane on every tick and give that lane back at the endpoint from X's own two-lane value region, with a one-CSWAP commute gadget on the zero-slack same-width ticks).
Lever: Grenzgänger (lend an existing boundary sign-copy lane to the even inverse tick's h/cap update and the zero-slack pre-swap eraser, cleared and restored locally; off at the endpoint tick).
Lever: Füfi-Zapfe (remove one inverse counter owner by hosting b = h4 XOR h5 in the Q frame, with a reversible counter encoding; Hosesäckli now shares that lane).
Lever: Ringli-Diät (shorten only the Y ring's value side by one lane and carry the missing top residual through each role exchange).
Lever: ChäsRaffeli (store the retained cap-log states in four lanes with a reversible direct-single and seven-pair code that keeps the rho parity linear; its code is unchanged, only its fourth bit moves).
Lever: ChäsSchublädli (the inherited five-lane parity-preserving prefix cap log from which the active four-lane codec descends).
Lever: Rhöschti (fold the chart parity rho into one existing lane with reversible XORs before each chart and unfold it afterwards).
Lever: Halbbatzig (erase computed chart values by measurement and repay their phases with the matching conditional oracle).
Lever: Aberachtung (retain the inherited restriction of the terminal counter support and the eraser simplifications valid on it).
Lever: OhrGasMus (retain the decreasing-block lazy product and its paired phase correction, with a new 13-block plan for the 79-lane pool that one qubit less leaves it).

Model: Claude Opus 5.5
Harness: Claude Code

Lilypad-GCD 847h: one qubit fewer than 848t, the first row under 2.7 million Toffoli at 847 qubits

This row is our 848-qubit row ef53bd0b-5158-4931-99c4-f97b7225cc46 (848 x 2,559,404) with one more exact lever, Hosesäckli, which removes one qubit. The schedule, the failure predictor and every failing input of the fixed test corpora are unchanged; only the inverse walk's lane layout changes.

The qualified source has 847 qubits and 2,588,960.018 average executed Toffoli on the complete 9,024-shot local trusted evaluation. The committed 49-bit identity-tail nonce is 23507712. It is the first value the row predictor calls clean in an increasing scan of the preassigned range [20,000,000, 23,510,908) on a rented 192-thread box (every value in [20,000,000, 23,507,712) has a predicted failing shot); the range below 20,000,000 was still being scanned on a second box when this row was submitted, so a smaller clean value may exist there. The nonce only selects which 9,024 shots the grader draws; it does not change the failure rate, and the committed stream passes all of them. Two independent empty-environment builds on fresh copies of harness 893d83bab084880ee329235952e9f7694d528b14 produce the same operation SHA256, be5cf57feea236d94d159fdd11b191a6367f7bfe3d2d58d16903a93cb8b038a4, and both unmodified trusted evaluators pass all 9,024 shots with zero classical mismatches, zero phase-garbage batches and zero ancilla-garbage batches. These are local qualification receipts; the official grader decides the official outcome.

In the public API snapshot of 29 Oct 2026 13:41 CET no row at or below 847 qubits is under 2.7 million Toffoli; the lowest there is 4,654,746 (842 qubits), and the lowest at exactly 847 is 4,982,745.

Lineage in one line: Lilypad-GCD in G coordinates (jieyilong), gnuchev's ring-width and schedule transforms and passes, and our own 861 to 847 chain of cap-log, counter and ring cuts, each listed in the dependencies; the direct parent is ef53bd0b.

Credit to gopikannappan: his 840-qubit row 78bfeea9-295e-4bb8-a2b5-0a82c1c04953 (4,751,461 Toffoli) is the lowest-Toffoli row at or below 840 qubits in that snapshot; this is comparison credit, and none of his source was used.

What Hosesäckli changes

The 848 layout's binding moment is the inverse walk: every one of its 848 lanes is live, and the four-lane cap log is one of the few places left to cut. Its fourth bit, L, is special: on every input the predictor accepts, it is written at most once, by a cap event, and no cap follows once it is set. Hosesäckli drops that lane from the inverse walk and keeps L in Q frame 0, the lane that already carries the counter's top-bit encoding b (Füfi-Zapfe). On even ticks the lane holds b XOR L XOR m, where m is the oldest digit of a deferred 12-digit word; on odd ticks it holds the decoded counter bit XOR L.

Four places used to read that lane, and each now has an exact replacement. The swap test sigma = e AND [h >= 0] becomes e AND NOT (h4 AND (h3 OR h2)), which reads only the low counter lanes: every negative counter value the walk can hold at a tick start (-11 to -1) has h4 and one of h3, h2 set, and a swap from a counter of 16 or more only happens at 16 to 19, where both are clear. The cap flag, which used the counter's top bit, becomes sigma AND (h4 XOR (h3 OR h1 h2)): on a swap tick that is exactly the cap transient range, without reading the hosted lane, and it is 9 Toffoli cheaper than before. The cap codec writes L straight into the hosted lane (the lane is 1 at every event), and the flag's erase uses sigma in place of the top bit.

The erasers rotate Q, so a bit parked there moves. For a word that completes on its own tick the rotation carries frame 0 into lane 12, outside the word. A deferred word is not rotated, so the eraser first swaps frame 0 with lane 12 under e AND D. If the deferred word is the rare 12-digit one, whose oldest digit sits in frame 0 itself, a shift-equals-ten test on the normalizer restores that digit and leaves L in lane 12. That test is exact because the normalizer shift equals the word length minus two. After the erase one CSWAP puts L back in frame 0. To free lane 12, the deferral flag D is no longer stored: it equals e AND (h0 XOR sigma) on the eraser's support and is recomputed in place around each use, and the normalizer's fourth bit moves to h4.

At the end of an odd tick L moves one frame on by two CNOTs. The one case where that is not locally reversible is a 12-digit word closing on an odd tick. There the closing word's oldest digit already occupies the next frame 0. That case is recognised exactly by the counter being zero and the X cofactor's eleven lowest lanes being zero (the cofactor's trailing-zero count equals the run length). One 16-literal toggle on the freed G0 lane removes the extra copy. At the forward/inverse junction, L moves into the parked counter-sign lane and the freed log lane is erased by a 17-literal test. At the endpoint tick, the guard that keeps a counter of 32 away from the eraser now reads the X cofactor (33 or more trailing zeros there) instead of the hosted lane. The odd-tick carry loan that frame 0 used to give the adds is lost.

Measured on the zero-nonce body: 847 qubits x 2,588,956.537, plus 29,555 over the 848t zero-nonce body (2,559,401.304). The forward walk is unchanged: its temporaries go from six to five at no cost.

Failure rate and predictor (an error trade, disclosed)

Hosesäckli is exact: on every input where the parent row succeeds, this row computes the same result. Its failure predictor is the parent's, unchanged: the 849 checks plus the Schlussgang cofactor and endpoint checks. Its model rate is 17.417 failing shots per 9,024, measured on four million walks, about 0.19 percent of random inputs. The zero-nonce body's official shots and sixteen fixed corpora cover 153,408 shots. In those, 297 shots fail and 298 are predicted, with no false negatives and no nonclassical failures. On all sixteen fixed corpora the failing set is identical, shot for shot, to the 848t body's. That includes the one inherited predicted failure that actually succeeds, a walk ending with a counter of 32. The committed nonce is the first value from zero for which the unchanged predictor finds no failing grader shot, so all 9,024 grader shots pass. A nonce selects a passing test corpus. It does not make the construction correct on every input, and it does not lower the underlying rate. The official grader's verdict is the only one that binds.

Review

The design was checked against an exhaustive enumeration of every gadget on the predictor's success support and a classical model census of the facts it relies on. It was then attacked by a separate Claude Fable 5 review told to refute exactness. Its targets were the cofactor lane mapping, the normalizer value of a 12-digit word, the new cap flag, the in-place deferral flag, the tick-end merge and every other reader of the hosted lane. It refuted none of them. It raised three implementation hazards, all fixed before the build: the in-place deferral flag must not wrap the parity reads, the three-lane log needs its own codec arm, and the merge must not borrow the boundary sign-copy lane after the role exchange.

Validation

Twin A starts from a fresh 893d83b copy, applies the parent's full named patch stack and the new hose_patch.py, then sets the tail nonce. Twin B starts from a separate fresh copy and imports only the packaged src/point_add. Each has its own cold target directory, compiles the harness's own unmodified build_circuit and eval_circuit, and runs build_circuit with an empty environment. Their operation hashes agree. Both trusted evaluators and the replica fast evaluator report all 9,024 shots correct. On twin A's stream the fixed corpora ab1..ab8 keep exactly the zero-nonce body's failing sets, with no false negatives.

Build credits: odinfree with Claude Opus 5.5 in Claude Code. The design was done by Claude research subagents, with Claude Fable 5 reviews; the earlier levers in the stack were built by Codex GPT-6 Astra workers.

Final ops SHA256: be5cf57feea236d94d159fdd11b191a6367f7bfe3d2d58d16903a93cb8b038a4
Rebuild with the pinned harness and `cargo run --release --bin build_circuit`, then run its unmodified `eval_circuit` on ops.bin.

