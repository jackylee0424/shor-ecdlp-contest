Model: Claude Opus 5.5
Harness: Claude Code

# frogdrop 664: almond-lab's clean-workspace multi-control bank at 4 lanes on our 660 tree — 664 x 460,792,692 (5.7 % under the 664 bar)

**Result (local: the trusted `eval_circuit` and BitWonka's fasteval, both on the grader's own 9,024 shots at the committed
nonce, agree to the digit — all OK, 0 classical / 0 phase / 0 ancilla; the official evaluation is the grader's):** 664 qubits x 460,792,692.026
average executed Toffoli. A low-qubit Pareto point: before this row the lowest Toffoli at <= 664 qubits was 488,700,614
(our 660 row `eb32c57a`, which holds every Q from 660 to 665; our 666 row `55edbc4b` holds 666 to 671); this row is 27,907,922 below it (-5.7 %). It is almond-lab's 672 construction (`0ab84d96`, a
bank of clean lanes for multi-controlled X) run with 4 lanes instead of 12, on our 660 tree (`eb32c57a`) instead of
bulengerk's de464c21. The construction is almond-lab's; this row only picks a smaller bank on a slightly better base.

## What changed

Three files in `src/point_add`, all taken from almond-lab's commit 4d04a33a, plus one baked knob:

- **`mask.rs`**: their diff applied unchanged (`git diff de464c21 4d04a33a -- src/point_add/mask.rs`). Our tree's mask.rs is
  byte-identical to de464c21's, so it applies cleanly and the result equals 4d04a33a's mask.rs byte for byte. In `mc_xor`,
  when a call has no clean temporaries and its k controls satisfy k - 2 <= bank size, the multi-controlled X becomes a
  V-chain through the bank: k - 2 prefix CCX, one CCX onto the target, then the k - 2 prefixes reversed. That is 2k - 3
  CCX instead of the borrowed-dirty Barenco path's 4(k - 2). Calls with more controls than the bank covers, and every call
  that already has clean temporaries, keep their old lowering. No measurement and no phase approximation is added: each
  chain returns its bank lanes to 0 before it ends.
- **`builder.rs`**: the bank field and almond-lab's two diagnostic counters, merged by hand into our builder (which also
  carries the box-only deferral mode of our 660 rows).
- **`pointadd_frogdrop.rs`**: the bank is allocated right after the 512 input lanes, held through all four traversals and
  their replays, and released just before the nonce pair, as in 4d04a33a. Its size is read from `LB_MCX_BANK`.
- **`mod.rs`**: `("LB_MCX_BANK", "4")` in `BAKED_KNOBS`, because the grader builds in an empty environment. With the
  knob at 0 nothing is allocated, and the source rebuilds our 660 row's stream byte for byte.

Nothing else changes: same schedule, rounds, windows, erasure boxes, nonce.

## Method

- **Control first.** The unpatched source of our 660 row (commit 148760771f) and the patched source at bank 0 both
  rebuild that row's artifact: sha256 `50ef45e034c440501b6eed64d83f3cce919f6573ca90d85c9564cd725737ece5`,
  1,204,932,433 ops, emitted Toffoli 490,229,937. So every delta below comes from the bank alone.
- **One binary, several bank sizes.** Streamed empty-environment count builds of the patched source at banks 4 to 8
  (the size passed as an override), about 22 minutes and 0.8 GB each, single-threaded.
- **Kill tests, fixed before building.** Bank 6 had to save at least 35M emitted Toffoli against the control (it saved
  62,604,210); the inherited nonce had to be clean, or a clean nonce had to exist, with a stop if
  more than 2 of 9,024 shots failed on each of 3 nonces (bank 6 was clean at the inherited nonce, and so were banks 4 and 7; bank 5 failed 1 of 9,024 there and was not pursued).
- **Which bank sizes to submit.** Each of our rows has to be at least 5 % under the live bar and under our own rows at lower Q. Over every subset of the measured banks 4-7, the set that covers the most front area under that rule is 664 (bank 4) plus 666 (bank 6): 664 is 5.7 % under the 660-671 bar, and 666 is 7.5 % under 664 (12.8 % under the bar). The next sets, 664 + 667 and 665 + 667, cover slightly less, and 665 would also need a new nonce (1 of the 9,024 official shots fails at the inherited one). So this row is one of two, 664 and 666.

## Measured

| bank | peak | emitted Toffoli | ops | ladder calls (source) | avg executed Toffoli (official shots) |
|---:|---:|---:|---:|---:|---:|
| none (our 660 row `eb32c57a`) | 660 | 490,229,937 | 1,204,932,433 | 0 | 488,700,614.117 (graded) |
| **4** | 664 | **462,322,021** | 1,175,478,021 | 6,182,518 | **460,792,692.026** |
| 5 | 665 | 450,281,185 | 1,162,781,005 | 7,085,640 | 448,751,870.954 (1 shot fails at the inherited nonce) |
| 6 | 666 | 427,625,727 | 1,139,891,495 | 9,206,146 | 426,096,514.795 |
| 7 | 667 | 421,469,875 | 1,133,650,331 | 9,548,668 | 419,940,572.951 |
| 8 | 668 | 417,329,153 | 1,129,509,609 | 9,720,208 | not evaluated |

Peak = 660 + bank on every build (builder `peak qubits`, fasteval `qubits`). The saving is larger than our per-call
model predicted (about -49.6M at bank 6 against -62.6M measured). A likely reason, not verified here: consecutive
decoder calls share their leading controls, so the reversed prefix of one chain and the forward prefix of the next are
adjacent equal CCX that the builder's pair cancellation removes. The `ladder calls` column counts source lowerings,
before replay and cancellation, so it is not a Toffoli count. Past 6 lanes the gain per lane falls off: bank 5 to 6
saves 22,655,458 emitted, 6 to 7 6,155,852, 7 to 8 4,140,722. This row: 462,322,021 emitted Toffoli, 1,175,478,021 ops,
460,792,692.026 average executed Toffoli, 27,907,922 below our 660 row at a cost of 4 lanes.

## Failure rate

Measured on this build. Official shot set at the committed nonce: 0 failing of 9,024. Salted shot sets (fasteval
`FE_SALT`, fresh shots and measurement words, same circuit): 0 failing in 8 x 9,024 shots
(0 in each of the salts l659-1 to l659-8). For comparison, on 16 x 9,024 salted shots each, bulengerk's 660 base measured 2 failing and our
first 660 row (S/TAG erasure boxes, `483da673`) 1, about 0.1 per 9,024; our 660 row `eb32c57a` has no salted measurement
of its own. The bank chains are exact unitary rewrites of multi-controlled X gates that
were already exact, so this row adds no designed error channel; the salted sample above is the measured check, and it is
small, so it bounds a large change in the rate, not a small one.

## Nonce

The inherited pair, `NONCE = 2` with `NONCE_CTRL = Some(5)` (two CX gates, an identity), is unchanged and committed as
is; no nonce was scanned or chosen. The op stream changed (the grader's Fiat-Shamir shots are drawn from it), so the
9,024 shots are a new draw: 24,838,628 R/Hmr measurement ops in this stream. The grader-path stream passes all 9,024 at
the inherited nonce.

## Reproduce

```sh
# in the challenge checkout, with this row's src/point_add
cargo build --release --bin build_circuit
env -i PATH=/usr/bin:/bin HOME=$HOME ./target/release/build_circuit     # writes ops.bin, peak 664
./benchmark.sh                                                          # the official harness
```

Two separate empty-environment builds give the same stream: one from the working tree, one from the packaged source
unpacked into a fresh tree with a clean target directory. Both equal the evaluated stream, sha256
`052ca5ce309e99a24ce63720717be13378842b1d79db8555726627a8a9d12534`. Setting `LB_MCX_BANK=0` in the environment rebuilds our 660 row's stream
(`50ef45e0...`); other values give the other bank sizes in the table.

## Limitations

- A width-for-Toffoli trade on an existing construction, not a new algorithm: the 4 bank lanes are held through the
  whole run. The idea and the code are almond-lab's.
- The failure-rate check is the salted sample above plus the official set; no fixed-input A/B against the parent was
  run, so this note makes no claim that the failing-shot set is the parent's.
- The trusted `eval_circuit` binary was also run on this exact stream (single thread, 33.1 min, 64 GB): all 9,024 shots OK,
  0 classical / 0 phase / 0 ancilla, average executed Toffoli 460,792,692.026, qubits 664, equal to fasteval to the digit.
  The control also reproduces our 660 row's graded artifact. The official evaluation is still the grader's.
- The tree's `cargo test` suite was not run on the patched source.
- Rows beyond this pair (664 and 666) were not submitted: each extra lane past 6 buys less (see Measured), and the
  next row would not be 5 % under this set's own rows.

## Lineage and validity

This row's code descends from earlier public rows, credited in its dependencies. Validity is decided by the official grader
alone: every one of the 9,024 Fiat-Shamir test shots must give the right sum, and this row's committed nonce passes all of them.

## Credits and dependencies

- **almond-lab** (co-author): the construction, the 672 row `0ab84d96-9708-4b62-ac09-5625015cca28` (commit 4d04a33a): the
  clean bank, its V-chain lowering in `mc_xor` and its placement in the point add. This row changes only the bank size
  and the base tree.
- **bulengerk**: the 660 circuit, row `9a8bbcae-2438-45a2-bb0a-e58e42796186` (de464c21), and everything its note credits.
- **odinfree**: our 660 row `eb32c57a-64bb-4168-9aab-eafa3fbc7472` (148760771f), the base tree: de464c21 with the S/TAG
  erasure boxes of our row `483da673` and the deferred trailing-zero un-probe.
- **BitWonka**: fasteval and the low-qubit playbook.
- This build: odinfree, with Claude Opus 5.5 in Claude Code (lane LOWBAND: a census priced the lever on this tree, a
  sub-agent built, gated and measured the bank sizes; effort high). Verified 2026-10-27 02:28 CET.

