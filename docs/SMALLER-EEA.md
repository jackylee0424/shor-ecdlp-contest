# Smaller exact EEA feasibility

Brief 23, 2026-10-29.  Exact integer arithmetic is in
`workspace/smaller_eea.py`.

## Verdict

**Do not start a 256-bit Entrant replacement yet.  Start one proof-first
Bernstein--Yang milestone.**  There is no presently specified circuit that is
simultaneously exact, worst-case bounded, challenge-compatible, and cheaper
than the leader.  The apparent alternatives separate as follows.

1. **arXiv:2607.13816 v3 is the bench EEA, not a new candidate.**  Its packed
   two-work-register, four-phase, 1,620-step construction, active windows and
   in-place Figure 15 division/multiplication are precisely the architecture
   formalized under `Submission/2607_13816`.  The paper's `229n²+O(n log n)` is
   an asymptotic leading term, and its `15.35M` n=256 count is rounded output
   from a Qiskit/template pipeline.  The kernel-backed count is 15,910,015 CCX
   per measured wrapper; the leader already proves a further 165,240-CCX
   cancellation, leaving **15,744,775 effective CCX/wrapper**.  The paper does
   not provide a second 835-wire challenge layout to transplant.
2. **Bernstein--Yang divsteps is the best research target.**  Replacing the
   sampled 532 ticks by a proved 590-tick half-delta bound still leaves enormous
   score headroom.  A deliberately conservative screening profile at fixed
   ring width 340 is 414,770 CCX/wrapper.  However, the 340-lane envelope, the
   uncapped reverse/replay rule, and that gate receipt are not proved.  They are
   the project, not implementation details.
3. **Top-aligned greedyfrog is second.**  Its packing and fixed boundary are
   attractive, but an exact inverse decision decoder is still absent.  The
   28-lane/21-row donor decoder, per-slot windows and 254--260-slot schedules
   are sampled.  A 469-slot unwindowed screen is cheap, but is not an exact
   circuit count because full decode is unpriced.
4. **“Remove 57% while retaining the bench EEA” is only a lower bound.**  After
   assigning the leader's cancellation to its B/E cells, repeated boundary
   location is exactly 8,943,260 effective CCX/wrapper.  Setting that work to
   zero leaves 6,801,515 CCX/wrapper and projects a 48.93% score cut, but no
   circuit can get fixed-lane arithmetic for zero cost.  The current packed
   representation makes the boundary part of the state; eliminating it means
   caching a coherent one-hot boundary (hundreds of extra wires) or changing
   representation, so the microstep proof no longer transfers unchanged.

The recommended first milestone is therefore:

> A kernel-checked pure Lean termination certificate for the selected
> half-delta divstep recurrence at 256 bits (590 ticks, or fall back to the
> published classic 742-tick formula), followed by an n=8 exact fixed-schedule
> forward/reverse `Straight` circuit with branchwise coherence, exact
> CCX/record/support counts, and no run cap.

Stop immediately if the termination certificate needs a forbidden evaluator
axiom, if reverse replay needs a sampled run cap, or if the first complete
fixed-width receipt exceeds the qubit-dependent ceilings in the stop table
below.  No bench edit or stack patch is justified before that milestone.

Primary references: [Luo et al., arXiv:2607.13816v3](https://arxiv.org/abs/2607.13816),
the authors' [resource-estimation code](https://github.com/ZeroWang030221/Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Space-Efficient-Point-Addition),
[Bernstein--Yang safegcd](https://gcd.cr.yp.to/safegcd-20190413.pdf),
the [safegcd bounds certificate repository](https://github.com/sipa/safegcd-bounds),
and libsecp256k1's [implementation explanation](https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md).

## 1. Accounting basis

The baseline is leader spariev `c96133a`, bench `32b7d38`:

```text
Q = 856
T = 8,480,934,044
Q×T = 7,259,679,541,664
windows = 29
EEA occurrences = 29 × 4 = 116
```

The protected measured wrapper is 15,910,015 CCX.  The leader's all-four EEA
patch removes 714 pre-lowering T in each of 1,620 microsteps:

```text
714 / 7 = 102 CCX/microstep
102 × 1,620 = 165,240 CCX/wrapper
15,910,015 - 165,240 = 15,744,775 effective CCX/wrapper
```

The temporary-AND plus catalyst compiler prices each remaining eligible CCX at
four P/T gates.  The one global catalyst preparation remains in the retained
non-EEA total.  Therefore:

```text
current EEA T = 116 × 4 × 15,744,775 = 7,305,575,600
retained non-EEA T = 8,480,934,044 - 7,305,575,600
                   = 1,175,358,444
```

The current EEA is **86.14%** of final leader T (the “about 87%” headline).
Every projection below uses

```text
Tnew = 1,175,358,444 + 116 × 4 × Cwrapper.
```

The protected wrapper has 6,961,844 algorithmic measurements.  After leader
cancellation and compiler lowering, its per-wrapper record accounting is

```text
6,961,844 + 15,744,775 = 22,706,619 records.
```

The full leader record number 8,266,128,294 is a certified conservative bound,
not an exact decomposition.  Candidate “projected records” below subtract and
add wrapper receipts against that bound only as a cap screen; a replacement
still needs its own final-cursor theorem.

### Exactness legend

- **proved**: existing kernel theorem or exact integer consequence of one;
- **floor**: exact subtraction but not the cost of an implementable circuit;
- **screen**: exact integer evaluation of explicitly stated, unproved design
  hypotheses.  It is not a challenge resource bound.

This distinction is necessary: none of the attractive donor numbers is an
exact worst-case challenge receipt today.

## 2. Candidate prices

| Candidate | Q used for screen | Worst-case CCX / wrapper | T / wrapper after 4-P | Records / wrapper | Status |
|---|---:|---:|---:|---:|---|
| Leader after cancellation | 856 | **15,744,775** | **62,979,100** | **22,706,619** | proved |
| v3/protected wrapper before leader cancellation | 856 | 15,910,015 | 63,640,060 | 22,871,859 | proved, dominated |
| Hybrid with all priced B/E location work set to zero | 856 | 6,801,515 | 27,206,060 | 8,555,807 | exact floor; no circuit |
| BY half-delta, 590 ticks, W=340 | 952 | 414,770 | 1,659,080 | 616,550 | screen; width/replay unproved |
| BY classic bound sensitivity, 742 ticks, W=340 | 952 | 521,626 | 2,086,504 | 775,390 | screen; width/replay unproved |
| greedyfrog, 469 unwindowed slots (average of two forward/two reverse) | 841 | 4,279,625 | 17,118,500 | ≤8,560,657 screen | slot/decode theorem absent |

The Q values for the two novel lines are not claims.  BY Q=952 assumes two
340-lane rings can preserve all of the donor's sharing, hence
`856 + 2×(340-292)`.  A non-packed four-word fallback is expected around
1,290--1,400 Q.  Greedy Q=841 is the donor's 825-ish traversal plus the
leader's 16-wire coherent address/sign bank; an exact full decoder may exceed
it.

### 2.1 Bernstein--Yang divsteps

#### Iterations

There are two relevant fixed horizons.

- The classic Bernstein--Yang Theorem 11.2 expression
  `floor((49n+80)/17)` gives 742 at n=256 (nearby literature counts differ by
  one depending on initialization and bit-size convention).  It is a safe
  conservative sensitivity point, not the sampled 532 schedule.
- The half-delta variant used by libsecp256k1 has a 590-divstep convex-hull
  bound for 256-bit inputs.  A machine-checkable external certificate exists,
  but it is not yet a Lean theorem in this repository.  The challenge proof
  must replay or re-express that certificate in the kernel.

Padding after completion is semantically harmless only after proving the
selected recurrence is absorbing when `g=0`, including the coefficient and
transcript state used by the quantum inverse.

#### Screening circuit

The calculator charges each fixed-width tick at ring width W and h-register
width H as

```text
2W                 two signed-add / ring-swap lane passes
+ 2H + 1           sigma and conservative h update
```

Conditional sign changes are CNOT/X conjugations and cost no CCX.  For
`W=340`, `H=11`, this is 703 CCX/tick, hence:

```text
590 × 703 = 414,770 CCX/wrapper
742 × 703 = 521,626 CCX/wrapper.
```

The record screen charges one compiler record per CCX plus W measured
carry/AND erasures and two decision/control records per tick.  This gives
616,550 and 775,390 records/wrapper respectively.  These are exact values of
the stated model, not receipts from a completed circuit.

#### Width and qubits

The donor's W=292 schedule is sampled and therefore inadmissible.  Three width
levels must be kept separate:

1. **W=292:** donor/sample only; reject.
2. **W≈330--340 packed rings:** attractive conditional target.  It requires a
   theorem bounding both signed values and both growing cofactors at every
   public tick while proving the packed fields never overlap.  Q≈932--952.
3. **Four fixed signed words:** obvious exact fallback geometry, roughly
   1,290--1,400 total challenge wires once the live passenger, address bank and
   compiler/catalyst wires are included.  Its gate count must be rebuilt; the
   414,770 figure cannot simply be copied to it.

Extra wires are economically justified if the circuit exists.  At Q=952 a
greater-than-10% improvement permits **12,258,155 CCX/wrapper**.  At Q=1,290
it still permits **8,382,616 CCX/wrapper**.  The screening core is far below
both; proof and exact replay, not the score slope, are the risk.

#### Exact contract

A raw divstep output is not automatically the bench wrapper output.  It may
leave signed `f`, a scaled coefficient, delta, and a transcript state.  The
replacement must prove either:

- the exact existing forward ideal state `secp256k1EEAOutputIdealState` and
  consume it with an exact reverse wrapper; or
- a new abstract forward/reverse inversion-pair interface, then reprove the
  Figure 15 division/multiplication composition around that interface.

The second route is smaller.  It must provide canonical `x⁻¹ mod p` in the
same physical operand bank, preserve the other live operand, expose whatever
state the reverse needs, and return all workspace clean.  Constant-time
conditional swaps/negations, terminal sign normalization, all measurement
phases, and replay for every history are part of that theorem.  No sampled run
log or terminal range cut is allowed.

### 2.2 Top-aligned greedyfrog

The attractive exact pieces are the 258-lane value/cofactor packing invariant,
the marker-delimited top boundary, fixed-lane arithmetic, and reversible
renormalization.  The current donor is not exact because it uses sampled
per-slot windows, a fixed 254--260 slot horizon, and a 28-lane/21--25-row
inverse decoder.

The screening schedule combines the bench theorem
`paperQuotientWeight_le_405` with a proposed total-renormalization bound of at
most `2n=512`.  If every stall absorbs eight excess shifts, this gives

```text
405 + ceil(512/8) = 469 slots.
```

Using the donor's unwindowed prices gives:

```text
forward: 469 × 5,496  = 2,577,624 CCX
reverse: 469 × 12,754 = 5,981,626 CCX
two of each / window: 17,118,500 CCX = 68,474,000 lowered T
average wrapper:       4,279,625 CCX.
```

This is not an exact worst-case price.  The full decoder is excluded because no
exact bounded-row decoder is known.  Charging every screened CCX once more for
an algorithmic measured erase plus three decision records per slot gives the
conservative record screen 8,560,657/wrapper, still safely below the global
record cap after substitution.

The inversion contract is the same abstract contract as divsteps.  It does not
produce the bench's packed four-phase internal state, so only Figure 15's
multiply/measure/recompute shell should be reused.  The point-add formula does
not change, but the in-place division/multiplication proof does.

**Stop condition specific to greedyfrog:** if exact reverse recovery requires
either a Θ(n)-bit transcript per slot or a full-width division whose proved
count exceeds 14,210,389 CCX/average wrapper at Q=841 (12,258,155 at Q=952),
it misses the >10% policy.  Stop earlier if the decoder still has a finite-row
overflow event; that is approximation, regardless of how small its sampled
rate is.

### 2.3 arXiv v3

At n=256 the paper states

```text
inversion width = 2n + 6 floor(log2 n) + 19 = 579
point-add width = 3n + 6 floor(log2 n) + 19 = 835.
```

Those are standalone circuit widths.  The challenge circuit also has a
coherent 16-wire address/sign bank during arithmetic and uses the temporary-AND
and catalyst ancillas.  More importantly, the bench already implements the
same register-sharing algorithm, including the corrected 1,620-step
matrix--continuant bound, active windows, measured uncomputation and Figure 15
shell.  Its binding inventory is 580 EEA roles plus the live data bank, root,
infinity, address/sign bank and two compiler wires: 856 total.

The leading term `229×256² = 15,007,744` is not a concrete count.  V3 Table 2
reports a rounded 15.35M forward inversion after blockwise Qiskit compilation
and local NCT templates.  The repository does not ship that rounded table as a
Lean proof or as an exact challenge `Straight` receipt.  The protected exact
wrapper is 15,910,015 CCX, and the leader's kernel-checked cancellation already
brings it to 15,744,775.

Thus v3's inversion contract already matches the bench route and Figure 15 is
already reused.  The only live subproject here is **prove additional local NCT
templates**, not “port v3.”  An exact paper-versus-bench operation diff could
reveal more cancellations, but the rounded 15.35M number cannot support a score
projection.

### 2.4 Bench-semantics hybrid

The exact raw location terms per wrapper are:

| Term | CCX/wrapper |
|---|---:|
| B interval ripple/decoder | 4,387,970 |
| E coefficient-prefix | 3,998,010 |
| B endpoint prepare/restore | 673,920 |
| **raw location subtotal** | **9,059,900** |

The leader cancels 102 CCX/microstep.  Of those, 72 are B/E location work
(two B1 controls, B2, and E prepare/clean), so the effective subtotal is

```text
9,059,900 - 72×1,620 = 8,943,260 CCX/wrapper.
```

Removing it for free leaves 6,801,515 CCX/wrapper.  The corresponding exact
floor is:

```text
T = 1,175,358,444 + 116×4×6,801,515
  = 4,331,261,404
Q×T at Q=856 = 3,707,559,761,824
change = -48.929429453%.
```

The floor also removes the 5,207,552 B/E algorithmic erasures and projects
8,555,807 records/wrapper after compiler lowering.

Two honest implementation families exist:

- **cached boundary masks:** retain the packed-state semantics, compute the
  coherent one-hot boundary once per microstep and reuse it across B/E.  One
  n-bit mask already moves the peak near Q=1,112; two masks are worse.  Exact
  dirty borrowing and restoration are mandatory.  At Q=1,112 the >10% ceiling
  is 10,129,916 CCX/wrapper.
- **normalised representation:** make the boundary a fixed lane as greedyfrog
  does.  This removes the locator structurally, but changes the state and step
  recurrence.  Only the outer inversion theorem transfers; it is no longer a
  “same EEA microstep” proof.

There is no 856-wire local edit: `FEWER-QUBITS.md` proves that every owner is
live at the EEA peak.  A hybrid should be stopped unless it supplies an actual
fixed schedule, exact mask/normalisation cost, and a new support allocation.

## 3. Minimal Lean proof route

### 3.1 Shared abstract interface

Introduce one small interface theorem for a paired inversion implementation,
parameterized by its physical layout:

1. `forward` coherently maps every clean canonical nonzero x to canonical
   `x⁻¹ mod p` plus a well-formed private transcript/state;
2. `reverse` consumes exactly that forward image and restores x and all private
   workspace;
3. both circuits preserve the passenger/data bank and external coherent
   address state;
4. exact support, well-formedness, record cursor, gate slots, CCX/P count and
   reset cleanliness.

Then instantiate Figure 15 with this pair.  Do not force a new algorithm to
equal `secp256k1EEAOutputIdealState` field-for-field unless that is genuinely
cheaper than proving the abstract composition.

### 3.2 Divstep-specific theorems

Minimal mathematical layer:

1. one-step integer correctness: parity/divisibility, gcd preservation,
   determinant/cofactor invariant and modular inverse relation;
2. signed fixed-width range invariant for every value, cofactor and delta
   register at each public tick;
3. fixed-horizon termination (590 selected target; 742 fallback), followed by
   absorbing padding;
4. canonical terminal normalization, including the sign/scaling factor.

Minimal circuit layer:

5. fixed-width signed add/subtract, conditional negate, conditional swap and
   delta-update coherent theorems;
6. transcript measurement/replay and phase repair for every outcome, with no
   capped run;
7. tick forward/reverse theorem, fixed-schedule induction, exact count/support/
   record recurrences;
8. the abstract inversion-pair instance and Figure 15 bridge.

The termination theorem is the main risk.  The external convex-hull proof is a
finite rational/polyhedral certificate, but expressing and replaying it without
`native_decide`, an axiom, or an enormous kernel term may dominate the work.

### 3.3 Greedyfrog-specific additions

In addition to the shared interface:

1. marker/value/bit-reversed-cofactor packing invariant;
2. correspondence between greedy digits and binary quotient 1-bits, importing
   the existing 405 bound;
3. exact total-renormalization and stall-slot bound;
4. exact, bounded inverse recovery of rotation/swap/digit for every reachable
   state;
5. fixed unwindowed or proved-window circuit and its complete record receipt.

The exact decoder is the main risk.  Until theorem 4 exists, gate counting more
of the donor is low value.

### 3.4 Hybrid-specific additions

For cached masks, prove a new step circuit implements the existing ideal
`indexedStep` transition.  The current arithmetic and 1,620-step termination
proof can then transfer, while the physical step/coherence/count/support chain
must be rebuilt.  For a normalised representation, only the outer inversion
specification and generic cells transfer.

### 3.5 Bench lemmas that transfer

The following infrastructure is reusable once a replacement proves the shared
interface:

- `CoherentlyImplementsOn` composition and measured-uncompute lemmas, including
  `measuredAndErase_coherent_uncompute`;
- `fig15MultiplyToWork`, `fig15MultiplyToData`,
  `fig15MultiplyToDataInverse`, their coherent/resource theorems, the 256-bit
  measure/reset bank, `registerZCorrection`, and final bank swap;
- the point-stage, exceptional-image, lookup, outer-window, compiler, catalyst,
  decoder and final Certificate proofs above the in-place arithmetic contract;
- generic Gidney add/compare/constant arithmetic cells where their register
  contracts match.

The current EEA's packed-field, active-window, quotient/remainder, length-map,
terminal-epoch and exact wrapper-count lemmas do **not** transfer to divsteps or
greedyfrog.  V3 transfers all of them because it is that construction.

### 3.6 Effort

| Size | Deliverable |
|---|---|
| S | Pin the recurrence and conventions; pure integer reference model; define the abstract inversion-pair contract; reproduce this calculator. |
| M | One exact divstep cell and its inverse; n=8 fixed schedule; branchwise measurement phase proof; exact small-width counts/support/records.  Also enough for one additional v3 local-cancellation template. |
| L | Parametric word/tick circuit, signed-width invariants, full transcript replay, Figure 15 bridge, and compiler/catalyst resource chain. |
| XL | Kernel-check the 590-tick bound/certificate; 256-bit width envelope and packed layout; full fixed schedule and final Certificate integration.  Greedyfrog is also XL because of exact decode. |

Honest overall estimates: BY **XL/XL+**, greedyfrog **XL**, cached-mask hybrid
**L/XL**, v3-as-new-candidate **S (reject)**.  Calendar estimates are premature
until the n=8 circuit and termination certificate replay.

## 4. Conditional projection for the best research candidate

The best research candidate is BY590.  Under the explicitly conditional
`W=340`, `H=11`, 590-tick profile:

```text
Cwrapper = 414,770 CCX
replacement EEA T = 116 × 4 × 414,770 = 192,453,280
total T = 1,175,358,444 + 192,453,280
        = 1,367,811,724
Q = 952
Q×T = 952 × 1,367,811,724
    = 1,302,156,761,248
change vs 7,259,679,541,664 = -82.063164720%
projected record bound = 5,703,680,290
```

The arithmetic is exact; the candidate hypotheses are not.  To show that
extra wires remain economically safe, reusing the same arithmetic number at a
1,290-wire score-only fallback gives

```text
1,290 × 1,367,811,724 = 1,764,477,123,960
change = -75.694834547%.
```

That second line is not a circuit projection because the four-word layout will
change the gate count.  It only demonstrates that a substantial width increase
does not erase the opportunity.

For comparison, the exact zero-location floor is
`856×4,331,261,404 = 3,707,559,761,824` (−48.929429453%), and the conditional
greedy screen is
`841×3,161,104,444 = 2,658,488,837,404` (−63.380080041%).

## 5. Stop conditions and milestone gate

### Score ceilings

The table is the largest uniform CCX/wrapper compatible with each strict score
target, retaining the leader's non-EEA T.  “>10%” means strict
`10×newScore < 9×leaderScore`.

| Q | Any improvement | >10% improvement |
|---:|---:|---:|
| 841 | 16,070,777 | 14,210,389 |
| 856 | 15,744,774 | 13,916,987 |
| 900 | 14,851,189 | 13,112,760 |
| 952 | 13,901,627 | 12,258,155 |
| 1,112 | 11,536,918 | 10,129,916 |
| 1,290 | 9,595,474 | 8,382,616 |
| 1,400 | 8,642,514 | 7,524,953 |

Stop a design when its proved physical union and exact wrapper count cross the
relevant row.  Also stop regardless of score if any of these occurs:

- the schedule, width, decoder capacity, run length or terminal range is based
  on sampling or a nonce-selected corpus;
- emitted gates or coefficient data depend on Q or on data-dependent host
  branching rather than permitted `Straight` controls;
- reverse replay cannot be proved for every measurement history on the
  forward image;
- count/support verification needs `sorry`, `native_decide`, an unchecked
  binary receipt or another forbidden shortcut;
- a small-width fully expanded circuit shows the source-to-`Straight` lowering
  or kernel replay is not scalable.

### First reviewable milestone

Create no Entrant patch.  In lab scratch only:

1. `EEA2DivstepsMath.lean`: selected divstep recurrence, one-step invariants,
   absorbing completion and a kernel-replayed 256-bit iteration certificate;
2. `EEA2Small.lean`: n=8 fixed-width forward/reverse circuit, exhaustive only
   through proved finite lemmas (not a forbidden native shortcut), exact
   branchwise coherence and exact resource theorem;
3. extend `smaller_eea.py` with the actual cell receipt and measured physical
   union.

Pass the milestone only if both Lean files use the allowed axiom set and the
counted circuit has no run cap or sampled width.  Only then design the 256-bit
packed layout and Figure 15 bridge.
