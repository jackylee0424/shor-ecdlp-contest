# Tight divstep coefficients and replay lower bound

Brief 27, 2026-10-29. Lean: `workspace/DivstepTight.lean`. Calculator:
`workspace/divstep_tight.py`.

## Verdict

**No: the proved design does not beat the leader.** The coefficient problem
has a clean exact solution, but local tag-free replay does not.

Store unscaled modular cofactors `(B,D)` rather than the scaled matrix column
`(b,d)`. Lean proves for every tick

```text
f = B*x (mod p),       g = D*x (mod p),       0 <= B,D < p.
```

For a 256-bit modulus, `B` and `D` therefore use exactly 256 unsigned lanes,
independent of the horizon. At termination the inverse is simply `B*f mod p`;
the old data-dependent `2^-ticks` decoder disappears.

However, Lean also proves an explicit three-way collision: valid even, swap,
and add predecessors have the same complete post-state `(delta,f,g,B,D,ticks)`.
No deterministic inverse from that post-state exists on the general odd-`f`
domain. A local inverse needs at least three tag symbols, hence two qubits per
tick; the existing four-way tag is sufficient and its arbitrary-N replay is
proved for the modular representation.

Using those proved widths and two-bit tags in Brief 26's optimistic literal
cell formula gives, at N=590,

```text
Q = 3,018
T = 3,582,256,364
Q*T = 10,811,249,706,552
change vs 7,259,679,541,664 = +48.921858665% (worse).
```

Even the **impossible** zero-history sensitivity is only
`1,838 * 3,582,256,364 = 6,584,187,197,032`, a 9.304712980% cut. It misses the
lab's >10% submission bar before charging a physical modular-halving circuit.
The N=724 and N=742 zero-history sensitivities already lose to the leader.

The result is therefore a stop, not an Entrant candidate. The old `W=340`,
703-CCX screen remains a different, unproved packed-ring architecture; the
fixed modular-cofactor theorem does not certify that packing or that price.

## 1. Exact fixed-width recurrence

Let `p` be positive and odd, and let `x` be the input to invert. Define

```text
half_p(z) = ((p+1)/2 * z) mod p.
```

Because `2*((p+1)/2) = p+1`, Lean proves

```text
2*half_p(z) = z (mod p),       0 <= half_p(z) < p.
```

The state is `(delta2,f,g,B,D,ticks)`, initialized to
`(1,p,x,0,1,0)` modulo `p`. Its active branches are:

| Branch | Condition | `(delta2,f,g)` output | `(B,D)` output |
|---|---|---|---|
| even | `g` even | `(delta2+2,f,g/2)` | `(B,half_p(D))` |
| swap | `g` odd, `delta2>0` | `(2-delta2,g,(g-f)/2)` | `(D,half_p(D-B))` |
| add | `g` odd, `delta2<=0` | `(delta2+2,f,(g+f)/2)` | `(B,half_p(D+B))` |

`g=0` remains absorbing. Theorems `step_modInvariant` and
`walk_modInvariant` prove the congruences parametrically. `terminal_inverse`
proves

```text
f^2=1  ->  (B*f)*x = 1 (mod p).
```

This is the same modular-cofactor method documented by libsecp256k1: its
variables `d,e` maintain `d*x=f` and `e*x=g` modulo the odd modulus, applying
modular division by two at every divstep. The batched implementation delays
the divisions, but it does not need growing `t+2`-bit persistent cofactors.

Primary references:

- Bernstein--Yang, *Fast constant-time gcd computation and modular
  inversion*, especially paragraphs 8.1--8.3 and the transition-matrix bounds:
  <https://gcd.cr.yp.to/safegcd-20190413.pdf>.
- libsecp256k1, `doc/safegcd_implementation.md`, sections 2--4:
  <https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md>.

### Exact lane envelope

For `0 < p < 2^n` and `0 <= x < p`, Lean proves for every public tick:

| Register | Range | Lanes |
|---|---|---:|
| `f` | `[-(2^n-1), 2^n-1]` | `n+1` signed |
| `g` | `[-(2^n-1), 2^n-1]` | `n+1` signed |
| `B` | `[0,p)` | `n` unsigned |
| `D` | `[0,p)` | `n` unsigned |
| `delta2` | `[-(2*ticks+1), 2*ticks+1]` | `1+ceil(log2(2N+2))` signed |
| `ticks` | `[0,N]` | `ceil(log2(N+1))` unsigned |

At n=256 and N=590, 724, or 742 this is exactly

```text
f 257, g 257, B 256, D 256, delta2 12, ticks 10
state total = 1,048 lanes.
```

The 256 coefficient lanes are also necessary in this representation: the
all-input n=8 and n=12 regressions reach canonical coefficients 254 and 4,094.

### 62-step batching alternative

The libsecp-style block route is also fixed-width, but it is not the selected
gate model here. For a 62-step block the exact obligations are:

- prove `|u|+|v| <= 2^62` and `|q|+|r| <= 2^62` for the scaled block matrix;
- allocate 64 signed bits per matrix entry in the inclusive worst case
  (`+2^62` is reachable on an all-even prefix);
- retain modular cofactors in `(-2p,p)`, requiring 258 signed bits each;
- provide up to 320 signed accumulator bits while forming and correcting each
  matrix row before the exact 62-bit division;
- prove the correction multiple cancels the low 62 bits and returns each
  cofactor to `(-2p,p)`.

These are the ranges explained in the libsecp document. A quantum circuit
would additionally need exact constant/signed multipliers and their cleanup;
no CCX advantage follows merely from the smaller number of full-width updates.

## 2. Why local tag-free replay is impossible

For modulus 5, all three following predecessors have odd `f`, canonical
`B,D`, distinct active branches, and the same post-state:

```text
post = ( 1,  1, 1, 1, 1, 1)

even predecessor = (-1,  1, 2, 1, 2, 0)
swap predecessor = ( 1, -1, 1, 4, 1, 0)
add  predecessor = (-1,  1, 1, 1, 1, 0)
```

Theorems `collision_even`, `collision_swap`, `collision_add`,
`no_tag_free_local_inverse`, and `three_distinct_tags_necessary` kernel-check
the collision and its consequence. The sign of post-`delta2`, the parity of
post-`g`, and both modular cofactors are therefore insufficient in general.

The exact tagged inverse is:

```text
even: (delta'-2, f',       2g',      B',             2D' mod p)
swap: (2-delta', f'-2g',   f',       B'-2D' mod p,   B')
add:  (delta'-2, f',       2g'-f',   B',             2D'-B' mod p)
```

`unstep_step` proves it, and `replay_trace` proves arbitrary-N Bennett replay.
The zero branch is the fourth two-bit code word. Absorbing padding could be
recognized from the public reverse index and the retained tick count, but the
three active branches already force two local tag bits.

### One-bit global transcript tradeoff

Globally, the swap bit is determined by the parity bit and the **pre-step**
delta sign. Thus one parity bit per tick plus delta checkpoints can regenerate
the swap sequence by scanning each block forward. For block length `L`, an
abstract storage schedule uses

```text
N parity bits + (ceil(N/L)-1)*H delta-checkpoint bits + L reusable sigma bits.
```

The integer optima are 747 lanes at `(N,L,H)=(590,85,12)`, 899 at
`(724,91,12)`, and 919 at `(742,93,12)`. This is **not tag-free** and is not a
physical circuit receipt: a coherent forward-scan decoder, scratch cleanup,
and its extra CCX count remain to be proved. It is included only as the
minimal credible block-level alternative to `2N` local tags.

## 3. n=8 and n=12 receipts

The Lean statements are parametric; `n8_all_inputs_fit` and
`n12_all_inputs_fit` instantiate the fixed-width theorem for every positive
odd modulus and every `0 <= x < p`. `unstep_step`, `replay_trace`, and
`terminal_inverse` apply to both widths without enumeration.

Python independently exhausts every admissible input:

| n | Inputs | Sharp horizon | max value abs | max unsigned `B,D` | max `|delta2|` |
|---:|---:|---:|---:|---:|---:|
| 8 | 16,384 | 19 | 255 | 254 | 15 |
| 12 | 4,194,304 | 28 | 4,095 | 4,094 | 23 |

For every row it checks canonical bounds, both modular invariants, the exact
one-step inverse, full tagged replay, gcd, and terminal inverse. The n=12 run
completed in about 175 seconds on this machine.

Lean check:

```text
BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/DivstepTight.lean
rc=0 elapsed=3s
```

## 4. Repricing

This table deliberately keeps Brief 26's conservative literal skeleton and
changes only what is now proved: `C=256` rather than `C=N+2`, and two local
tag bits rather than three raw predicates. It charges every CCX at exactly
4 T under the leader's lowering and credits zero measured erasures.

```text
CCX/cell = 9*257 + 8*256 + 4*12 - 13 = 4,396
CCX/walk = N*4,396
CCX/clean wrapper = 2*N*4,396
base support = state 1,048 + output 256 + scratch 258 = 1,562
challenge Q = 856 - 580 + base support + history
T = 1,175,358,444 + 116*4*(CCX/clean wrapper).
```

| N | Replay model | CCX/walk | CCX/clean wrapper | History | Q | T | Q×T | vs leader |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 590 | **proved local 2-bit tags** | 2,593,640 | 5,187,280 | 1,180 | 3,018 | 3,582,256,364 | 10,811,249,706,552 | +48.921858665% |
| 590 | parity/checkpoint screen | 2,593,640 | 5,187,280 | 747 | 2,585 | 3,582,256,364 | 9,260,132,700,940 | +27.555667544% |
| 590 | impossible zero-history sensitivity | 2,593,640 | 5,187,280 | 0 | 1,838 | 3,582,256,364 | 6,584,187,197,032 | -9.304712980% |
| 724 | **proved local 2-bit tags** | 3,182,704 | 6,365,408 | 1,448 | 3,286 | 4,128,907,756 | 13,567,590,886,216 | +86.889666525% |
| 724 | parity/checkpoint screen | 3,182,704 | 6,365,408 | 899 | 2,737 | 4,128,907,756 | 11,300,820,528,172 | +55.665556080% |
| 724 | impossible zero-history sensitivity | 3,182,704 | 6,365,408 | 0 | 1,838 | 4,128,907,756 | 7,588,932,455,528 | +4.535364295% |
| 742 | **proved local 2-bit tags** | 3,261,832 | 6,523,664 | 1,484 | 3,322 | 4,202,338,540 | 13,960,168,629,880 | +92.297312158% |
| 742 | parity/checkpoint screen | 3,261,832 | 6,523,664 | 919 | 2,757 | 4,202,338,540 | 11,585,847,354,780 | +59.591718729% |
| 742 | impossible zero-history sensitivity | 3,261,832 | 6,523,664 | 0 | 1,838 | 4,202,338,540 | 7,723,898,236,520 | +6.394479153% |

These are exact values of the stated arithmetic model, not a physical circuit
receipt. They are optimistic because `4,396` is inherited from the scaled-
cofactor skeleton: canonical `half_p` needs a conditional modulus add and
cleanup that the old shift did not. Adding that missing cost can only worsen
the table.

## 5. Remaining obligations and stop rule

The fixed-width theorem closes the `C_t=t+2` blocker. It does **not** close:

1. a coherent fixed-width modular-halving `Straight` circuit and exact count;
2. a 340-lane product/packing invariant—four separate value/cofactor words
   already occupy 1,026 lanes before delta and ticks;
3. a local tag-free decoder (now refuted on the general domain), or a proved
   coherent parity/checkpoint decoder with its gate overhead;
4. the unconditional 590/724/742 half-delta termination theorem;
5. a complete support/count/record/coherence receipt and Figure 15 bridge.

Do not open an Entrant patch from this route. Reopen C7b only if a stronger
reachable-state-specific decoder removes essentially all history **and** a
physical packed-ring cell beats the impossible zero-history sensitivity by
enough to clear 10%; the current conservative cell cannot do so.
