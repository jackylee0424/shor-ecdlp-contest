import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import ShorECDLP.Challenge.StraightLine

/-!
# Half-delta divsteps: exact recurrence and algebraic certificate interface

`delta2` is twice Bernstein--Yang's half-integer delta.  Thus the initial
delta is `1/2`, represented by `delta2 = 1`, and the three nonterminal updates
are `2-delta2`, `2+delta2`, and `2+delta2`.

The integer matrix is scaled: after `ticks` nonterminal steps,

  `2^ticks * [f,g]ᵀ = [[a,b],[c,d]] * [f₀,g₀]ᵀ`.

This file proves the recurrence, absorption rule, parity preservation, and
matrix identities.  It intentionally does not claim the external 590-step
convex-hull certificate has been replayed in Lean.
-/

namespace ShorECDLP.DivstepM1

set_option linter.unusedSimpArgs false

structure State where
  delta2 : Int
  f : Int
  g : Int
  a : Int
  b : Int
  c : Int
  d : Int
  ticks : Nat
deriving DecidableEq, Repr

def init (f g : Int) : State :=
  ⟨1, f, g, 1, 0, 0, 1, 0⟩

/-- The selected half-delta recurrence.  `g=0` is made explicitly absorbing,
including the matrix/transcript state, so fixed-horizon padding is exact. -/
def step (s : State) : State :=
  if s.g = 0 then s
  else if Even s.g then
    ⟨s.delta2 + 2, s.f, s.g / 2,
      2 * s.a, 2 * s.b, s.c, s.d, s.ticks + 1⟩
  else if 0 < s.delta2 then
    ⟨2 - s.delta2, s.g, (s.g - s.f) / 2,
      2 * s.c, 2 * s.d, s.c - s.a, s.d - s.b, s.ticks + 1⟩
  else
    ⟨s.delta2 + 2, s.f, (s.g + s.f) / 2,
      2 * s.a, 2 * s.b, s.c + s.a, s.d + s.b, s.ticks + 1⟩

def walk : Nat → State → State
  | 0, s => s
  | k + 1, s => walk k (step s)

@[simp] theorem walk_zero (s : State) : walk 0 s = s := rfl
@[simp] theorem walk_succ (k : Nat) (s : State) : walk (k+1) s = walk k (step s) := rfl

theorem step_of_g_zero {s : State} (h : s.g = 0) : step s = s := by
  simp [step, h]

theorem walk_of_g_zero {s : State} (h : s.g = 0) (k : Nat) : walk k s = s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [walk_succ, step_of_g_zero h]
      exact ih h

def MatrixInvariant (f0 g0 : Int) (s : State) : Prop :=
  (2 : Int) ^ s.ticks * s.f = s.a * f0 + s.b * g0 ∧
  (2 : Int) ^ s.ticks * s.g = s.c * f0 + s.d * g0

@[simp] theorem init_matrixInvariant (f0 g0 : Int) :
    MatrixInvariant f0 g0 (init f0 g0) := by
  simp [MatrixInvariant, init]

theorem odd_sub_odd {x y : Int} (hx : Odd x) (hy : Odd y) : Even (x-y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a-b, by ring⟩

theorem odd_add_odd {x y : Int} (hx : Odd x) (hy : Odd y) : Even (x+y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a+b+1, by ring⟩

theorem odd_of_not_even {x : Int} (h : ¬ Even x) : Odd x := by
  exact Int.not_even_iff_odd.mp h

theorem step_f_odd {s : State} (hf : Odd s.f) : Odd (step s).f := by
  unfold step
  split
  · exact hf
  split
  · exact hf
  split
  · exact odd_of_not_even ‹¬ Even s.g›
  · exact hf

theorem step_matrixInvariant {f0 g0 : Int} {s : State}
    (hf : Odd s.f) (hmat : MatrixInvariant f0 g0 s) :
    MatrixInvariant f0 g0 (step s) := by
  unfold step
  split
  · simpa [MatrixInvariant] using hmat
  split
  · rename_i hg0 heven
    have hhalf : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even heven
    rcases hmat with ⟨hfmat, hgmat⟩
    constructor <;> simp only [MatrixInvariant, State.ticks, State.f, State.g,
      State.a, State.b, State.c, State.d, pow_succ]
    · calc
        2 ^ s.ticks * 2 * s.f = 2 * (2 ^ s.ticks * s.f) := by ring
        _ = (2 * s.a) * f0 + (2 * s.b) * g0 := by rw [hfmat]; ring
    · calc
        2 ^ s.ticks * 2 * (s.g / 2) = 2 ^ s.ticks * (2 * (s.g / 2)) := by ring
        _ = 2 ^ s.ticks * s.g := by rw [hhalf]
        _ = s.c * f0 + s.d * g0 := hgmat
  · split
    · rename_i hg0 hneven hdelta
      have hgodd : Odd s.g := odd_of_not_even hneven
      have hdiff : Even (s.g - s.f) := odd_sub_odd hgodd hf
      have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
        Int.two_mul_ediv_two_of_even hdiff
      rcases hmat with ⟨hfmat, hgmat⟩
      constructor <;> simp only [MatrixInvariant, State.ticks, State.f, State.g,
        State.a, State.b, State.c, State.d, pow_succ]
      · calc
          2 ^ s.ticks * 2 * s.g = 2 * (2 ^ s.ticks * s.g) := by ring
          _ = (2 * s.c) * f0 + (2 * s.d) * g0 := by rw [hgmat]; ring
      · calc
          2 ^ s.ticks * 2 * ((s.g - s.f) / 2) =
              2 ^ s.ticks * (2 * ((s.g - s.f) / 2)) := by ring
          _ = 2 ^ s.ticks * (s.g - s.f) := by rw [hhalf]
          _ = 2 ^ s.ticks * s.g - 2 ^ s.ticks * s.f := by ring
          _ = (s.c * f0 + s.d * g0) - (s.a * f0 + s.b * g0) := by
            rw [hfmat, hgmat]
          _ = (s.c - s.a) * f0 + (s.d - s.b) * g0 := by ring
    · rename_i hg0 hneven hdelta
      have hgodd : Odd s.g := odd_of_not_even hneven
      have hsum : Even (s.g + s.f) := odd_add_odd hgodd hf
      have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
        Int.two_mul_ediv_two_of_even hsum
      rcases hmat with ⟨hfmat, hgmat⟩
      constructor <;> simp only [MatrixInvariant, State.ticks, State.f, State.g,
        State.a, State.b, State.c, State.d, pow_succ]
      · calc
          2 ^ s.ticks * 2 * s.f = 2 * (2 ^ s.ticks * s.f) := by ring
          _ = (2 * s.a) * f0 + (2 * s.b) * g0 := by rw [hfmat]; ring
      · calc
          2 ^ s.ticks * 2 * ((s.g + s.f) / 2) =
              2 ^ s.ticks * (2 * ((s.g + s.f) / 2)) := by ring
          _ = 2 ^ s.ticks * (s.g + s.f) := by rw [hhalf]
          _ = 2 ^ s.ticks * s.g + 2 ^ s.ticks * s.f := by ring
          _ = (s.c * f0 + s.d * g0) + (s.a * f0 + s.b * g0) := by
            rw [hfmat, hgmat]
          _ = (s.c + s.a) * f0 + (s.d + s.b) * g0 := by ring

theorem walk_f_odd {s : State} (hf : Odd s.f) (k : Nat) : Odd (walk k s).f := by
  induction k generalizing s with
  | zero => exact hf
  | succ k ih => exact ih (step_f_odd hf)

theorem walk_matrixInvariant {f0 g0 : Int} {s : State}
    (hf : Odd s.f) (hmat : MatrixInvariant f0 g0 s) (k : Nat) :
    MatrixInvariant f0 g0 (walk k s) := by
  induction k generalizing s with
  | zero => exact hmat
  | succ k ih => exact ih (step_f_odd hf) (step_matrixInvariant hf hmat)

theorem init_walk_matrixInvariant {f0 g0 : Int} (hf : Odd f0) (k : Nat) :
    MatrixInvariant f0 g0 (walk k (init f0 g0)) :=
  walk_matrixInvariant hf (init_matrixInvariant f0 g0) k

/-- What a future kernel-replayed 590-step hull certificate must provide. -/
def TerminatesBy (bound : Nat) : Prop :=
  ∀ f0 g0 : Int, Odd f0 → 0 ≤ g0 → g0 ≤ f0 →
    (walk bound (init f0 g0)).g = 0

/-- Once termination and `|f|=1` are supplied, the scaled transition matrix
row gives the exact Bezout relation used to decode the modular inverse. -/
theorem terminal_bezout {f0 g0 : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) :
    let s := walk k (init f0 g0)
    s.g = 0 ∧ (2 : Int) ^ s.ticks * s.f = s.a * f0 + s.b * g0 := by
  exact ⟨hg, (init_walk_matrixInvariant hf k).1⟩

/-- secp256k1's modulus is below the exact 590-step threshold printed by the
external safegcd-bounds certificate.  This arithmetic fact is kernel checked;
the hull-to-termination implication is not imported here. -/
def hull590Limit : Nat :=
  0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2

def secp256k1P : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

theorem secp256k1_lt_hull590Limit : secp256k1P < hull590Limit := by
  norm_num [secp256k1P, hull590Limit]

/-! ## Exhaustive n=8 regression (kernel `decide`, no native evaluator) -/

def n8State (f g : Fin 256) : State := init (Int.ofNat f.val) (Int.ofNat g.val)

theorem n8_terminates_19 :
    ∀ f g : Fin 256, f.val % 2 = 1 → g.val < f.val →
      (walk 19 (n8State f g)).g = 0 := by
  decide +kernel

theorem n8_18_is_insufficient :
    (walk 18 (init 237 235)).g ≠ 0 := by
  decide +kernel

theorem n8_worst_witness_terminates_at_19 :
    (walk 19 (init 237 235)).g = 0 := by
  decide +kernel

/-! ## Exact n=8 truth-table circuit baseline

This is an exact fixed-width `Straight` circuit, but deliberately not the
scalable ripple divstep cell.  It preserves the 16 input bits and computes the
19-step terminal `(f,b,ticks)` receipt into 26 clean output bits by one
constant-equality row for every admissible `(odd f,g<f)`.  The scaled matrix
coefficient `b`, together with terminal `f` and `ticks`, is the packed
transition data from `terminal_bezout`.
-/

open ShorECDLP.Challenge
open ShorECDLP.Classical
open ShorECDLP.Paper2607_13816

def n8InputWires : List Wire := List.range 16
def n8OutputWires : List Wire := List.range' 16 26
def n8Flag : Wire := 42
def n8Scratch : List Wire := List.range' 43 14
def n8Support : List Wire := List.range 57

def n8Rows : List (Nat × Nat) :=
  (List.range 256).flatMap fun f =>
    if f % 2 = 1 then (List.range f).map fun g => (f, g) else []

theorem n8Rows_length : n8Rows.length = 16384 := by
  decide +kernel

def twosComplement (width : Nat) (x : Int) : Nat :=
  (x % (2 : Int) ^ width).toNat

def n8OutputWord (f g : Nat) : Nat :=
  let s := walk 19 (init (Int.ofNat f) (Int.ofNat g))
  twosComplement 9 s.f +
    2 ^ 9 * twosComplement 12 s.b +
    2 ^ 21 * s.ticks

def n8RowTargets (f g : Nat) : List Wire :=
  (List.range 26).filterMap fun i =>
    if (n8OutputWord f g).testBit i then some (16 + i) else none

def n8RowValue (f g : Nat) : Nat := f + 256 * g

def n8RowCircuit (f g : Nat) : Circuit :=
  let compute := computeEqConst n8InputWires (n8RowValue f g) n8Flag n8Scratch
  (compute ++ (n8RowTargets f g).map (Gate.CX n8Flag)) ++ compute

def n8ForwardCircuit : Circuit :=
  n8Rows.flatMap fun row => n8RowCircuit row.1 row.2

def n8ReverseCircuit : Circuit := n8ForwardCircuit.adjoint
def n8ForwardReverseCircuit : Circuit := n8ForwardCircuit ++ n8ReverseCircuit

def circuitStraight {n start : Nat} : Circuit → Straight n start start
  | [] => .done
  | gate :: gates => .gate (.literal gate) (circuitStraight gates)

def n8ForwardStraight : Straight 0 0 0 := circuitStraight n8ForwardCircuit
def n8ReverseStraight : Straight 0 0 0 := circuitStraight n8ReverseCircuit

theorem n8RowCircuit_toffoliCount (f g : Nat) :
    eeaToffoliCount (n8RowCircuit f g) = 58 := by
  have henough : n8InputWires.length - 2 ≤ n8Scratch.length := by decide
  have hcx : eeaToffoliCount
      ((n8RowTargets f g).map (Gate.CX n8Flag)) = 0 := by
    induction n8RowTargets f g with
    | nil => rfl
    | cons target targets ih =>
        simpa [eeaToffoliCount, Function.comp_def] using ih
  unfold n8RowCircuit
  dsimp only
  rw [eeaToffoliCount_append, eeaToffoliCount_append,
    computeEqConst_toffoliCount n8InputWires (n8RowValue f g)
      n8Flag n8Scratch henough, hcx]
  norm_num [mcxVChainToffoliCost, n8InputWires]

private theorem flatMap_n8RowCircuit_toffoliCount (rows : List (Nat × Nat)) :
    eeaToffoliCount (rows.flatMap fun row => n8RowCircuit row.1 row.2) =
      rows.length * 58 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatMap_cons, eeaToffoliCount_append, ih,
        n8RowCircuit_toffoliCount, List.length_cons]
      omega

theorem n8ForwardCircuit_toffoliCount :
    eeaToffoliCount n8ForwardCircuit = 950272 := by
  rw [n8ForwardCircuit, flatMap_n8RowCircuit_toffoliCount, n8Rows_length]

theorem n8ReverseCircuit_toffoliCount :
    eeaToffoliCount n8ReverseCircuit = 950272 := by
  rw [n8ReverseCircuit, eeaToffoliCount_adjoint,
    n8ForwardCircuit_toffoliCount]

theorem n8ForwardReverseCircuit_toffoliCount :
    eeaToffoliCount n8ForwardReverseCircuit = 1900544 := by
  rw [n8ForwardReverseCircuit, eeaToffoliCount_append,
    n8ForwardCircuit_toffoliCount, n8ReverseCircuit_toffoliCount]

theorem circuitStraight_gateSlots {n start : Nat} (circuit : Circuit) :
    (circuitStraight (n := n) (start := start) circuit).gateSlots = circuit.length := by
  induction circuit with
  | nil => rfl
  | cons gate gates ih =>
      simp [circuitStraight, Straight.gateSlots, ih, Nat.add_comm]

theorem n8ForwardStraight_gateSlots :
    n8ForwardStraight.gateSlots = n8ForwardCircuit.length := by
  exact circuitStraight_gateSlots n8ForwardCircuit

theorem n8ForwardReverse_is_explicit_adjoint :
    n8ForwardReverseCircuit = n8ForwardCircuit ++ n8ForwardCircuit.adjoint := rfl

end ShorECDLP.DivstepM1
