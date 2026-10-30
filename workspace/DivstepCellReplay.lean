import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf

/-!
# Exact reversible replay model for a half-delta divstep cell

This file deliberately separates the reversible arithmetic contract from a
future physical lowering.  Only the two transition-matrix entries needed for
inverse recovery are retained: if

  `2^ticks * f = a*f₀ + b*g₀` and
  `2^ticks * g = c*f₀ + d*g₀`,

then `(b,d)` is closed under every divstep branch.  A two-bit encoding of
`Branch` is therefore sufficient replay information; the unused matrix row is
not required by the circuit state.
-/

namespace ShorECDLP.DivstepCell

set_option linter.unusedSimpArgs false

/-- The exact arithmetic state retained by the proposed cell. -/
structure Core where
  delta2 : Int
  f : Int
  g : Int
  b : Int
  d : Int
  ticks : Nat
deriving DecidableEq, Repr

def init (f g : Int) : Core := ⟨1, f, g, 0, 1, 0⟩

/-- Four mutually exclusive branches.  `zero` is absorbing padding. -/
inductive Branch where
  | zero | even | swap | add
deriving DecidableEq, Repr

def branch (s : Core) : Branch :=
  if s.g = 0 then .zero
  else if Even s.g then .even
  else if 0 < s.delta2 then .swap
  else .add

/-- The `(delta2,f,g,b,d)` projection of `DivstepMath.step`. -/
def step (s : Core) : Core :=
  if s.g = 0 then s
  else if Even s.g then
    ⟨s.delta2 + 2, s.f, s.g / 2, 2 * s.b, s.d, s.ticks + 1⟩
  else if 0 < s.delta2 then
    ⟨2 - s.delta2, s.g, (s.g - s.f) / 2,
      2 * s.d, s.d - s.b, s.ticks + 1⟩
  else
    ⟨s.delta2 + 2, s.f, (s.g + s.f) / 2,
      2 * s.b, s.d + s.b, s.ticks + 1⟩

/-- Local copy of the full state from `workspace/DivstepMath.lean`, used only
to state the refinement boundary without editing that earlier artifact. -/
structure MathState where
  delta2 : Int
  f : Int
  g : Int
  a : Int
  b : Int
  c : Int
  d : Int
  ticks : Nat
deriving DecidableEq, Repr

def mathStep (s : MathState) : MathState :=
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

def project (s : MathState) : Core :=
  ⟨s.delta2, s.f, s.g, s.b, s.d, s.ticks⟩

/-- Exact one-cell refinement to the recurrence of `DivstepMath`: discarding
the unused `(a,c)` row commutes with a step. -/
theorem project_mathStep (s : MathState) :
    project (mathStep s) = step (project s) := by
  by_cases hz : s.g = 0
  · simp [mathStep, step, project, hz]
  by_cases he : Even s.g
  · simp [mathStep, step, project, hz, he]
  by_cases hd : 0 < s.delta2
  · simp [mathStep, step, project, hz, he, hd]
  · simp [mathStep, step, project, hz, he, hd]

/-- One forward cell emits the exact branch needed by its literal adjoint. -/
def forwardCell (s : Core) : Core × Branch := (step s, branch s)

/-- Arithmetic inverse selected by the retained branch.  Its correctness only
requires the standard reachable-state invariant that `f` is odd. -/
def unstep : Branch → Core → Core
  | .zero, s => s
  | .even, s =>
      ⟨s.delta2 - 2, s.f, 2 * s.g, s.b / 2, s.d, s.ticks - 1⟩
  | .swap, s =>
      ⟨2 - s.delta2, s.f - 2 * s.g, s.f,
        s.b / 2 - s.d, s.b / 2, s.ticks - 1⟩
  | .add, s =>
      ⟨s.delta2 - 2, s.f, 2 * s.g - s.f,
        s.b / 2, s.d - s.b / 2, s.ticks - 1⟩

theorem odd_sub_odd {x y : Int} (hx : Odd x) (hy : Odd y) : Even (x-y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a-b, by ring⟩

theorem odd_add_odd {x y : Int} (hx : Odd x) (hy : Odd y) : Even (x+y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a+b+1, by ring⟩

theorem odd_of_not_even {x : Int} (h : ¬ Even x) : Odd x :=
  Int.not_even_iff_odd.mp h

theorem step_f_odd {s : Core} (hf : Odd s.f) : Odd (step s).f := by
  unfold step
  split
  · exact hf
  split
  · exact hf
  split
  · exact odd_of_not_even ‹¬ Even s.g›
  · exact hf

/-- The branch-tagged cell is injective on the reachable odd-`f` domain. -/
theorem unstep_step {s : Core} (hf : Odd s.f) :
    unstep (branch s) (step s) = s := by
  by_cases hz : s.g = 0
  · simp [branch, step, hz, unstep]
  by_cases he : Even s.g
  · have hg : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even he
    simp [branch, step, hz, he, unstep, hg]
  by_cases hd : 0 < s.delta2
  · have hgodd : Odd s.g := odd_of_not_even he
    have hdiff : Even (s.g - s.f) := odd_sub_odd hgodd hf
    have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
      Int.two_mul_ediv_two_of_even hdiff
    simp [branch, step, hz, he, hd, unstep, hhalf]
  · have hgodd : Odd s.g := odd_of_not_even he
    have hsum : Even (s.g + s.f) := odd_add_odd hgodd hf
    have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
      Int.two_mul_ediv_two_of_even hsum
    simp [branch, step, hz, he, hd, unstep, hhalf]

def walk : Nat → Core → Core
  | 0, s => s
  | n + 1, s => walk n (step s)

def trace : Nat → Core → Core × List Branch
  | 0, s => (s, [])
  | n + 1, s =>
      let next := forwardCell s
      let rest := trace n next.1
      (rest.1, next.2 :: rest.2)

def replay : List Branch → Core → Core
  | [], s => s
  | tag :: tags, s => unstep tag (replay tags s)

@[simp] theorem trace_fst (n : Nat) (s : Core) :
    (trace n s).1 = walk n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [trace, forwardCell, walk, ih]

theorem walk_f_odd {s : Core} (hf : Odd s.f) (n : Nat) :
    Odd (walk n s).f := by
  induction n generalizing s with
  | zero => exact hf
  | succ n ih => exact ih (step_f_odd hf)

/-! ## Conservative, fully parametric lane envelopes -/

def ValueBound (M : Int) (s : Core) : Prop :=
  -M ≤ s.f ∧ s.f ≤ M ∧ -M ≤ s.g ∧ s.g ≤ M

def DeltaBound (s : Core) : Prop :=
  -((2 : Int) * s.ticks + 1) ≤ s.delta2 ∧
    s.delta2 ≤ (2 : Int) * s.ticks + 1

def CoeffBound (s : Core) : Prop :=
  -((2 : Int) ^ s.ticks) ≤ s.b ∧ s.b ≤ (2 : Int) ^ s.ticks ∧
    -((2 : Int) ^ s.ticks) ≤ s.d ∧ s.d ≤ (2 : Int) ^ s.ticks

theorem step_valueBound {M : Int} {s : Core}
    (hf : Odd s.f) (h : ValueBound M s) : ValueBound M (step s) := by
  rcases h with ⟨hfl, hfu, hgl, hgu⟩
  by_cases hz : s.g = 0
  · simp [step, hz, ValueBound, hfl, hfu, hgl, hgu]
    omega
  by_cases he : Even s.g
  · have hhalf : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even he
    simp only [step, hz, he, if_false, if_true, ValueBound, Core.f, Core.g]
    constructor
    · exact hfl
    constructor
    · exact hfu
    constructor <;> omega
  by_cases hd : 0 < s.delta2
  · have hgodd : Odd s.g := odd_of_not_even he
    have hdiff : Even (s.g - s.f) := odd_sub_odd hgodd hf
    have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
      Int.two_mul_ediv_two_of_even hdiff
    simp only [step, hz, he, hd, if_false, if_true, ValueBound, Core.f, Core.g]
    constructor
    · exact hgl
    constructor
    · exact hgu
    constructor <;> omega
  · have hgodd : Odd s.g := odd_of_not_even he
    have hsum : Even (s.g + s.f) := odd_add_odd hgodd hf
    have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
      Int.two_mul_ediv_two_of_even hsum
    simp only [step, hz, he, hd, if_false, if_true, ValueBound, Core.f, Core.g]
    constructor
    · exact hfl
    constructor
    · exact hfu
    constructor <;> omega

theorem step_deltaBound {s : Core} (h : DeltaBound s) :
    DeltaBound (step s) := by
  rcases h with ⟨hl, hu⟩
  by_cases hz : s.g = 0
  · simpa [step, hz, DeltaBound] using And.intro hl hu
  by_cases he : Even s.g
  · simp only [step, hz, he, if_false, if_true, DeltaBound, Core.ticks,
      Core.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega
  by_cases hd : 0 < s.delta2
  · simp only [step, hz, he, hd, if_false, if_true, DeltaBound, Core.ticks,
      Core.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega
  · simp only [step, hz, he, hd, if_false, if_true, DeltaBound, Core.ticks,
      Core.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega

theorem step_coeffBound {s : Core} (h : CoeffBound s) :
    CoeffBound (step s) := by
  rcases h with ⟨hbl, hbu, hdl, hdu⟩
  by_cases hz : s.g = 0
  · simp [step, hz, CoeffBound, hbl, hbu, hdl, hdu]
  have hp : (2 : Int) ^ (s.ticks + 1) = 2 * (2 : Int) ^ s.ticks := by
    rw [pow_succ]
    ring
  by_cases he : Even s.g
  · simp only [step, hz, he, if_false, if_true, CoeffBound, Core.ticks,
      Core.b, Core.d, hp]
    constructor <;> omega
  by_cases hd : 0 < s.delta2
  · simp only [step, hz, he, hd, if_false, if_true, CoeffBound, Core.ticks,
      Core.b, Core.d, hp]
    constructor <;> omega
  · simp only [step, hz, he, hd, if_false, if_true, CoeffBound, Core.ticks,
      Core.b, Core.d, hp]
    constructor <;> omega

theorem walk_envelopes {M : Int} {s : Core}
    (hf : Odd s.f) (hv : ValueBound M s) (hd : DeltaBound s)
    (hc : CoeffBound s) (n : Nat) :
    ValueBound M (walk n s) ∧ DeltaBound (walk n s) ∧
      CoeffBound (walk n s) := by
  induction n generalizing s with
  | zero => exact ⟨hv, hd, hc⟩
  | succ n ih =>
      exact ih (step_f_odd hf) (step_valueBound hf hv)
        (step_deltaBound hd) (step_coeffBound hc)

@[simp] theorem init_deltaBound (f g : Int) : DeltaBound (init f g) := by
  simp [DeltaBound, init]

@[simp] theorem init_coeffBound (f g : Int) : CoeffBound (init f g) := by
  norm_num [CoeffBound, init]

theorem init_valueBound {M f g : Int}
    (hf0 : 0 ≤ f) (hfM : f ≤ M)
    (hg0 : 0 ≤ g) (hgM : g ≤ M) :
    ValueBound M (init f g) := by
  simp only [ValueBound, init, Core.f, Core.g]
  omega

/-- Structural all-input theorem used at n=8 and n=12: for every odd unsigned
input pair bounded by `M`, every public step uses `n+1` signed value bits when
`M=2^n-1`; delta and coefficient bounds follow the actual tick counter. -/
theorem unsigned_walk_envelopes {M f g : Int}
    (hfodd : Odd f) (hf0 : 0 ≤ f) (hfM : f ≤ M)
    (hg0 : 0 ≤ g) (hgM : g ≤ M) (n : Nat) :
    ValueBound M (walk n (init f g)) ∧
      DeltaBound (walk n (init f g)) ∧
      CoeffBound (walk n (init f g)) :=
  walk_envelopes hfodd (init_valueBound hf0 hfM hg0 hgM)
    (init_deltaBound f g) (init_coeffBound f g) n

/-- Bennett replay: every branch tag is consumed and the complete input state
is recovered.  A physical implementation may copy the terminal inverse before
this replay, leaving no quantum history behind. -/
theorem replay_trace {s : Core} (hf : Odd s.f) (n : Nat) :
    replay (trace n s).2 (trace n s).1 = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [trace, forwardCell]
      simp only [replay]
      rw [ih (step_f_odd hf)]
      exact unstep_step hf

/-! ## Parametric conservative resource receipt

The formula describes the explicit unitary skeleton documented in
`docs/DIVSTEP-CELL.md`: clean-v-chain nonzero test; two word Fredkin passes;
three controlled two's-complement negations; two mask/Cuccaro controlled adds;
an active controlled coefficient shift; and the delta update.  It is a
constructor target, not yet a theorem about a completed `Straight` value.
-/

def cellCCX (valueWidth coeffWidth deltaWidth : Nat) : Nat :=
  9 * valueWidth + 8 * coeffWidth + 4 * deltaWidth - 13

def walkCCX (N valueWidth coeffWidth deltaWidth : Nat) : Nat :=
  N * cellCCX valueWidth coeffWidth deltaWidth

def bennettCCX (N valueWidth coeffWidth deltaWidth : Nat) : Nat :=
  2 * walkCCX N valueWidth coeffWidth deltaWidth

theorem cellCCX_closed (v c h : Nat) :
    cellCCX v c h = 9*v + 8*c + 4*h - 13 := rfl

theorem bennettCCX_closed (N v c h : Nat) :
    bennettCCX N v c h = 2 * N * (9*v + 8*c + 4*h - 13) := by
  simp [bennettCCX, walkCCX, cellCCX, Nat.mul_assoc]

end ShorECDLP.DivstepCell
