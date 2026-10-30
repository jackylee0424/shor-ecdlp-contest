import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import Mathlib.Data.Int.ModEq

/-!
# Fixed-width modular cofactors for half-delta divsteps

The scaled `(b,d)` column in `DivstepCellReplay.lean` grows by one bit per
tick.  This file instead stores the unscaled residues `(B,D)` satisfying

  `f = B*x (mod p)` and `g = D*x (mod p)`.

Both residues are canonical in `[0,p)`.  Division by two is multiplication
by `2⁻¹ mod p`, implemented arithmetically by `halfMod`.  This removes both
the growing coefficient envelope and the terminal variable-power unscale.

The second result is negative but decisive: even with `(B,D)`, the post-state
does not determine the preceding branch on the general odd-`f` domain.  The
file exhibits three different valid predecessors (even/swap/add) with the
same post-state, proving that a local inverse needs at least three tag values
(two qubits in a binary register).
-/

namespace ShorECDLP.DivstepTight

set_option linter.unusedSimpArgs false

def canon (p x : Int) : Int := x % p

def Canonical (p x : Int) : Prop := 0 ≤ x ∧ x < p

theorem canon_canonical {p x : Int} (hp : 0 < p) : Canonical p (canon p x) := by
  constructor
  · exact Int.emod_nonneg x hp.ne'
  · exact Int.emod_lt_of_pos x hp

theorem canonical_emod {p x : Int} (hx : Canonical p x) : x % p = x := by
  exact Int.emod_eq_of_lt hx.1 hx.2

theorem canonical_modEq_eq {p x y : Int} (hx : Canonical p x)
    (hy : Canonical p y) (hxy : x ≡ y [ZMOD p]) : x = y := by
  have := hxy.eq
  simpa [canonical_emod hx, canonical_emod hy] using this

/-- Canonical division by two modulo the positive odd modulus `p`. -/
def halfMod (p x : Int) : Int := canon p (((p + 1) / 2) * x)

theorem odd_isCoprime_two {p : Int} (hp : Odd p) : IsCoprime p (2 : Int) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨k, rfl⟩ := hp
  calc
    Int.gcd (2 * k + 1) 2 = Int.gcd (1 + k * 2) 2 := by ring_nf
    _ = Int.gcd 1 2 := Int.gcd_add_mul_right_left 2 1 k
    _ = 1 := by norm_num [Int.gcd_def]

theorem odd_add_one_even {p : Int} (hp : Odd p) : Even (p + 1) := by
  obtain ⟨k, rfl⟩ := hp
  exact ⟨k + 1, by ring⟩

theorem two_mul_halfMod_modEq {p x : Int} (hp : Odd p) :
    2 * halfMod p x ≡ x [ZMOD p] := by
  have hdiv : 2 * ((p + 1) / 2) = p + 1 :=
    Int.two_mul_ediv_two_of_even (odd_add_one_even hp)
  have hmod := (Int.mod_modEq (((p + 1) / 2) * x) p).mul_left (2 : Int)
  calc
    2 * halfMod p x ≡ 2 * (((p + 1) / 2) * x) [ZMOD p] := hmod
    _ = (2 * ((p + 1) / 2)) * x := by ring
    _ = (p + 1) * x := by rw [hdiv]
    _ = x + p * x := by ring
    _ ≡ x [ZMOD p] := Int.modEq_add_fac_self

theorem halfMod_canonical {p x : Int} (hp : 0 < p) :
    Canonical p (halfMod p x) := canon_canonical hp

theorem cancel_two_modEq {p a b : Int} (hp : Odd p)
    (h : 2 * a ≡ 2 * b [ZMOD p]) : a ≡ b [ZMOD p] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  apply (odd_isCoprime_two hp).dvd_of_dvd_mul_right
  have heq : 2 * b - 2 * a = (b - a) * 2 := by ring
  rw [heq] at h
  exact h

/-- The exact arithmetic state.  `B,D` are always canonical residues, so
their width is the modulus width and is independent of `ticks`. -/
structure State where
  delta2 : Int
  f : Int
  g : Int
  B : Int
  D : Int
  ticks : Nat
deriving DecidableEq, Repr

def init (p x : Int) : State := ⟨1, p, x, canon p 0, canon p 1, 0⟩

inductive Branch where
  | zero | even | swap | add
deriving DecidableEq, Repr

def branch (s : State) : Branch :=
  if s.g = 0 then .zero
  else if Even s.g then .even
  else if 0 < s.delta2 then .swap
  else .add

def step (p : Int) (s : State) : State :=
  if s.g = 0 then s
  else if Even s.g then
    ⟨s.delta2 + 2, s.f, s.g / 2, s.B, halfMod p s.D, s.ticks + 1⟩
  else if 0 < s.delta2 then
    ⟨2 - s.delta2, s.g, (s.g - s.f) / 2,
      s.D, halfMod p (s.D - s.B), s.ticks + 1⟩
  else
    ⟨s.delta2 + 2, s.f, (s.g + s.f) / 2,
      s.B, halfMod p (s.D + s.B), s.ticks + 1⟩

def walk (p : Int) : Nat → State → State
  | 0, s => s
  | k + 1, s => walk p k (step p s)

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

theorem step_f_odd {p : Int} {s : State} (hf : Odd s.f) :
    Odd (step p s).f := by
  unfold step
  split
  · exact hf
  split
  · exact hf
  split
  · exact odd_of_not_even ‹¬ Even s.g›
  · exact hf

def CoeffCanonical (p : Int) (s : State) : Prop :=
  Canonical p s.B ∧ Canonical p s.D

theorem init_coeffCanonical {p x : Int} (hp : 0 < p) :
    CoeffCanonical p (init p x) := by
  exact ⟨canon_canonical hp, canon_canonical hp⟩

theorem step_coeffCanonical {p : Int} {s : State} (hp : 0 < p)
    (hc : CoeffCanonical p s) : CoeffCanonical p (step p s) := by
  rcases hc with ⟨hB, hD⟩
  by_cases hz : s.g = 0
  · simpa [step, hz, CoeffCanonical] using And.intro hB hD
  by_cases he : Even s.g
  · simp [step, hz, he, CoeffCanonical, hB, halfMod_canonical hp]
  by_cases hd : 0 < s.delta2
  · simp [step, hz, he, hd, CoeffCanonical, hD, halfMod_canonical hp]
  · simp [step, hz, he, hd, CoeffCanonical, hB, halfMod_canonical hp]

theorem walk_coeffCanonical {p : Int} {s : State} (hp : 0 < p)
    (hc : CoeffCanonical p s) (k : Nat) :
    CoeffCanonical p (walk p k s) := by
  induction k generalizing s with
  | zero => exact hc
  | succ k ih => exact ih (step_coeffCanonical hp hc)

def ModInvariant (p x : Int) (s : State) : Prop :=
  s.f ≡ s.B * x [ZMOD p] ∧ s.g ≡ s.D * x [ZMOD p]

theorem init_modInvariant (p x : Int) : ModInvariant p x (init p x) := by
  constructor
  · rw [Int.modEq_iff_dvd]
    refine ⟨-1, ?_⟩
    simp [init, canon]
  · simpa [init, canon] using (Int.mod_modEq 1 p).symm.mul_right x

theorem step_modInvariant {p x : Int} {s : State} (hp : Odd p)
    (hf : Odd s.f) (hi : ModInvariant p x s) :
    ModInvariant p x (step p s) := by
  rcases hi with ⟨hfi, hgi⟩
  by_cases hz : s.g = 0
  · simpa [step, hz, ModInvariant] using And.intro hfi hgi
  by_cases he : Even s.g
  · have hhalf : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even he
    constructor
    · simpa [step, hz, he, ModInvariant] using hfi
    · apply cancel_two_modEq hp
      calc
        2 * (step p s).g = s.g := by simp [step, hz, he, hhalf]
        _ ≡ s.D * x [ZMOD p] := hgi
        _ ≡ (2 * halfMod p s.D) * x [ZMOD p] :=
          (two_mul_halfMod_modEq hp).symm.mul_right x
        _ = 2 * ((step p s).D * x) := by simp [step, hz, he]; ring
  by_cases hd : 0 < s.delta2
  · have hgodd : Odd s.g := odd_of_not_even he
    have hdiff : Even (s.g - s.f) := odd_sub_odd hgodd hf
    have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
      Int.two_mul_ediv_two_of_even hdiff
    constructor
    · simpa [step, hz, he, hd, ModInvariant] using hgi
    · apply cancel_two_modEq hp
      calc
        2 * (step p s).g = s.g - s.f := by simp [step, hz, he, hd, hhalf]
        _ ≡ s.D * x - s.B * x [ZMOD p] := hgi.sub hfi
        _ = (s.D - s.B) * x := by ring
        _ ≡ (2 * halfMod p (s.D - s.B)) * x [ZMOD p] :=
          (two_mul_halfMod_modEq hp).symm.mul_right x
        _ = 2 * ((step p s).D * x) := by simp [step, hz, he, hd]; ring
  · have hgodd : Odd s.g := odd_of_not_even he
    have hsum : Even (s.g + s.f) := odd_add_odd hgodd hf
    have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
      Int.two_mul_ediv_two_of_even hsum
    constructor
    · simpa [step, hz, he, hd, ModInvariant] using hfi
    · apply cancel_two_modEq hp
      calc
        2 * (step p s).g = s.g + s.f := by simp [step, hz, he, hd, hhalf]
        _ ≡ s.D * x + s.B * x [ZMOD p] := hgi.add hfi
        _ = (s.D + s.B) * x := by ring
        _ ≡ (2 * halfMod p (s.D + s.B)) * x [ZMOD p] :=
          (two_mul_halfMod_modEq hp).symm.mul_right x
        _ = 2 * ((step p s).D * x) := by simp [step, hz, he, hd]; ring

theorem walk_f_odd {p : Int} {s : State} (hf : Odd s.f) (k : Nat) :
    Odd (walk p k s).f := by
  induction k generalizing s with
  | zero => exact hf
  | succ k ih => exact ih (step_f_odd hf)

theorem walk_modInvariant {p x : Int} {s : State} (hp : Odd p)
    (hf : Odd s.f) (hi : ModInvariant p x s) (k : Nat) :
    ModInvariant p x (walk p k s) := by
  induction k generalizing s with
  | zero => exact hi
  | succ k ih => exact ih (step_f_odd hf) (step_modInvariant hp hf hi)

/-- No variable power-of-two decoder remains: at a coprime terminal state,
the canonical inverse is simply `B*f mod p`. -/
theorem terminal_inverse {p x : Int} {s : State}
    (hi : ModInvariant p x s) (hsq : s.f * s.f = 1) :
    (s.B * s.f) * x ≡ 1 [ZMOD p] := by
  calc
    (s.B * s.f) * x = s.f * (s.B * x) := by ring
    _ ≡ s.f * s.f [ZMOD p] := hi.1.symm.mul_left s.f
    _ = 1 := hsq

/-! ## Two-bit tagged inverse and replay

The collision below rules out a local tag-free inverse, but the usual
three-way active tag (`even`, `swap`, `add`) is sufficient.  Absorbing
`zero` padding is a fourth code word. -/

def unstep (p : Int) : Branch → State → State
  | .zero, s => s
  | .even, s =>
      ⟨s.delta2 - 2, s.f, 2 * s.g, s.B, canon p (2 * s.D), s.ticks - 1⟩
  | .swap, s =>
      ⟨2 - s.delta2, s.f - 2 * s.g, s.f,
        canon p (s.B - 2 * s.D), s.B, s.ticks - 1⟩
  | .add, s =>
      ⟨s.delta2 - 2, s.f, 2 * s.g - s.f,
        s.B, canon p (2 * s.D - s.B), s.ticks - 1⟩

theorem canon_two_halfMod {p x : Int} (hp0 : 0 < p) (hpodd : Odd p)
    (hx : Canonical p x) : canon p (2 * halfMod p x) = x := by
  apply canonical_modEq_eq (canon_canonical hp0) hx
  exact (Int.mod_modEq (2 * halfMod p x) p).trans (two_mul_halfMod_modEq hpodd)

theorem restore_swap_B {p B D : Int} (hp0 : 0 < p) (hpodd : Odd p)
    (hB : Canonical p B) :
    canon p (D - 2 * halfMod p (D - B)) = B := by
  apply canonical_modEq_eq (canon_canonical hp0) hB
  calc
    canon p (D - 2 * halfMod p (D - B)) ≡
        D - 2 * halfMod p (D - B) [ZMOD p] := Int.mod_modEq _ _
    _ ≡ D - (D - B) [ZMOD p] :=
      Int.ModEq.rfl.sub (two_mul_halfMod_modEq hpodd)
    _ = B := by ring

theorem restore_add_D {p B D : Int} (hp0 : 0 < p) (hpodd : Odd p)
    (hD : Canonical p D) :
    canon p (2 * halfMod p (D + B) - B) = D := by
  apply canonical_modEq_eq (canon_canonical hp0) hD
  calc
    canon p (2 * halfMod p (D + B) - B) ≡
        2 * halfMod p (D + B) - B [ZMOD p] := Int.mod_modEq _ _
    _ ≡ (D + B) - B [ZMOD p] :=
      (two_mul_halfMod_modEq hpodd).sub Int.ModEq.rfl
    _ = D := by ring

theorem unstep_step {p : Int} {s : State} (hp0 : 0 < p) (hpodd : Odd p)
    (hf : Odd s.f) (hc : CoeffCanonical p s) :
    unstep p (branch s) (step p s) = s := by
  rcases hc with ⟨hB, hD⟩
  by_cases hz : s.g = 0
  · simp [branch, step, hz, unstep]
  by_cases he : Even s.g
  · have hg : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even he
    simp [branch, step, hz, he, unstep, hg, canon_two_halfMod hp0 hpodd hD]
  by_cases hd : 0 < s.delta2
  · have hgodd : Odd s.g := odd_of_not_even he
    have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
      Int.two_mul_ediv_two_of_even (odd_sub_odd hgodd hf)
    simp [branch, step, hz, he, hd, unstep, hhalf,
      restore_swap_B hp0 hpodd hB]
  · have hgodd : Odd s.g := odd_of_not_even he
    have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
      Int.two_mul_ediv_two_of_even (odd_add_odd hgodd hf)
    simp [branch, step, hz, he, hd, unstep, hhalf,
      restore_add_D hp0 hpodd hD]

def trace (p : Int) : Nat → State → State × List Branch
  | 0, s => (s, [])
  | k + 1, s =>
      let rest := trace p k (step p s)
      (rest.1, branch s :: rest.2)

def replay (p : Int) : List Branch → State → State
  | [], s => s
  | tag :: tags, s => unstep p tag (replay p tags s)

theorem trace_fst (p : Int) (k : Nat) (s : State) :
    (trace p k s).1 = walk p k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [trace, walk, ih]

theorem replay_trace {p : Int} {s : State} (hp0 : 0 < p) (hpodd : Odd p)
    (hf : Odd s.f) (hc : CoeffCanonical p s) (k : Nat) :
    replay p (trace p k s).2 (trace p k s).1 = s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [trace, replay]
      rw [ih (step_f_odd hf) (step_coeffCanonical hp0 hc)]
      exact unstep_step hp0 hpodd hf hc

/-! ## Fixed lane envelope -/

def ValueBound (M : Int) (s : State) : Prop :=
  -M ≤ s.f ∧ s.f ≤ M ∧ -M ≤ s.g ∧ s.g ≤ M

def DeltaBound (s : State) : Prop :=
  -((2 : Int) * s.ticks + 1) ≤ s.delta2 ∧
    s.delta2 ≤ (2 : Int) * s.ticks + 1

theorem step_valueBound {p M : Int} {s : State} (hf : Odd s.f)
    (hv : ValueBound M s) : ValueBound M (step p s) := by
  rcases hv with ⟨hfl, hfu, hgl, hgu⟩
  by_cases hz : s.g = 0
  · simp [step, hz, ValueBound, hfl, hfu, hgl, hgu]
    omega
  by_cases he : Even s.g
  · have hhalf : 2 * (s.g / 2) = s.g := Int.two_mul_ediv_two_of_even he
    simp only [step, hz, he, if_false, if_true, ValueBound, State.f, State.g]
    constructor
    · exact hfl
    constructor
    · exact hfu
    constructor <;> omega
  by_cases hd : 0 < s.delta2
  · have hgodd : Odd s.g := odd_of_not_even he
    have hhalf : 2 * ((s.g - s.f) / 2) = s.g - s.f :=
      Int.two_mul_ediv_two_of_even (odd_sub_odd hgodd hf)
    simp only [step, hz, he, hd, if_false, if_true, ValueBound, State.f, State.g]
    constructor
    · exact hgl
    constructor
    · exact hgu
    constructor <;> omega
  · have hgodd : Odd s.g := odd_of_not_even he
    have hhalf : 2 * ((s.g + s.f) / 2) = s.g + s.f :=
      Int.two_mul_ediv_two_of_even (odd_add_odd hgodd hf)
    simp only [step, hz, he, hd, if_false, if_true, ValueBound, State.f, State.g]
    constructor
    · exact hfl
    constructor
    · exact hfu
    constructor <;> omega

theorem step_deltaBound {p : Int} {s : State} (hd : DeltaBound s) :
    DeltaBound (step p s) := by
  rcases hd with ⟨hl, hu⟩
  by_cases hz : s.g = 0
  · simpa [step, hz, DeltaBound] using And.intro hl hu
  by_cases he : Even s.g
  · simp only [step, hz, he, if_false, if_true, DeltaBound, State.ticks,
      State.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega
  by_cases hdelta : 0 < s.delta2
  · simp only [step, hz, he, hdelta, if_false, if_true, DeltaBound, State.ticks,
      State.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega
  · simp only [step, hz, he, hdelta, if_false, if_true, DeltaBound, State.ticks,
      State.delta2, Nat.cast_add, Nat.cast_one]
    constructor <;> omega

theorem step_ticks_le (p : Int) (s : State) :
    (step p s).ticks ≤ s.ticks + 1 := by
  by_cases hz : s.g = 0
  · simp [step, hz]
  by_cases he : Even s.g
  · simp [step, hz, he]
  by_cases hd : 0 < s.delta2
  · simp [step, hz, he, hd]
  · simp [step, hz, he, hd]

theorem walk_ticks_le (p : Int) (s : State) (k : Nat) :
    (walk p k s).ticks ≤ s.ticks + k := by
  induction k generalizing s with
  | zero => simp [walk]
  | succ k ih =>
      rw [walk]
      have hs := step_ticks_le p s
      have hk := ih (step p s)
      omega

theorem walk_envelope {p M : Int} {s : State} (hp : 0 < p)
    (hf : Odd s.f) (hv : ValueBound M s) (hd : DeltaBound s)
    (hc : CoeffCanonical p s) (k : Nat) :
    ValueBound M (walk p k s) ∧ DeltaBound (walk p k s) ∧
      CoeffCanonical p (walk p k s) := by
  induction k generalizing s with
  | zero => exact ⟨hv, hd, hc⟩
  | succ k ih =>
      exact ih (step_f_odd hf) (step_valueBound hf hv)
        (step_deltaBound hd) (step_coeffCanonical hp hc)

theorem init_valueBound {p x M : Int} (hp0 : 0 ≤ p) (hpM : p ≤ M)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) : ValueBound M (init p x) := by
  simp only [ValueBound, init, State.f, State.g]
  omega

theorem init_deltaBound (p x : Int) : DeltaBound (init p x) := by
  norm_num [DeltaBound, init]

/-- Parametric all-input envelope.  If `p < 2^n`, then `f,g` need `n+1`
signed bits while `B,D` need exactly `n` unsigned bits, for every tick. -/
theorem unsigned_walk_envelope {p x M : Int} (hp : 0 < p) (hpodd : Odd p)
    (hpM : p ≤ M) (hx0 : 0 ≤ x) (hxM : x ≤ M) (k : Nat) :
    ValueBound M (walk p k (init p x)) ∧
      DeltaBound (walk p k (init p x)) ∧
      CoeffCanonical p (walk p k (init p x)) :=
  walk_envelope hp hpodd (init_valueBound hp.le hpM hx0 hxM)
    (init_deltaBound p x) (init_coeffCanonical hp) k

theorem n8_all_inputs_fit {p x : Int} (hp : 0 < p) (hpodd : Odd p)
    (hp8 : p < 2^8) (hx0 : 0 ≤ x) (hxp : x < p) (k : Nat) :
    let s := walk p k (init p x)
    ValueBound (2^8-1) s ∧ 0 ≤ s.B ∧ s.B < 2^8 ∧
      0 ≤ s.D ∧ s.D < 2^8 := by
  dsimp only
  have h := unsigned_walk_envelope hp hpodd (M := (2^8-1 : Int))
    (by omega) hx0 (by omega) k
  rcases h with ⟨hv, _, ⟨hB, hD⟩⟩
  rcases hB with ⟨hB0, hBp⟩
  rcases hD with ⟨hD0, hDp⟩
  exact ⟨hv, hB0, by omega, hD0, by omega⟩

theorem n12_all_inputs_fit {p x : Int} (hp : 0 < p) (hpodd : Odd p)
    (hp12 : p < 2^12) (hx0 : 0 ≤ x) (hxp : x < p) (k : Nat) :
    let s := walk p k (init p x)
    ValueBound (2^12-1) s ∧ 0 ≤ s.B ∧ s.B < 2^12 ∧
      0 ≤ s.D ∧ s.D < 2^12 := by
  dsimp only
  have h := unsigned_walk_envelope hp hpodd (M := (2^12-1 : Int))
    (by omega) hx0 (by omega) k
  rcases h with ⟨hv, _, ⟨hB, hD⟩⟩
  rcases hB with ⟨hB0, hBp⟩
  rcases hD with ⟨hD0, hDp⟩
  exact ⟨hv, hB0, by omega, hD0, by omega⟩

/-! ## A three-way collision: no tag-free local inverse -/

def collisionPost : State := ⟨1, 1, 1, 1, 1, 1⟩
def collisionEven : State := ⟨-1, 1, 2, 1, 2, 0⟩
def collisionSwap : State := ⟨1, -1, 1, 4, 1, 0⟩
def collisionAdd : State := ⟨-1, 1, 1, 1, 1, 0⟩

theorem collision_even : step 5 collisionEven = collisionPost := by decide
theorem collision_swap : step 5 collisionSwap = collisionPost := by decide
theorem collision_add : step 5 collisionAdd = collisionPost := by decide

theorem collision_branches :
    branch collisionEven = .even ∧ branch collisionSwap = .swap ∧
      branch collisionAdd = .add := by decide

theorem collision_valid :
    Odd collisionEven.f ∧ Odd collisionSwap.f ∧ Odd collisionAdd.f ∧
    CoeffCanonical 5 collisionEven ∧ CoeffCanonical 5 collisionSwap ∧
    CoeffCanonical 5 collisionAdd := by
  norm_num [collisionEven, collisionSwap, collisionAdd, CoeffCanonical, Canonical]

theorem collision_pairwise_distinct :
    collisionEven ≠ collisionSwap ∧ collisionEven ≠ collisionAdd ∧
      collisionSwap ≠ collisionAdd := by decide

/-- There is no deterministic inverse from the post-state alone, even when
restricted to odd `f` and canonical modular cofactors. -/
theorem no_tag_free_local_inverse :
    ¬ ∃ undo : State → State,
      ∀ s, Odd s.f → CoeffCanonical 5 s → undo (step 5 s) = s := by
  rintro ⟨undo, hundo⟩
  have he := hundo collisionEven collision_valid.1 collision_valid.2.2.2.1
  have hs := hundo collisionSwap collision_valid.2.1 collision_valid.2.2.2.2.1
  rw [collision_even] at he
  rw [collision_swap] at hs
  have : collisionEven = collisionSwap := he.symm.trans hs
  exact collision_pairwise_distinct.1 this

/-- Any tag type supporting these three inverse cases must assign three
pairwise different tag values.  Thus a binary local tag needs two bits. -/
theorem three_distinct_tags_necessary {Tag : Type} (tag : State → Tag)
    (undo : Tag → State → State)
    (he : undo (tag collisionEven) collisionPost = collisionEven)
    (hs : undo (tag collisionSwap) collisionPost = collisionSwap)
    (ha : undo (tag collisionAdd) collisionPost = collisionAdd) :
    tag collisionEven ≠ tag collisionSwap ∧
      tag collisionEven ≠ tag collisionAdd ∧
      tag collisionSwap ≠ tag collisionAdd := by
  constructor
  · intro h
    rw [h] at he
    exact collision_pairwise_distinct.1 (he.symm.trans hs)
  constructor
  · intro h
    rw [h] at he
    exact collision_pairwise_distinct.2.1 (he.symm.trans ha)
  · intro h
    rw [h] at hs
    exact collision_pairwise_distinct.2.2 (hs.symm.trans ha)

/-! The resource formulas below are arithmetic screens for the conservative
literal skeleton inherited from Brief 26, with the now-proved fixed
coefficient width.  They are not the count of a constructed `Straight`. -/

def fixedCellCCX (valueWidth coeffWidth deltaWidth : Nat) : Nat :=
  9 * valueWidth + 8 * coeffWidth + 4 * deltaWidth - 13

theorem fixedCellCCX_256 : fixedCellCCX 257 256 12 = 4396 := by decide

end ShorECDLP.DivstepTight
