import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Kernel-checkable consequences for half-delta divsteps

This file deliberately repeats the small arithmetic model from
`workspace/DivstepMath.lean`, so it can be checked directly against the bench
without installing lab scratch as a Lake package.  The selected recurrence is
hddivsteps: `delta2 = 2 * delta`, initially `1` (that is, `delta = 1/2`).
-/

namespace ShorECDLP.DivstepBound

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 800

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
@[simp] theorem walk_succ (k : Nat) (s : State) : walk (k + 1) s = walk k (step s) := rfl

theorem step_of_g_zero {s : State} (h : s.g = 0) : step s = s := by
  simp [step, h]

theorem walk_of_g_zero {s : State} (h : s.g = 0) (k : Nat) : walk k s = s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [walk_succ, step_of_g_zero h]
      exact ih h

theorem start_g_ne_zero_of_walk_g_ne_zero {s : State} {k : Nat}
    (h : (walk k s).g ≠ 0) : s.g ≠ 0 := by
  intro hs
  rw [walk_of_g_zero hs k] at h
  exact h hs

def SameCommonDivisors (f g f' g' : Int) : Prop :=
  ∀ z : Int, (z ∣ f ∧ z ∣ g) ↔ (z ∣ f' ∧ z ∣ g')

theorem sameCommonDivisors_refl (f g : Int) : SameCommonDivisors f g f g := by
  intro z
  rfl

theorem sameCommonDivisors_trans {f g f' g' f'' g'' : Int}
    (h₁ : SameCommonDivisors f g f' g')
    (h₂ : SameCommonDivisors f' g' f'' g'') :
    SameCommonDivisors f g f'' g'' := by
  intro z
  exact (h₁ z).trans (h₂ z)

theorem odd_of_dvd_odd {d f : Int} (hf : Odd f) (hd : d ∣ f) : Odd d := by
  obtain ⟨k, rfl⟩ := hd
  exact Int.Odd.of_mul_left hf

theorem odd_isCoprime_two {d : Int} (hd : Odd d) : IsCoprime d (2 : Int) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨k, rfl⟩ := hd
  calc
    Int.gcd (2 * k + 1) 2 = Int.gcd (1 + k * 2) 2 := by ring_nf
    _ = Int.gcd 1 2 := Int.gcd_add_mul_right_left 2 1 k
    _ = 1 := by norm_num [Int.gcd_def]

theorem dvd_half_of_dvd_even {d g : Int} (hdodd : Odd d) (hgeven : Even g)
    (hdg : d ∣ g) : d ∣ g / 2 := by
  have htwice : 2 * (g / 2) = g := Int.two_mul_ediv_two_of_even hgeven
  apply (odd_isCoprime_two hdodd).dvd_of_dvd_mul_right
  rw [mul_comm, htwice]
  exact hdg

theorem sameCommonDivisors_even_half {f g : Int} (hf : Odd f) (hg : Even g) :
    SameCommonDivisors f g f (g / 2) := by
  intro z
  constructor
  · rintro ⟨hzf, hzg⟩
    exact ⟨hzf, dvd_half_of_dvd_even (odd_of_dvd_odd hf hzf) hg hzg⟩
  · rintro ⟨hzf, hzh⟩
    refine ⟨hzf, ?_⟩
    have htwice : 2 * (g / 2) = g := Int.two_mul_ediv_two_of_even hg
    rw [← htwice]
    exact dvd_mul_of_dvd_right hzh 2

theorem sameCommonDivisors_swap_sub_half {f g : Int} (hf : Odd f) (hg : Odd g) :
    SameCommonDivisors f g g ((g - f) / 2) := by
  have hdiff : Even (g - f) := hg.sub_odd hf
  intro z
  constructor
  · rintro ⟨hzf, hzg⟩
    refine ⟨hzg, dvd_half_of_dvd_even (odd_of_dvd_odd hf hzf) hdiff ?_⟩
    exact dvd_sub hzg hzf
  · rintro ⟨hzg, hzh⟩
    have htwo : z ∣ g - f := by
      have htwice : 2 * ((g - f) / 2) = g - f := Int.two_mul_ediv_two_of_even hdiff
      rw [← htwice]
      exact dvd_mul_of_dvd_right hzh 2
    exact ⟨by simpa only [sub_sub_cancel] using dvd_sub hzg htwo, hzg⟩

theorem sameCommonDivisors_add_half {f g : Int} (hf : Odd f) (hg : Odd g) :
    SameCommonDivisors f g f ((g + f) / 2) := by
  have hsum : Even (g + f) := hg.add_odd hf
  intro z
  constructor
  · rintro ⟨hzf, hzg⟩
    exact ⟨hzf, dvd_half_of_dvd_even (odd_of_dvd_odd hf hzf) hsum (dvd_add hzg hzf)⟩
  · rintro ⟨hzf, hzh⟩
    have htwo : z ∣ g + f := by
      have htwice : 2 * ((g + f) / 2) = g + f := Int.two_mul_ediv_two_of_even hsum
      rw [← htwice]
      exact dvd_mul_of_dvd_right hzh 2
    exact ⟨hzf, by simpa only [add_sub_cancel_right] using dvd_sub htwo hzf⟩

theorem sameCommonDivisors_gcd {f g f' g' : Int}
    (h : SameCommonDivisors f g f' g') : Int.gcd f g = Int.gcd f' g' := by
  apply Nat.dvd_antisymm
  · rw [← Int.natCast_dvd_natCast]
    exact Int.dvd_coe_gcd ((h _).mp ⟨Int.gcd_dvd_left f g, Int.gcd_dvd_right f g⟩).1
      ((h _).mp ⟨Int.gcd_dvd_left f g, Int.gcd_dvd_right f g⟩).2
  · rw [← Int.natCast_dvd_natCast]
    exact Int.dvd_coe_gcd ((h _).mpr ⟨Int.gcd_dvd_left f' g', Int.gcd_dvd_right f' g'⟩).1
      ((h _).mpr ⟨Int.gcd_dvd_left f' g', Int.gcd_dvd_right f' g'⟩).2

theorem step_f_odd {s : State} (hf : Odd s.f) : Odd (step s).f := by
  unfold step
  split
  · exact hf
  split
  · exact hf
  split
  · exact Int.not_even_iff_odd.mp ‹¬ Even s.g›
  · exact hf

theorem step_sameCommonDivisors {s : State} (hf : Odd s.f) :
    SameCommonDivisors s.f s.g (step s).f (step s).g := by
  unfold step
  split
  · exact sameCommonDivisors_refl _ _
  split
  · exact sameCommonDivisors_even_half hf ‹Even s.g›
  split
  · exact sameCommonDivisors_swap_sub_half hf (Int.not_even_iff_odd.mp ‹¬ Even s.g›)
  · exact sameCommonDivisors_add_half hf (Int.not_even_iff_odd.mp ‹¬ Even s.g›)

theorem walk_f_odd {s : State} (hf : Odd s.f) (k : Nat) : Odd (walk k s).f := by
  induction k generalizing s with
  | zero => exact hf
  | succ k ih => exact ih (step_f_odd hf)

theorem walk_sameCommonDivisors {s : State} (hf : Odd s.f) (k : Nat) :
    SameCommonDivisors s.f s.g (walk k s).f (walk k s).g := by
  induction k generalizing s with
  | zero => exact sameCommonDivisors_refl _ _
  | succ k ih =>
      exact sameCommonDivisors_trans (step_sameCommonDivisors hf) (ih (step_f_odd hf))

theorem walk_gcd {s : State} (hf : Odd s.f) (k : Nat) :
    Int.gcd (walk k s).f (walk k s).g = Int.gcd s.f s.g := by
  exact (sameCommonDivisors_gcd (walk_sameCommonDivisors hf k)).symm

theorem terminal_f_natAbs_eq_gcd {f0 g0 : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) :
    (walk k (init f0 g0)).f.natAbs = Int.gcd f0 g0 := by
  have h := walk_gcd (s := init f0 g0) hf k
  rw [hg, Int.gcd_zero_right] at h
  exact h

theorem terminal_f_eq_gcd_or_neg {f0 g0 : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) :
    (walk k (init f0 g0)).f = (Int.gcd f0 g0 : Int) ∨
      (walk k (init f0 g0)).f = -(Int.gcd f0 g0 : Int) := by
  have habs := terminal_f_natAbs_eq_gcd hf k hg
  obtain hpos | hneg := Int.natAbs_eq (walk k (init f0 g0)).f
  · left
    simpa [habs] using hpos
  · right
    simpa [habs] using hneg

/-! The scaled transition-matrix invariant, repeated here so the final modular
corollary and the recurrence are checked in one standalone source. -/

def MatrixInvariant (f0 g0 : Int) (s : State) : Prop :=
  (2 : Int) ^ s.ticks * s.f = s.a * f0 + s.b * g0 ∧
  (2 : Int) ^ s.ticks * s.g = s.c * f0 + s.d * g0

@[simp] theorem init_matrixInvariant (f0 g0 : Int) :
    MatrixInvariant f0 g0 (init f0 g0) := by
  simp [MatrixInvariant, init]

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
      have hgodd : Odd s.g := Int.not_even_iff_odd.mp hneven
      have hdiff : Even (s.g - s.f) := hgodd.sub_odd hf
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
      have hgodd : Odd s.g := Int.not_even_iff_odd.mp hneven
      have hsum : Even (s.g + s.f) := hgodd.add_odd hf
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

theorem walk_matrixInvariant {f0 g0 : Int} {s : State}
    (hf : Odd s.f) (hmat : MatrixInvariant f0 g0 s) (k : Nat) :
    MatrixInvariant f0 g0 (walk k s) := by
  induction k generalizing s with
  | zero => exact hmat
  | succ k ih => exact ih (step_f_odd hf) (step_matrixInvariant hf hmat)

theorem init_walk_matrixInvariant {f0 g0 : Int} (hf : Odd f0) (k : Nat) :
    MatrixInvariant f0 g0 (walk k (init f0 g0)) :=
  walk_matrixInvariant hf (init_matrixInvariant f0 g0) k

/-- At a coprime terminal state, `b*f` is the inverse of `g0` up to the
known power-of-two scaling.  Since `f0` is odd, that scaling is a unit modulo
`f0`; multiplying this congruence by its inverse gives the ordinary inverse. -/
theorem terminal_scaled_inverse {f0 g0 : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) (hcop : Int.gcd f0 g0 = 1) :
    let s := walk k (init f0 g0)
    (s.b * s.f) * g0 ≡ (2 : Int) ^ s.ticks [ZMOD f0] := by
  dsimp only
  let s := walk k (init f0 g0)
  have habs : s.f.natAbs = 1 := by
    simpa [s, hcop] using terminal_f_natAbs_eq_gcd hf k hg
  have hsq : s.f * s.f = 1 := by
    have := (Int.natAbs_eq_iff_mul_self_eq (a := s.f) (b := (1 : Int))).mp (by simpa using habs)
    simpa using this
  dsimp [s] at hsq
  have hmat := (init_walk_matrixInvariant (f0 := f0) (g0 := g0) hf k).1
  rw [Int.modEq_iff_dvd]
  refine ⟨s.a * s.f, ?_⟩
  dsimp [s] at hmat ⊢
  calc
    (2 : Int) ^ (walk k (init f0 g0)).ticks -
        ((walk k (init f0 g0)).b * (walk k (init f0 g0)).f) * g0 =
        (2 : Int) ^ (walk k (init f0 g0)).ticks *
            ((walk k (init f0 g0)).f * (walk k (init f0 g0)).f) -
          (walk k (init f0 g0)).b * g0 * (walk k (init f0 g0)).f := by
            rw [hsq]
            ring
    _ = ((2 : Int) ^ (walk k (init f0 g0)).ticks * (walk k (init f0 g0)).f -
          (walk k (init f0 g0)).b * g0) * (walk k (init f0 g0)).f := by ring
    _ = (walk k (init f0 g0)).a * f0 * (walk k (init f0 g0)).f := by rw [hmat]; ring
    _ = f0 * ((walk k (init f0 g0)).a * (walk k (init f0 g0)).f) := by ring

/-- Any modular inverse of the public power-of-two scale turns the matrix row
into an ordinary inverse of `g0`. -/
theorem terminal_inverse_of_unscale {f0 g0 u : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) (hcop : Int.gcd f0 g0 = 1)
    (hu : u * (2 : Int) ^ (walk k (init f0 g0)).ticks ≡ 1 [ZMOD f0]) :
    (u * ((walk k (init f0 g0)).b * (walk k (init f0 g0)).f)) * g0 ≡ 1 [ZMOD f0] := by
  have hs := terminal_scaled_inverse hf k hg hcop
  simpa [mul_assoc] using (hs.mul_left u).trans hu

theorem exists_power_two_unscale {f0 : Int} (hf : Odd f0) (ticks : Nat) :
    ∃ u : Int, u * (2 : Int) ^ ticks ≡ 1 [ZMOD f0] := by
  have hcop : IsCoprime ((2 : Int) ^ ticks) f0 := (odd_isCoprime_two hf).symm.pow_left
  rcases hcop with ⟨u, v, huv⟩
  refine ⟨u, Int.modEq_iff_dvd.mpr ?_⟩
  refine ⟨v, ?_⟩
  linarith

/-- The terminal matrix data contains an ordinary modular inverse whenever
the inputs are coprime; the existential witness includes unscaling by the
automatically invertible power of two. -/
theorem terminal_inverse_exists {f0 g0 : Int} (hf : Odd f0) (k : Nat)
    (hg : (walk k (init f0 g0)).g = 0) (hcop : Int.gcd f0 g0 = 1) :
    ∃ x : Int, x * g0 ≡ 1 [ZMOD f0] := by
  obtain ⟨u, hu⟩ := exists_power_two_unscale hf (walk k (init f0 g0)).ticks
  exact ⟨u * ((walk k (init f0 g0)).b * (walk k (init f0 g0)).f),
    terminal_inverse_of_unscale hf k hg hcop hu⟩

/-! ## A compact certificate interface for the missing finite hull check

`PotentialCertificate` is deliberately rational and local.  Its contraction
factor `25/32 = 0.78125` is weaker than the published hddivsteps factor
approximately `0.74015`, but is already strong enough to force termination by
742 from the 256-bit triangle if the initial gauge is at most four times its
coordinate bound.  Thus the only remaining finite-computation obligation is
to exhibit such a polyhedral gauge and check `contracts` on its finitely many
faces.
-/

abbrev Potential := Int → Int → Int → ℚ

structure PotentialCertificate (P : Potential) : Prop where
  nonneg : ∀ delta2 f g, 0 ≤ P delta2 f g
  dominatesG : ∀ delta2 f g, (Int.natAbs g : ℚ) ≤ P delta2 f g
  contracts : ∀ s : State, s.g ≠ 0 →
    32 * P (step s).delta2 (step s).f (step s).g ≤
      25 * P s.delta2 s.f s.g

theorem potential_walk_bound {P : Potential} (hP : PotentialCertificate P)
    {s : State} {k : Nat} (hfinal : (walk k s).g ≠ 0) :
    P (walk k s).delta2 (walk k s).f (walk k s).g ≤
      ((25 : ℚ) / 32) ^ k * P s.delta2 s.f s.g := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      have hstepfinal : (walk k (step s)).g ≠ 0 := hfinal
      have hsg : s.g ≠ 0 := start_g_ne_zero_of_walk_g_ne_zero hfinal
      have hrec := ih hstepfinal
      have hcontract := hP.contracts s hsg
      have hnonneg : 0 ≤ ((25 : ℚ) / 32) ^ k := pow_nonneg (by norm_num) _
      have hstep : P (step s).delta2 (step s).f (step s).g ≤
          ((25 : ℚ) / 32) * P s.delta2 s.f s.g := by
        linarith
      rw [pow_succ]
      exact hrec.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hstep hnonneg)

theorem terminates_742_of_potential {P : Potential} (hP : PotentialCertificate P)
    {f0 g0 : Int}
    (hinit : P 1 f0 g0 ≤ (4 : ℚ) * 2 ^ 256) :
    (walk 742 (init f0 g0)).g = 0 := by
  by_contra hfinal
  have hbound := potential_walk_bound hP (s := init f0 g0) (k := 742) hfinal
  have hdom := hP.dominatesG (walk 742 (init f0 g0)).delta2
    (walk 742 (init f0 g0)).f (walk 742 (init f0 g0)).g
  have habs : (1 : ℚ) ≤ Int.natAbs (walk 742 (init f0 g0)).g := by
    exact Nat.cast_le.mpr (Int.natAbs_pos.mpr hfinal)
  have hnonneg : 0 ≤ ((25 : ℚ) / 32) ^ 742 := pow_nonneg (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_left hinit hnonneg
  have hle : (1 : ℚ) ≤ ((25 : ℚ) / 32) ^ 742 * ((4 : ℚ) * 2 ^ 256) :=
    habs.trans (hdom.trans (hbound.trans hscaled))
  have hlt : ((25 : ℚ) / 32) ^ 742 * ((4 : ℚ) * 2 ^ 256) < 1 := by
    norm_num [div_pow]
  linarith

/-- Exact finite-hull obligation left by Brief 25.  A concrete witness should
be a finite rational polyhedral gauge; all universally quantified fields then
reduce to local face/vertex inequalities. -/
def Has256TrianglePotential : Prop :=
  ∃ P : Potential, PotentialCertificate P ∧
    ∀ f g : Int, Odd f → 0 ≤ g → g ≤ f → f < (2 : Int) ^ 256 →
      P 1 f g ≤ (4 : ℚ) * 2 ^ 256

theorem halfDelta_terminates_742_of_certificate (hcert : Has256TrianglePotential) :
    ∀ f0 g0 : Int, Odd f0 → 0 ≤ g0 → g0 ≤ f0 → f0 < (2 : Int) ^ 256 →
      (walk 742 (init f0 g0)).g = 0 := by
  rcases hcert with ⟨P, hP, hinit⟩
  intro f0 g0 hf hg0 hgf hf256
  exact terminates_742_of_potential hP (hinit f0 g0 hf hg0 hgf hf256)

#print axioms terminal_f_natAbs_eq_gcd
#print axioms terminal_inverse_of_unscale
#print axioms terminal_inverse_exists
#print axioms terminates_742_of_potential
#print axioms halfDelta_terminates_742_of_certificate

end ShorECDLP.DivstepBound
