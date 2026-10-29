import ShorECDLP.Submission.Entrant.Streaming.Dirty.DirtyMCX
import ShorECDLP.Submission.«2607_13816».Challenge.Interval
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement

namespace ShorECDLP.FlagCorrection

open ShorECDLP Classical Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Compact

def firstHalf : List Wire := List.range' 263 256 ++ [580]
def halfScratch : List Wire := List.range' 4 255
def halfFlag : Wire := 259

def secondControl (i : Nat) : Wire :=
  if i < 255 then 581 + i else if i = 255 then 838 else halfFlag

def dirtyDonor (i : Nat) : Wire := 263 + i

def secondHalf : List Wire := List.ofFn (fun i : Fin 256 => secondControl i)

def firstAcc (i : Fin 257) : Wire :=
  accumulatorPort ⟨i.val, by omega⟩

def secondAcc (i : Fin 256) : Wire :=
  accumulatorPort ⟨257 + i.val, by omega⟩

theorem firstHalf_acc : firstHalf = List.ofFn firstAcc := by
  decide +kernel

theorem secondHalf_acc : secondHalf = List.ofFn secondAcc := by
  decide +kernel

def AccZero (st : BasisState) : Prop := ∀ i, st (accumulatorPort i) = false

def accZero (st : BasisState) : Bool :=
  registerMatches firstHalf 0 st && registerMatches secondHalf 0 st

theorem registerMatchesFrom_zero_iff (wires : List Wire) (bit : Nat) (st : BasisState) :
    registerMatchesFrom wires 0 bit st = true ↔ ∀ w ∈ wires, st w = false := by
  induction wires generalizing bit with
  | nil => simp [registerMatchesFrom]
  | cons w ws ih =>
      simp only [registerMatchesFrom, Bool.and_eq_true, decide_eq_true_eq,
        Nat.zero_testBit, List.mem_cons]
      constructor
      · rintro ⟨hw, ht⟩ v (rfl | hv)
        · exact hw
        · exact ((ih (bit + 1)).mp ht) v hv
      · intro h
        exact ⟨h w (by simp), (ih (bit + 1)).mpr (fun v hv => h v (by simp [hv]))⟩

theorem registerMatches_zero_iff (wires : List Wire) (st : BasisState) :
    registerMatches wires 0 st = true ↔ ∀ w ∈ wires, st w = false :=
  registerMatchesFrom_zero_iff wires 0 st

theorem splitPredicate_eq_decide (st : BasisState) :
    (registerMatches firstHalf 0 st && registerMatches secondHalf 0 st) =
      accZero st := rfl

theorem accZero_eq_true_iff (st : BasisState) : accZero st = true ↔ AccZero st := by
  simp only [accZero, Bool.and_eq_true, registerMatches_zero_iff]
  rw [firstHalf_acc, secondHalf_acc]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    by_cases hi : i.val < 257
    · exact h₁ (firstAcc ⟨i.val, hi⟩) (List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, by
        simp [firstAcc]⟩)
    · let j : Fin 256 := ⟨i.val - 257, by omega⟩
      have he : secondAcc j = accumulatorPort i := by
        unfold secondAcc j
        apply congrArg accumulatorPort
        apply Fin.ext
        change 257 + (i.val - 257) = i.val
        omega
      rw [← he]
      exact h₂ _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h
    constructor
    · intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact h ⟨i.val, by omega⟩
    · intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact h ⟨257 + i.val, by omega⟩

theorem firstHalf_layout : EqConstLayout firstHalf halfFlag halfScratch := by
  constructor
  · simp [firstHalf, halfScratch]
  · simp only [McxVChainLayout, firstHalf, halfFlag, halfScratch]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨List.nodup_range', by simp, ?_⟩
      intro a ha b hb h
      simp only [List.mem_range'] at ha
      simp only [List.mem_singleton] at hb
      subst b
      dsimp only [Wire] at *
      omega
    · exact List.nodup_cons.mpr ⟨by simp, List.nodup_range'⟩
    · intro a ha b hb h
      simp only [List.mem_append, List.mem_cons,
        List.mem_range', List.not_mem_nil, or_false] at ha hb
      dsimp only [Wire] at *
      rcases ha with ha | rfl <;> rcases hb with rfl | hb <;> omega

theorem secondControl_injective :
    ∀ i < 257, ∀ j < 257, secondControl i = secondControl j → i = j := by
  intro i hi j hj h
  unfold secondControl halfFlag at h
  dsimp only [Wire] at h
  split_ifs at h <;> omega

theorem dirtyDonor_injective :
    ∀ i ≤ 254, ∀ j ≤ 254, dirtyDonor i = dirtyDonor j → i = j := by
  intro i hi j hj h
  unfold dirtyDonor at h
  dsimp only [Wire] at h
  omega

theorem secondHalf_nodup : secondHalf.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Fin.ext (secondControl_injective i (by omega) j (by omega) h)

theorem halfFlag_not_second : halfFlag ∉ secondHalf := by
  intro h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  unfold secondControl halfFlag at hi
  dsimp only [Wire] at hi
  split_ifs at hi <;> omega

theorem flag_not_second (flag : Wire) (hf : flag < 4) : flag ∉ secondHalf := by
  intro h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  unfold secondControl halfFlag at hi
  dsimp only [Wire] at *
  split_ifs at hi <;> omega

theorem controls_donors_apart :
    ∀ i < 257, ∀ j ≤ 254, secondControl i ≠ dirtyDonor j := by
  intro i hi j hj h
  unfold secondControl dirtyDonor halfFlag at h
  dsimp only [Wire] at h
  split_ifs at h <;> omega

theorem controls_flag_apart (flag : Wire) (hf : flag < 4) :
    ∀ i < 257, secondControl i ≠ flag := by
  intro i hi h
  unfold secondControl halfFlag at h
  dsimp only [Wire] at *
  split_ifs at h <;> omega

theorem donors_flag_apart (flag : Wire) (hf : flag < 4) :
    ∀ i ≤ 254, dirtyDonor i ≠ flag := by
  intro i hi h
  unfold dirtyDonor at h
  dsimp only [Wire] at *
  omega

def splitZeroTest (flag : Wire) : Circuit :=
  let half := computeEqConst firstHalf 0 halfFlag halfScratch
  let mask := zeroMask secondHalf 0
  (((half ++ mask) ++ dirtyMCX secondControl dirtyDonor flag 254) ++ mask) ++ half

theorem splitZeroTest_HPFree (flag : Wire) : HPFree (splitZeroTest flag) := by
  unfold splitZeroTest
  simp only [Classical.hpFree_append]
  exact ⟨⟨⟨⟨computeEqConst_HPFree _ _ _ _, zeroMask_HPFree _ _⟩,
    dirtyMCX_HPFree _ _ _ _⟩, zeroMask_HPFree _ _⟩, computeEqConst_HPFree _ _ _ _⟩

theorem halfFlag_not_first : halfFlag ∉ firstHalf := by
  simp only [halfFlag, firstHalf, List.mem_append, List.mem_range',
    List.mem_singleton, not_or]
  dsimp only [Wire]
  omega

theorem flag_not_first (flag : Wire) (hf : flag < 4) : flag ∉ firstHalf := by
  simp only [firstHalf, List.mem_append, List.mem_range', List.mem_singleton]
  dsimp only [Wire] at *
  omega

theorem halfFlag_ne_flag (flag : Wire) (hf : flag < 4) : halfFlag ≠ flag := by
  unfold halfFlag
  dsimp only [Wire] at *
  omega

theorem splitZeroTest_run (flag : Wire) (hf : flag < 4) (st : BasisState)
    (hc : Clean halfScratch st) (hz : st halfFlag = false) :
    Classical.run (splitZeroTest flag) st =
      st[flag ↦ xor (st flag)
        (registerMatches firstHalf 0 st && registerMatches secondHalf 0 st)] := by
  let m := registerMatches firstHalf 0 st
  let s := st[halfFlag ↦ xor (st halfFlag) m]
  have hfirst : Classical.run (computeEqConst firstHalf 0 halfFlag halfScratch) st = s := by
    simpa only [s, m] using run_computeEqConst firstHalf 0 halfFlag halfScratch st
      firstHalf_layout hc
  let mask := zeroMask secondHalf 0
  let u := Classical.run mask s
  have hmaskHalf : u halfFlag = m := by
    dsimp only [u]
    rw [(zeroMask_usesOnly secondHalf 0).preservesOutside s halfFlag_not_second]
    dsimp only [s]
    rw [upd_same, hz]
    cases m <;> rfl
  have hsecondMatchS : registerMatches secondHalf 0 s = registerMatches secondHalf 0 st := by
    change registerMatchesFrom secondHalf 0 0 s = _
    dsimp only [s]
    exact registerMatchesFrom_upd_not_mem secondHalf 0 0 st halfFlag _ halfFlag_not_second
  have hcontrols : controlsAnd secondControl s 257 =
      (controlsAnd secondControl st 256 && m) := by
    rw [show 257 = 256 + 1 by omega, controlsAnd_succ]
    have hp : controlsAnd secondControl s 256 = controlsAnd secondControl st 256 :=
      controlsAnd_congr secondControl s st 256 (by
        intro i hi
        dsimp only [s]
        rw [upd_other]
        unfold secondControl halfFlag
        dsimp only [Wire] at *
        split_ifs <;> omega)
    rw [hp]
    have he : secondControl 256 = halfFlag := by simp [secondControl]
    rw [he]
    dsimp only [s]
    rw [upd_same, hz]
    cases m <;> rfl
  have hmaskedControls : controlsAnd secondControl u 257 =
      (registerMatches secondHalf 0 st && m) := by
    rw [show 257 = 256 + 1 by omega, controlsAnd_succ]
    have he : secondControl 256 = halfFlag := by simp [secondControl]
    rw [he, hmaskHalf]
    rw [controlsAnd_wireAnd]
    rw [show List.ofFn (fun i : Fin 256 => secondControl i.val) = secondHalf by rfl]
    have hm := wireAnd_run_zeroMask secondHalf 0 s secondHalf_nodup
    change wireAnd secondHalf u = registerMatches secondHalf 0 s at hm
    rw [hm, hsecondMatchS]
  have hdirty := dirtyMCX_run secondControl dirtyDonor flag 254
    dirtyDonor_injective controls_donors_apart
    (controls_flag_apart flag hf) (donors_flag_apart flag hf) u
  have hcleanS : Clean halfScratch s := by
    intro w hw
    dsimp only [s]
    rw [upd_other]
    · exact hc w hw
    · intro he
      subst w
      simp [halfScratch, halfFlag] at hw
  have huFlag : u flag = s flag :=
    (zeroMask_usesOnly secondHalf 0).preservesOutside s (flag_not_second flag hf)
  let v := xor (s flag) (controlsAnd secondControl u 257)
  let t := s[flag ↦ v]
  let q := u[flag ↦ v]
  have hdirty' : Classical.run (dirtyMCX secondControl dirtyDonor flag 254) u = q := by
    simpa only [q, v, huFlag] using hdirty
  have hmaskBack : Classical.run mask q = t := by
    dsimp only [q, t]
    rw [(zeroMask_usesOnly secondHalf 0).run_upd_outside flag v u
      (flag_not_second flag hf)]
    dsimp only [u, mask]
    rw [run_zeroMask_twice secondHalf 0 s secondHalf_nodup]
  have hcleanT : Clean halfScratch t := by
    intro w hw
    dsimp only [t]
    rw [upd_other]
    · exact hcleanS w hw
    · intro he
      subst w
      dsimp only [Wire] at *
      simp only [halfScratch, List.mem_range'] at hw
      omega
  have hmatchT : registerMatches firstHalf 0 t = m := by
    change registerMatchesFrom firstHalf 0 0 t = m
    dsimp only [t]
    rw [registerMatchesFrom_upd_not_mem firstHalf 0 0 _ flag _ (flag_not_first flag hf)]
    dsimp only [s, m]
    exact registerMatchesFrom_upd_not_mem firstHalf 0 0 _ halfFlag _ halfFlag_not_first
  have hsecond := run_computeEqConst firstHalf 0 halfFlag halfScratch t
    firstHalf_layout hcleanT
  simp only [splitZeroTest, Classical.run_append, hfirst]
  change Classical.run (computeEqConst firstHalf 0 halfFlag halfScratch)
    (Classical.run mask (Classical.run (dirtyMCX secondControl dirtyDonor flag 254) u)) = _
  rw [hdirty', hmaskBack]
  rw [hsecond, hmatchT]
  funext w
  by_cases hwf : w = flag
  · subst w
    rw [upd_other _ _ _ (halfFlag_ne_flag flag hf).symm, upd_same]
    dsimp only [t]
    rw [upd_same]
    dsimp only [v, s]
    rw [upd_other _ _ _ (halfFlag_ne_flag flag hf).symm]
    rw [hmaskedControls]
    change xor (st flag) (registerMatches secondHalf 0 st && m) =
      xor (st flag) (m && registerMatches secondHalf 0 st)
    cases m <;> cases st flag <;> cases registerMatches secondHalf 0 st <;> rfl
  · rw [upd_other _ _ _ hwf]
    by_cases hwh : w = halfFlag
    · subst w
      change (t halfFlag ^^ m) = st halfFlag
      have htHalf : t halfFlag = m := by
        change s[flag ↦ v] halfFlag = m
        rw [upd_other _ _ _ (halfFlag_ne_flag flag hf)]
        change st[halfFlag ↦ xor (st halfFlag) m] halfFlag = m
        rw [upd_same, hz]
        cases m <;> rfl
      rw [htHalf, hz]
      cases m <;> rfl
    · rw [upd_other _ _ _ hwh]
      dsimp only [t, s]
      rw [upd_other _ _ _ hwf, upd_other _ _ _ hwh]

end ShorECDLP.FlagCorrection

