import ShorECDLP.Submission.«2607_13816».Challenge.EndpointTransposition

namespace ShorECDLP.Compact
open ShorECDLP Quantum
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Conjugate the seed toggle through a borrowed V-chain. -/
def dirtySweep (c a : Nat → Wire) : Nat → Circuit
  | 0 => [.CCX (c 0) (c 1) (a 0)]
  | n+1 => [.CCX (c (n+2)) (a n) (a (n+1))] ++ dirtySweep c a n ++
      [.CCX (c (n+2)) (a n) (a (n+1))]

def controlsAnd (c : Nat → Wire) (st : BasisState) (n : Nat) : Bool :=
  ((List.range n).map (fun i => st (c i))).all id

theorem controlsAnd_succ (c : Nat → Wire) (st : BasisState) (n : Nat) :
    controlsAnd c st (n+1) = (controlsAnd c st n && st (c n)) := by
  simp [controlsAnd, List.range_succ, List.all_append]

theorem controlsAnd_two (c : Nat → Wire) (st : BasisState) :
    controlsAnd c st 2 = (st (c 0) && st (c 1)) := by simp [controlsAnd, List.range_succ]

theorem controlsAnd_congr (c : Nat → Wire) (s t : BasisState) (n : Nat)
    (h : ∀ i < n, s (c i) = t (c i)) : controlsAnd c s n = controlsAnd c t n := by
  unfold controlsAnd
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- No cleanliness assumption: every borrowed bit receives the prefix toggle. -/
theorem dirtySweep_run (c a : Nat → Wire) (n : Nat)
    (ha : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j)
    (hca : ∀ i < n+2, ∀ j ≤ n, c i ≠ a j) (st : BasisState) :
    let out := Classical.run (dirtySweep c a n) st
    (∀ i < n+2, out (c i) = st (c i)) ∧
    (∀ i ≤ n, out (a i) = xor (st (a i)) (controlsAnd c st (i+2))) ∧
    (∀ w, (∀ i ≤ n, w ≠ a i) → out w = st w) := by
  induction n generalizing st with
  | zero =>
    change (∀ i < 2, (st[a 0 ↦ xor (st (a 0)) (st (c 0) && st (c 1))]) (c i) = _) ∧ _
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; exact upd_other _ _ _ (hca i hi 0 (by omega))
    · intro i hi; have : i = 0 := by omega
      subst i; simpa only [dirtySweep, Classical.run_cons, Classical.run_nil, Classical.applyGate, controlsAnd_two, Nat.zero_add] using (upd_same st (a 0) (xor (st (a 0)) (st (c 0) && st (c 1))))
    · intro w hw; exact upd_other _ _ _ (hw 0 (by omega))
  | succ n ih =>
    let v := xor (st (a (n+1))) (st (c (n+2)) && st (a n))
    let s := st[a (n+1) ↦ v]
    let t := Classical.run (dirtySweep c a n) s
    have hne (i : Nat) (hi : i ≤ n) : a i ≠ a (n+1) := by
      intro he; have := ha i (by omega) (n+1) (by omega) he; omega
    have hc (i : Nat) (hi : i < n+3) : s (c i) = st (c i) :=
      upd_other _ _ _ (hca i (by omega) (n+1) (by omega))
    have hd (i : Nat) (hi : i ≤ n) : s (a i) = st (a i) := upd_other _ _ _ (hne i hi)
    have ht := ih (fun i hi j hj => ha i (by omega) j (by omega))
      (fun i hi j hj => hca i (by omega) j (by omega)) s
    dsimp only at ht
    change (∀ i < n+2, t (c i) = s (c i)) ∧
      (∀ i ≤ n, t (a i) = xor (s (a i)) (controlsAnd c s (i+2))) ∧
      (∀ w, (∀ i ≤ n, w ≠ a i) → t w = s w) at ht
    have htc : t (c (n+2)) = st (c (n+2)) := by
      rw [ht.2.2 _ (fun i hi => hca _ (by omega) i (by omega)), hc _ (by omega)]
    have htn : t (a n) = xor (st (a n)) (controlsAnd c st (n+2)) := by
      rw [ht.2.1 n (by omega), hd n (by omega),
        controlsAnd_congr c s st (n+2) (fun i hi => hc i (by omega))]
    have hte : t (a (n+1)) = v := by
      rw [ht.2.2 _ (fun i hi => (hne i hi).symm)]
      exact upd_same _ _ _
    simp only [dirtySweep, Classical.run_append, Classical.run_cons, Classical.run_nil]
    let out := t[a (n+1) ↦ xor (t (a (n+1))) (t (c (n+2)) && t (a n))]
    change (∀ i < n+3, out (c i) = st (c i)) ∧
      (∀ i ≤ n+1, out (a i) = xor (st (a i)) (controlsAnd c st (i+2))) ∧
      (∀ w, (∀ i ≤ n+1, w ≠ a i) → out w = st w)
    dsimp only [out]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [upd_other _ _ _ (hca i (by omega) (n+1) (by omega))]
      by_cases hil : i < n+2
      · rw [ht.1 i hil, hc i hi]
      · rw [ht.2.2 _ (fun j hj => hca i (by omega) j (by omega)), hc i hi]
    · intro i hi
      by_cases hil : i ≤ n
      · rw [upd_other _ _ _ (hne i hil), ht.2.1 i hil, hd i hil,
          controlsAnd_congr c s st (i+2) (fun j hj => hc j (by omega))]
      · have : i = n+1 := by omega
        subst i
        rw [upd_same, hte, htc, htn, show n+1+2 = n+2+1 by omega,
          controlsAnd_succ c st (n+2)]
        dsimp only [v]
        cases st (a (n+1)) <;> cases st (c (n+2)) <;> cases st (a n) <;>
          cases controlsAnd c st (n+2) <;> rfl
    · intro w hw
      rw [upd_other _ _ _ (hw (n+1) (by omega)),
        ht.2.2 w (fun i hi => hw i (by omega))]
      exact upd_other _ _ _ (hw (n+1) (by omega))

/-- Barenco dirty-ancilla MCX, k=n+3 controls and n+1 donors. -/
def dirtyMCX (c a : Nat → Wire) (target : Wire) (n : Nat) : Circuit :=
  let half := [.CCX (c (n+2)) (a n) target] ++ dirtySweep c a n
  half ++ half

theorem dirtyMCX_run (c a : Nat → Wire) (target : Wire) (n : Nat)
    (ha : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j)
    (hca : ∀ i < n+3, ∀ j ≤ n, c i ≠ a j)
    (hct : ∀ i < n+3, c i ≠ target)
    (hat : ∀ i ≤ n, a i ≠ target) (st : BasisState) :
    Classical.run (dirtyMCX c a target n) st =
      st[target ↦ xor (st target) (controlsAnd c st (n+3))] := by
  let v := xor (st target) (st (c (n+2)) && st (a n))
  let s := st[target ↦ v]
  let t := Classical.run (dirtySweep c a n) s
  let z := xor (t target) (t (c (n+2)) && t (a n))
  let u := t[target ↦ z]
  have hsC (i : Nat) (hi : i < n+3) : s (c i) = st (c i) :=
    upd_other _ _ _ (hct i hi)
  have hsA (i : Nat) (hi : i ≤ n) : s (a i) = st (a i) :=
    upd_other _ _ _ (hat i hi)
  have ht := dirtySweep_run c a n ha (fun i hi j hj => hca i (by omega) j hj) s
  change (∀ i < n+2, t (c i) = s (c i)) ∧
    (∀ i ≤ n, t (a i) = xor (s (a i)) (controlsAnd c s (i+2))) ∧
    (∀ w, (∀ i ≤ n, w ≠ a i) → t w = s w) at ht
  have htC (i : Nat) (hi : i < n+3) : t (c i) = st (c i) := by
    rw [ht.2.2 _ (fun j hj => hca i hi j hj), hsC i hi]
  have htA (i : Nat) (hi : i ≤ n) :
      t (a i) = xor (st (a i)) (controlsAnd c st (i+2)) := by
    rw [ht.2.1 i hi, hsA i hi,
      controlsAnd_congr c s st (i+2) (fun j hj => hsC j (by omega))]
  have htt : t target = v := by
    rw [ht.2.2 _ (fun j hj => (hat j hj).symm)]
    exact upd_same _ _ _
  have hz : z = xor (st target) (controlsAnd c st (n+3)) := by
    dsimp only [z]
    rw [htt, htC _ (by omega), htA n (by omega),
      show n+3 = n+2+1 by omega, controlsAnd_succ c st (n+2)]
    dsimp only [v]
    cases st target <;> cases st (c (n+2)) <;> cases st (a n) <;>
      cases controlsAnd c st (n+2) <;> rfl
  have hu := dirtySweep_run c a n ha (fun i hi j hj => hca i (by omega) j hj) u
  simp only [dirtyMCX, Classical.run_append, Classical.run_cons, Classical.run_nil]
  change Classical.run (dirtySweep c a n) u = _
  funext w
  by_cases hwt : w = target
  · subst w
    rw [hu.2.2 _ (fun j hj => (hat j hj).symm)]
    exact (upd_same t target z).trans (hz.trans (upd_same _ _ _).symm)
  · rw [upd_other _ _ _ hwt]
    by_cases hwa : ∃ i ≤ n, w = a i
    · obtain ⟨i,hi,rfl⟩ := hwa
      rw [hu.2.1 i hi]
      rw [show u (a i) = t (a i) from upd_other _ _ _ (hat i hi), htA i hi,
        controlsAnd_congr c u st (i+2) (by
          intro j hj
          exact (upd_other t target z (hct j (by omega))).trans (htC j (by omega)))]
      cases st (a i) <;> cases controlsAnd c st (i+2) <;> rfl
    · have hwA : ∀ i ≤ n, w ≠ a i := by
        intro i hi he; exact hwa ⟨i,hi,he⟩
      rw [hu.2.2 w hwA]
      change u w = st w
      rw [show u w = t w from upd_other _ _ _ hwt, ht.2.2 w hwA]
      exact upd_other _ _ _ hwt

theorem dirtySweep_HPFree (c a : Nat → Wire) (n : Nat) :
    Classical.HPFree (dirtySweep c a n) := by
  induction n with
  | zero => simp [dirtySweep]
  | succ n ih => simp [dirtySweep, ih]

theorem dirtyMCX_HPFree (c a : Nat → Wire) (target : Wire) (n : Nat) :
    Classical.HPFree (dirtyMCX c a target n) := by
  simp [dirtyMCX, dirtySweep_HPFree]

/-- The coherent action has scalar exactly one, including dirty donors. -/
theorem dirtyMCX_ket (c a : Nat → Wire) (target : Wire) (n : Nat)
    (ha : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j)
    (hca : ∀ i < n+3, ∀ j ≤ n, c i ≠ a j)
    (hct : ∀ i < n+3, c i ≠ target)
    (hat : ∀ i ≤ n, a i ≠ target) (st : BasisState) :
    Quantum.run (dirtyMCX c a target n) (Quantum.ket st) =
      Quantum.ket (st[target ↦ xor (st target) (controlsAnd c st (n+3))]) := by
  rw [Quantum.run_ket_agrees_classical _ _ (dirtyMCX_HPFree _ _ _ _),
    dirtyMCX_run c a target n ha hca hct hat st]

theorem dirtySweep_length (c a : Nat → Wire) (n : Nat) :
    (dirtySweep c a n).length = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dirtySweep, List.length_append, List.length_singleton, ih]; omega

theorem dirtyMCX_length (c a : Nat → Wire) (target : Wire) (n : Nat) :
    (dirtyMCX c a target n).length = 4*(n+1) := by
  simp only [dirtyMCX, List.length_append, List.length_singleton, dirtySweep_length]
  omega

theorem dirtySweep_tCount (c a : Nat → Wire) (n : Nat) :
    ShorECDLP.tCount (dirtySweep c a n) = 7*(2*n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dirtySweep, tCount_append, ih]
    simp [tCount, tCost]
    omega

theorem dirtyMCX_tCount (c a : Nat → Wire) (target : Wire) (n : Nat) :
    ShorECDLP.tCount (dirtyMCX c a target n) = 28*(n+1) := by
  simp only [dirtyMCX, tCount_append, dirtySweep_tCount]
  simp [tCount, tCost]
  omega

theorem dirtySweep_wellFormed (c a : Nat → Wire) (n : Nat)
    (hc : c 0 ≠ c 1)
    (ha : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j)
    (hca : ∀ i < n+2, ∀ j ≤ n, c i ≠ a j) :
    CircuitWellFormed (dirtySweep c a n) := by
  induction n with
  | zero =>
    simp only [dirtySweep, circuitWellFormed_cons, circuitWellFormed_nil, and_true,
      Gate.WellFormed]
    exact ⟨hc, hca 0 (by omega) 0 (by omega), hca 1 (by omega) 0 (by omega)⟩
  | succ n ih =>
    have hg : (Gate.CCX (c (n+2)) (a n) (a (n+1))).WellFormed := by
      refine ⟨hca _ (by omega) _ (by omega), hca _ (by omega) _ (by omega), ?_⟩
      intro he; have := ha n (by omega) (n+1) (by omega) he; omega
    have hi := ih (fun i hi j hj => ha i (by omega) j (by omega))
      (fun i hi j hj => hca i (by omega) j (by omega))
    simpa only [dirtySweep, circuitWellFormed_append, circuitWellFormed_cons,
      circuitWellFormed_nil, and_true] using And.intro (And.intro hg hi) hg

theorem dirtyMCX_wellFormed (c a : Nat → Wire) (target : Wire) (n : Nat)
    (hc : c 0 ≠ c 1)
    (ha : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j)
    (hca : ∀ i < n+3, ∀ j ≤ n, c i ≠ a j)
    (hct : ∀ i < n+3, c i ≠ target)
    (hat : ∀ i ≤ n, a i ≠ target) :
    CircuitWellFormed (dirtyMCX c a target n) := by
  have hs := dirtySweep_wellFormed c a n hc ha
    (fun i hi j hj => hca i (by omega) j hj)
  have hg : (Gate.CCX (c (n+2)) (a n) target).WellFormed :=
    ⟨hca _ (by omega) _ (by omega), hct _ (by omega), hat _ (by omega)⟩
  simp only [dirtyMCX, circuitWellFormed_append, circuitWellFormed_cons,
    circuitWellFormed_nil, and_true]
  exact ⟨⟨hg, hs⟩, hg, hs⟩

theorem dirtySweep_support (c a : Nat → Wire) (n : Nat) (support : List Wire)
    (hc : ∀ i < n+2, c i ∈ support) (ha : ∀ i ≤ n, a i ∈ support) :
    circuitWires (dirtySweep c a n) ⊆ support := by
  induction n with
  | zero =>
    simpa [dirtySweep, circuitWires, gateWires] using
      And.intro (hc 0 (by omega)) (And.intro (hc 1 (by omega)) (ha 0 (by omega)))
  | succ n ih =>
    have hg : circuitWires [.CCX (c (n+2)) (a n) (a (n+1))] ⊆ support := by
      simpa [circuitWires, gateWires] using
        And.intro (hc (n+2) (by omega)) (And.intro (ha n (by omega)) (ha (n+1) (by omega)))
    simpa only [dirtySweep, circuitWires, List.flatMap_append, List.append_subset] using
      And.intro (And.intro hg (ih (fun i hi => hc i (by omega))
        (fun i hi => ha i (by omega)))) hg

theorem dirtyMCX_support (c a : Nat → Wire) (target : Wire) (n : Nat) (support : List Wire)
    (hc : ∀ i < n+3, c i ∈ support) (ha : ∀ i ≤ n, a i ∈ support)
    (ht : target ∈ support) : circuitWires (dirtyMCX c a target n) ⊆ support := by
  have hg : circuitWires [.CCX (c (n+2)) (a n) target] ⊆ support := by
    simpa [circuitWires, gateWires] using
      And.intro (hc (n+2) (by omega)) (And.intro (ha n (by omega)) ht)
  have hs := dirtySweep_support c a n support (fun i hi => hc i (by omega)) ha
  simpa only [dirtyMCX, circuitWires, List.flatMap_append, List.append_subset] using
    And.intro (And.intro hg hs) (And.intro hg hs)

theorem wireAnd_append_singleton (ws : List Wire) (w : Wire) (st : BasisState) :
    ShorECDLP.Paper2607_13816.wireAnd (ws ++ [w]) st =
      (ShorECDLP.Paper2607_13816.wireAnd ws st && st w) := by
  induction ws with
  | nil => simp [ShorECDLP.Paper2607_13816.wireAnd]
  | cons v vs ih =>
    simp only [List.cons_append, ShorECDLP.Paper2607_13816.wireAnd, ih]
    cases st v <;> rfl

theorem controlsAnd_wireAnd (c : Nat → Wire) (st : BasisState) (n : Nat) :
    controlsAnd c st n = ShorECDLP.Paper2607_13816.wireAnd
      (List.ofFn (fun i : Fin n => c i.val)) st := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [controlsAnd_succ, List.ofFn_succ', List.concat_eq_append,
      wireAnd_append_singleton, ih]
    congr 1

/-- Equality of two 513-bit words using an arbitrary, restored donor word. -/
def dirtyRegisterEqualCircuit (a target donor : Fin 513 → Wire) (flag : Wire) : Circuit :=
  let cells := ShorECDLP.Paper2607_13816.ChallengeMigration.equalityCells a target
  let mask := ShorECDLP.Paper2607_13816.zeroMask (List.ofFn target) 0
  let controls : Nat → Wire := fun i => target ⟨i % 513, Nat.mod_lt i (by decide : 0 < 513)⟩
  let donors : Nat → Wire := fun i => donor ⟨i % 511, by
    have := Nat.mod_lt i (by decide : 0 < 511)
    omega⟩
  ShorECDLP.Paper2607_13816.ChallengeMigration.xorWordCircuit cells ++ mask ++
    dirtyMCX controls donors flag 510 ++ mask ++
    ShorECDLP.Paper2607_13816.ChallengeMigration.xorWordCircuit cells

set_option maxRecDepth 10000 in
theorem dirtyRegisterEqualCircuit_run (a target donor : Fin 513 → Wire) (flag : Wire)
    (ht : Function.Injective target) (hd : Function.Injective donor)
    (hat : ∀ i j, a i ≠ target j) (hdt : ∀ i j, donor i ≠ target j)
    (hf : ∀ i, flag ≠ a i ∧ flag ≠ target i ∧ flag ≠ donor i)
    (st : BasisState) :
    Classical.run (dirtyRegisterEqualCircuit a target donor flag) st =
      st[flag ↦ xor (st flag) (decide (st ∘ target = st ∘ a))] := by
  let cells := equalityCells a target
  let register := List.ofFn target
  let mask := zeroMask register 0
  let controls : Nat → Wire := fun i => target ⟨i % 513, Nat.mod_lt i (by decide : 0 < 513)⟩
  let donors : Nat → Wire := fun i => donor ⟨i % 511, by
    have := Nat.mod_lt i (by decide : 0 < 511)
    omega⟩
  let xored := Classical.run (xorWordCircuit cells) st
  let masked := Classical.run mask xored
  have hsep : xorSeparated cells := by
    intro c hc d hd'
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd'
    exact hat i j
  have hmap : cells.map Prod.snd = register := by
    simp only [cells, register, equalityCells, List.map_ofFn]
    rfl
  have hnd : register.Nodup := List.nodup_ofFn.mpr ht
  have hflagX : flag ∉ xorWordSupport cells := by
    apply equalityCells_outside
    intro i
    exact ⟨(hf i).1, (hf i).2.1⟩
  have hflagR : flag ∉ register := by
    intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact (hf i).2.1 hi.symm
  have hcontrols (i : Nat) (hi : i < 513) : controls i = target ⟨i, hi⟩ := by
    simp only [controls, Nat.mod_eq_of_lt hi]
  have hdonors (i : Nat) (hi : i ≤ 510) : donors i = donor ⟨i, by omega⟩ := by
    simp only [donors, Nat.mod_eq_of_lt (by omega : i < 511)]
  have hmcx := dirtyMCX_run controls donors flag 510
    (fun i hi j hj he => by
      rw [hdonors i hi, hdonors j hj] at he
      exact congrArg Fin.val (hd he))
    (fun i hi j hj => by
      rw [hcontrols i (by omega), hdonors j hj]
      exact (hdt _ _).symm)
    (fun i hi => by
      rw [hcontrols i hi]
      exact ((hf _).2.1).symm)
    (fun i hi => by
      rw [hdonors i hi]
      exact ((hf _).2.2).symm) masked
  have hmaskedFlag : masked flag = st flag := by
    rw [show masked flag = xored flag from
      (zeroMask_usesOnly register 0).preservesOutside xored hflagR]
    exact (xorWordCircuit_usesOnly cells).preservesOutside st hflagX
  have hxbit (c : Wire × Wire) (hc : c ∈ cells) :
      xored c.2 = xor (st c.2) (st c.1) :=
    xorWordCircuit_bit cells hsep (hmap.symm ▸ hnd) st c hc
  have hmatch : registerMatches register 0 xored = pairEqual cells st := by
    rw [← hmap]
    exact registerMatchesFrom_xor cells 0 st xored hxbit
  have hcontrol : controlsAnd controls masked 513 = pairEqual cells st := by
    rw [controlsAnd_wireAnd]
    have hlist : (List.ofFn fun i : Fin 513 => controls i.val) = register := by
      congr 1
      funext i
      exact hcontrols i.val i.isLt
    rw [hlist, wireAnd_run_zeroMask register 0 xored hnd, hmatch]
  have hflagValue : xor (masked flag) (controlsAnd controls masked 513) =
      xor (st flag) (pairEqual cells st) := by rw [hmaskedFlag, hcontrol]
  have hmaskTwice : Classical.run mask masked = xored :=
    run_zeroMask_twice register 0 xored hnd
  have hxorTwice : Classical.run (xorWordCircuit cells) xored = st :=
    xorWordCircuit_twice cells hsep (hmap.symm ▸ hnd) st
  simp only [dirtyRegisterEqualCircuit, Classical.run_append]
  rw [show Classical.run (dirtyMCX controls donors flag 510) masked =
      masked[flag ↦ xor (st flag) (pairEqual cells st)] by rw [hmcx, hflagValue]]
  rw [(zeroMask_usesOnly register 0).run_upd_outside flag _ masked hflagR,
    hmaskTwice]
  rw [(xorWordCircuit_usesOnly cells).run_upd_outside flag _ xored hflagX,
    hxorTwice, pairEqual_ofFn]

structure DirtyEndpointGeometry (a b target : Fin 513 → Wire) (flag : Wire) : Prop where
  targetInjective : Function.Injective target
  aInjective : Function.Injective a
  bInjective : Function.Injective b
  inputsApart : ∀ i j, a i ≠ target j ∧ b i ≠ target j
  flagApart : ∀ i, flag ≠ a i ∧ flag ≠ b i ∧ flag ≠ target i

def dirtyEndpointTests (a b target : Fin 513 → Wire) (flag : Wire) : Circuit :=
  dirtyRegisterEqualCircuit a target b flag ++ dirtyRegisterEqualCircuit b target a flag

theorem dirtyEndpointTests_run (a b target : Fin 513 → Wire) (flag : Wire)
    (g : DirtyEndpointGeometry a b target flag) (st : BasisState) :
    Classical.run (dirtyEndpointTests a b target flag) st =
      st[flag ↦ xor (st flag) (endpointFlag (st ∘ a) (st ∘ b) (st ∘ target))] := by
  let first := xor (st flag) (decide (st ∘ target = st ∘ a))
  have ha := dirtyRegisterEqualCircuit_run a target b flag g.targetInjective g.bInjective
    (fun i j => (g.inputsApart i j).1) (fun i j => (g.inputsApart i j).2)
    (fun i => ⟨(g.flagApart i).1, (g.flagApart i).2.2, (g.flagApart i).2.1⟩) st
  have hb := dirtyRegisterEqualCircuit_run b target a flag g.targetInjective g.aInjective
    (fun i j => (g.inputsApart i j).2) (fun i j => (g.inputsApart i j).1)
    (fun i => ⟨(g.flagApart i).2.1, (g.flagApart i).2.2, (g.flagApart i).1⟩)
    (st[flag ↦ first])
  rw [word_update_outside target st flag first (fun i => ((g.flagApart i).2.2).symm),
    word_update_outside b st flag first (fun i => ((g.flagApart i).2.1).symm), upd_same] at hb
  simp only [dirtyEndpointTests, Classical.run_append]
  rw [ha]
  change Classical.run (dirtyRegisterEqualCircuit b target a flag) (st[flag ↦ first]) = _
  rw [hb]
  funext w
  by_cases hw : w = flag
  · subst w
    simp only [upd_same, first, endpointFlag]
    cases st flag <;> cases (decide (st ∘ target = st ∘ a)) <;>
      cases (decide (st ∘ target = st ∘ b)) <;> rfl
  · simp only [upd_other _ _ _ hw]

def dirtyEndpointTranspositionCircuit (a b target : Fin 513 → Wire) (flag : Wire) : Circuit :=
  dirtyEndpointTests a b target flag ++ endpointWordCircuit flag (endpointUpdateCells a b target) ++
    dirtyEndpointTests a b target flag

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem dirtyEndpointTransposition_correct (a b target : Fin 513 → Wire) (flag : Wire)
    (g : DirtyEndpointGeometry a b target flag) (st : BasisState) (hz : st flag = false) :
    let out := Classical.run (dirtyEndpointTranspositionCircuit a b target flag) st
    out ∘ target = Equiv.swap (st ∘ a) (st ∘ b) (st ∘ target) ∧
      out flag = false ∧ ∀ w, (∀ i, w ≠ target i) → out w = st w := by
  let guard := endpointFlag (st ∘ a) (st ∘ b) (st ∘ target)
  let ready := st[flag ↦ guard]
  let moved := Classical.run (endpointWordCircuit flag (endpointUpdateCells a b target)) ready
  have hr (row : Fin 513 → Wire) (h : ∀ i, flag ≠ row i) : ready ∘ row = st ∘ row :=
    word_update_outside row st flag guard (fun i => (h i).symm)
  have hra := hr a (fun i => (g.flagApart i).1)
  have hrb := hr b (fun i => (g.flagApart i).2.1)
  have hrt := hr target (fun i => (g.flagApart i).2.2)
  have hsep : endpointSeparated flag (endpointUpdateCells a b target) := by
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    refine ⟨(g.flagApart j).2.2, ?_⟩
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact g.inputsApart i j
  have hguard : ready flag = endpointFlag (ready ∘ a) (ready ∘ b) (ready ∘ target) := by
    rw [hra, hrb, hrt]
    exact upd_same _ _ _
  have ht := endpointWordCircuit_swap flag a b target ready hsep g.targetInjective hguard
  rw [hra, hrb, hrt] at ht
  change moved ∘ target = Equiv.swap (st ∘ a) (st ∘ b) (st ∘ target) at ht
  have hm (w : Wire) (h : ∀ i, w ≠ target i) : moved w = ready w := by
    apply endpointWordCircuit_frame
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact h i
  have hm_comp (row : Fin 513 → Wire) (h : ∀ i j, row i ≠ target j) :
      moved ∘ row = ready ∘ row := by
    funext i
    exact hm (row i) (h i)
  have hma : moved ∘ a = st ∘ a :=
    (hm_comp a (fun i j => (g.inputsApart i j).1)).trans hra
  have hmb : moved ∘ b = st ∘ b :=
    (hm_comp b (fun i j => (g.inputsApart i j).2)).trans hrb
  have hmf : moved flag = guard :=
    (hm flag (fun i => (g.flagApart i).2.2)).trans (upd_same _ _ _)
  have hfirst : Classical.run (dirtyEndpointTests a b target flag) st = ready := by
    rw [dirtyEndpointTests_run a b target flag g st, hz, Bool.false_xor]
  have hlast : Classical.run (dirtyEndpointTests a b target flag) moved = moved[flag ↦ false] := by
    rw [dirtyEndpointTests_run a b target flag g moved, hma, hmb, ht, endpointFlag_swap, hmf]
    change moved[flag ↦ xor guard guard] = _
    rw [Bool.xor_self]
  simp only [dirtyEndpointTranspositionCircuit, Classical.run_append, hfirst]
  change (Classical.run (dirtyEndpointTests a b target flag) moved) ∘ target = _ ∧ _
  rw [hlast]
  refine ⟨?_, upd_same _ _ _, ?_⟩
  · rw [word_update_outside target moved flag false (fun i => ((g.flagApart i).2.2).symm)]
    exact ht
  · intro w hw
    by_cases he : w = flag
    · subst w
      rw [upd_same, hz]
    · rw [upd_other _ _ _ he, hm w hw]
      exact upd_other st flag guard he

theorem dirtyRegisterEqualCircuit_HPFree (a target donor : Fin 513 → Wire) (flag : Wire) :
    Classical.HPFree (dirtyRegisterEqualCircuit a target donor flag) := by
  simp only [dirtyRegisterEqualCircuit, Classical.hpFree_append]
  exact ⟨⟨⟨⟨xorWordCircuit_HPFree _, zeroMask_HPFree _ _⟩,
    dirtyMCX_HPFree _ _ _ _⟩, zeroMask_HPFree _ _⟩, xorWordCircuit_HPFree _⟩

theorem dirtyEndpointTests_HPFree (a b target : Fin 513 → Wire) (flag : Wire) :
    Classical.HPFree (dirtyEndpointTests a b target flag) := by
  simp only [dirtyEndpointTests, Classical.hpFree_append]
  exact ⟨dirtyRegisterEqualCircuit_HPFree _ _ _ _, dirtyRegisterEqualCircuit_HPFree _ _ _ _⟩

theorem dirtyEndpointTransposition_HPFree (a b target : Fin 513 → Wire) (flag : Wire) :
    Classical.HPFree (dirtyEndpointTranspositionCircuit a b target flag) := by
  simp only [dirtyEndpointTranspositionCircuit, Classical.hpFree_append]
  exact ⟨⟨dirtyEndpointTests_HPFree _ _ _ _, endpointWordCircuit_HPFree _ _⟩,
    dirtyEndpointTests_HPFree _ _ _ _⟩

theorem xorWordCircuit_wellFormed_of (a target : Fin 513 → Wire)
    (h : ∀ i, a i ≠ target i) : CircuitWellFormed (xorWordCircuit (equalityCells a target)) := by
  intro gate hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

theorem dirtyRegisterEqualCircuit_wellFormed (a target donor : Fin 513 → Wire) (flag : Wire)
    (ht : Function.Injective target) (hd : Function.Injective donor)
    (hat : ∀ i j, a i ≠ target j) (hdt : ∀ i j, donor i ≠ target j)
    (hf : ∀ i, flag ≠ target i ∧ flag ≠ donor i) :
    CircuitWellFormed (dirtyRegisterEqualCircuit a target donor flag) := by
  let controls : Nat → Wire := fun i => target ⟨i % 513, Nat.mod_lt i (by decide : 0 < 513)⟩
  let donors : Nat → Wire := fun i => donor ⟨i % 511, by
    have := Nat.mod_lt i (by decide : 0 < 511)
    omega⟩
  have hcontrols (i : Nat) (hi : i < 513) : controls i = target ⟨i, hi⟩ := by
    simp only [controls, Nat.mod_eq_of_lt hi]
  have hdonors (i : Nat) (hi : i ≤ 510) : donors i = donor ⟨i, by omega⟩ := by
    simp only [donors, Nat.mod_eq_of_lt (by omega : i < 511)]
  have hmcx : CircuitWellFormed (dirtyMCX controls donors flag 510) := by
    apply dirtyMCX_wellFormed
    · rw [hcontrols 0 (by omega), hcontrols 1 (by omega)]
      intro he
      exact (by decide : (0 : Fin 513) ≠ 1) (ht he)
    · intro i hi j hj he
      rw [hdonors i hi, hdonors j hj] at he
      exact congrArg Fin.val (hd he)
    · intro i hi j hj
      rw [hcontrols i (by omega), hdonors j hj]
      exact (hdt _ _).symm
    · intro i hi
      rw [hcontrols i hi]
      exact ((hf _).1).symm
    · intro i hi
      rw [hdonors i hi]
      exact ((hf _).2).symm
  simp only [dirtyRegisterEqualCircuit, circuitWellFormed_append]
  exact ⟨⟨⟨⟨xorWordCircuit_wellFormed_of a target (fun i => hat i i),
    zeroMask_wellFormed _ _⟩, hmcx⟩, zeroMask_wellFormed _ _⟩,
    xorWordCircuit_wellFormed_of a target (fun i => hat i i)⟩

theorem dirtyEndpointTransposition_wellFormed (a b target : Fin 513 → Wire) (flag : Wire)
    (g : DirtyEndpointGeometry a b target flag) :
    CircuitWellFormed (dirtyEndpointTranspositionCircuit a b target flag) := by
  have ha := dirtyRegisterEqualCircuit_wellFormed a target b flag g.targetInjective g.bInjective
    (fun i j => (g.inputsApart i j).1) (fun i j => (g.inputsApart i j).2)
    (fun i => ⟨(g.flagApart i).2.2, (g.flagApart i).2.1⟩)
  have hb := dirtyRegisterEqualCircuit_wellFormed b target a flag g.targetInjective g.aInjective
    (fun i j => (g.inputsApart i j).2) (fun i j => (g.inputsApart i j).1)
    (fun i => ⟨(g.flagApart i).2.2, (g.flagApart i).1⟩)
  have ht : CircuitWellFormed (dirtyEndpointTests a b target flag) := by
    simpa only [dirtyEndpointTests, circuitWellFormed_append] using And.intro ha hb
  have hu : CircuitWellFormed (endpointWordCircuit flag (endpointUpdateCells a b target)) := by
    apply endpointWordCircuit_wellFormed
    · intro c hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
      refine ⟨(g.flagApart j).2.2, ?_⟩
      intro d hd'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd'
      exact g.inputsApart i j
    · intro c hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact ⟨(g.flagApart i).1, (g.flagApart i).2.1⟩
  simpa only [dirtyEndpointTranspositionCircuit, circuitWellFormed_append] using
    And.intro (And.intro ht hu) ht

theorem zeroMaskFrom_tCount_zero (register : List Wire) (value bit : Nat) :
    ShorECDLP.tCount (zeroMaskFrom register value bit) = 0 := by
  induction register generalizing bit with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : value.testBit bit
    · rw [zeroMaskFrom, if_pos h]
      simpa using ih (bit + 1)
    · rw [zeroMaskFrom, if_neg h, tCount_append, ih]
      rfl

theorem zeroMask_tCount_zero (register : List Wire) (value : Nat) :
    ShorECDLP.tCount (zeroMask register value) = 0 :=
  zeroMaskFrom_tCount_zero register value 0

theorem xorWordCircuit_tCount_zero (cells : List (Wire × Wire)) :
    ShorECDLP.tCount (xorWordCircuit cells) = 0 := by
  induction cells with
  | nil => rfl
  | cons c cs ih => simpa [xorWordCircuit, tCount, tCost] using ih

theorem dirtyRegisterEqualCircuit_tCount (a target donor : Fin 513 → Wire) (flag : Wire) :
    ShorECDLP.tCount (dirtyRegisterEqualCircuit a target donor flag) = 14308 := by
  simp only [dirtyRegisterEqualCircuit, tCount_append, xorWordCircuit_tCount_zero,
    zeroMask_tCount_zero, dirtyMCX_tCount]

theorem dirtyEndpointTests_tCount (a b target : Fin 513 → Wire) (flag : Wire) :
    ShorECDLP.tCount (dirtyEndpointTests a b target flag) = 28616 := by
  simp [dirtyEndpointTests, tCount_append, dirtyRegisterEqualCircuit_tCount]

theorem dirtyEndpointTransposition_tCount (a b target : Fin 513 → Wire) (flag : Wire) :
    ShorECDLP.tCount (dirtyEndpointTranspositionCircuit a b target flag) = 64414 := by
  simp only [dirtyEndpointTranspositionCircuit, tCount_append, dirtyEndpointTests_tCount,
    endpointWordCircuit_tCount, endpointUpdateCells, List.length_ofFn]

theorem circuitWires_subset_of_usesOnly {support : List Wire} {gs : Circuit}
    (h : PaperCircuitUsesOnly support gs) : circuitWires gs ⊆ support := by
  intro w hw
  obtain ⟨gate, hg, hw⟩ := List.mem_flatMap.mp hw
  exact h gate hg w hw

theorem dirtyRegisterEqualCircuit_support (a target donor : Fin 513 → Wire) (flag : Wire)
    (support : List Wire) (ha : ∀ i, a i ∈ support) (ht : ∀ i, target i ∈ support)
    (hd : ∀ i, donor i ∈ support) (hf : flag ∈ support) :
    circuitWires (dirtyRegisterEqualCircuit a target donor flag) ⊆ support := by
  have hx : circuitWires (xorWordCircuit (equalityCells a target)) ⊆ support := by
    intro w hw
    obtain ⟨gate, hg, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha i
    · exact ht i
  have hm : circuitWires (zeroMask (List.ofFn target) 0) ⊆ support := by
    apply (circuitWires_subset_of_usesOnly (zeroMask_usesOnly _ _)).trans
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ht i
  have hmcx : circuitWires (dirtyMCX
      (fun i => target ⟨i % 513, Nat.mod_lt i (by decide : 0 < 513)⟩)
      (fun i => donor ⟨i % 511, by
        have := Nat.mod_lt i (by decide : 0 < 511)
        omega⟩) flag 510) ⊆ support := by
    apply dirtyMCX_support
    · intro i hi
      exact ht _
    · intro i hi
      exact hd _
    · exact hf
  simpa only [dirtyRegisterEqualCircuit, circuitWires, List.flatMap_append,
    List.append_subset] using And.intro (And.intro (And.intro (And.intro hx hm) hmcx) hm) hx

theorem dirtyEndpointTransposition_support (a b target : Fin 513 → Wire) (flag : Wire)
    (support : List Wire) (ha : ∀ i, a i ∈ support) (hb : ∀ i, b i ∈ support)
    (ht : ∀ i, target i ∈ support) (hf : flag ∈ support) :
    circuitWires (dirtyEndpointTranspositionCircuit a b target flag) ⊆ support := by
  have hea := dirtyRegisterEqualCircuit_support a target b flag support ha ht hb hf
  have heb := dirtyRegisterEqualCircuit_support b target a flag support hb ht ha hf
  have he : circuitWires (dirtyEndpointTests a b target flag) ⊆ support := by
    simpa only [dirtyEndpointTests, circuitWires, List.flatMap_append,
      List.append_subset] using And.intro hea heb
  have hu : circuitWires (endpointWordCircuit flag (endpointUpdateCells a b target)) ⊆ support := by
    intro w hw
    obtain ⟨gate, hg, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp only [endpointBitCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    all_goals simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hw
    all_goals rcases hw with rfl | rfl | rfl
    all_goals first | exact hf | exact ha i | exact hb i | exact ht i
  simpa only [dirtyEndpointTranspositionCircuit, circuitWires, List.flatMap_append,
    List.append_subset] using And.intro (And.intro he hu) he

end ShorECDLP.Compact
