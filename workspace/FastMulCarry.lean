import ShorECDLP.Submission.Entrant.Compiler

/-!
# Stored-carry source builders for Brief 22

This file starts the exact circuit layer independently of the call-site wrappers.
`chunkAddOps` is the literal Gold/ecdsa.fail carry recipe: one unconditional CCX
per computed carry, followed by exact X-measure/reset of every owned carry.  A
non-final chunk leaves its carry-out coherent for the next chunk.
-/

namespace ShorECDLP.Entrant.FastMul

open Quantum ShorECDLP.Challenge
open Paper2607_13816 Paper2607_13816.ChallengeMigration

def carryForward (source target carry : Wire) : Option Wire -> Circuit
  | none => [.CCX source target carry]
  | some previous =>
      [.CX previous source, .CX previous target, .CCX source target carry,
        .CX previous carry]

def carryIsolate (carry : Wire) : Option Wire -> Circuit
  | none => []
  | some previous => [.CX previous carry]

def carryFinishSum (source target : Wire) : Option Wire -> Circuit
  | none => [.CX source target]
  | some previous => [.CX previous source, .CX source target]

def carryFinishCompare (source target : Wire) : Option Wire -> Circuit
  | none => []
  | some previous => [.CX previous target, .CX previous source]

def previousBit (previous : Option Wire) (state : BasisState) : Bool :=
  previous.elim false state

def carryUnwindOps {n : Nat} (source target carry : Wire)
    (previous : Option Wire) : List (LookupOp n) :=
  [ordinaryOp (carryIsolate carry previous), .erase source target carry,
    ordinaryOp (carryFinishSum source target previous)]

def carryCompareUnwindOps {n : Nat} (source target carry : Wire)
    (previous : Option Wire) : List (LookupOp n) :=
  [ordinaryOp (carryIsolate carry previous), .erase source target carry,
    ordinaryOp (carryFinishCompare source target previous)]

/-- One exact chunk. `work` has one lane for every non-final bit.  `outgoing`
is absent for the final chunk and otherwise owns its carry-out. -/
def chunkAddOps {n : Nat} :
    List Wire -> List Wire -> List Wire -> Option Wire -> Option Wire -> List (LookupOp n)
  | [source], [target], [], previous, none =>
      [ordinaryOp (carryFinishSum source target previous)]
  | [source], [target], [], previous, some outgoing =>
      [ordinaryOp (carryForward source target outgoing previous ++
        carryFinishSum source target previous)]
  | source :: sources, target :: targets, carry :: carries, previous, outgoing =>
      ordinaryOp (carryForward source target carry previous) ::
        chunkAddOps sources targets carries (some carry) outgoing ++
        carryUnwindOps source target carry previous
  | _, _, _, _, _ => []

def chunkAddProgram (n start : Nat) (sources targets work : List Wire)
    (incoming outgoing : Option Wire) :
    Straight n start (start + lookupMeasurements
      (chunkAddOps (n := n) sources targets work incoming outgoing)) :=
  lookupProgram n (chunkAddOps (n := n) sources targets work incoming outgoing) start

/-- Carry-only replay.  Unlike `chunkAddOps`, this restores both input words and
XORs the final carry into `outgoing`.  It is therefore the exact coherent way to
clear a boundary/quotient flag that already equals that carry predicate. -/
def chunkCompareOps {n : Nat} :
    List Wire -> List Wire -> List Wire -> Option Wire -> Wire -> List (LookupOp n)
  | [source], [target], [], previous, outgoing =>
      [ordinaryOp (carryForward source target outgoing previous ++
        carryFinishCompare source target previous)]
  | source :: sources, target :: targets, carry :: carries, previous, outgoing =>
      ordinaryOp (carryForward source target carry previous) ::
        chunkCompareOps sources targets carries (some carry) outgoing ++
        carryCompareUnwindOps source target carry previous
  | _, _, _, _, _ => []

def chunkCompareProgram (n start : Nat) (sources targets work : List Wire)
    (incoming : Option Wire) (outgoing : Wire) :
    Straight n start (start + lookupMeasurements
      (chunkCompareOps (n := n) sources targets work incoming outgoing)) :=
  lookupProgram n (chunkCompareOps (n := n) sources targets work incoming outgoing) start

def opCCX {n : Nat} : LookupOp n -> Nat
  | .gates gs => AndGadget.ccxCount
      (gs.flatMap (TemplateGate.instantiate (fun _ => false)))
  | .erase _ _ _ => 0

def opsCCX {n : Nat} (ops : List (LookupOp n)) : Nat :=
  (ops.map opCCX).sum

@[simp] theorem measurements_ordinary {n : Nat} (gs : Circuit) :
    lookupMeasurements [ordinaryOp (n := n) gs] = 0 := rfl

@[simp] theorem opCCX_erase {n : Nat} (a b t : Wire) :
    opCCX (LookupOp.erase (n := n) a b t) = 0 := rfl

@[simp] theorem opCCX_ordinary {n : Nat} (gs : Circuit) :
    opCCX (ordinaryOp (n := n) gs) = AndGadget.ccxCount gs := by
  simp [opCCX, ordinaryOp, literal_gates]

@[simp] theorem opsCCX_nil {n : Nat} : opsCCX ([] : List (LookupOp n)) = 0 := rfl

@[simp] theorem opsCCX_cons {n : Nat} (op : LookupOp n) (ops : List (LookupOp n)) :
    opsCCX (op :: ops) = opCCX op + opsCCX ops := by
  simp [opsCCX]

@[simp] theorem opsCCX_append {n : Nat} (xs ys : List (LookupOp n)) :
    opsCCX (xs ++ ys) = opsCCX xs + opsCCX ys := by
  simp [opsCCX, List.sum_append]

@[simp] theorem ccx_carryForward_none (source target carry : Wire) :
    AndGadget.ccxCount (carryForward source target carry none) = 1 := by
  rfl

@[simp] theorem ccx_carryForward_some (source target carry previous : Wire) :
    AndGadget.ccxCount (carryForward source target carry (some previous)) = 1 := by
  rfl

@[simp] theorem ccx_carryIsolate (carry : Wire) (previous : Option Wire) :
    AndGadget.ccxCount (carryIsolate carry previous) = 0 := by
  cases previous <;> rfl

@[simp] theorem ccx_carryFinishSum (source target : Wire) (previous : Option Wire) :
    AndGadget.ccxCount (carryFinishSum source target previous) = 0 := by
  cases previous <;> rfl

@[simp] theorem measurements_carryUnwindOps {n : Nat}
    (source target carry : Wire) (previous : Option Wire) :
    lookupMeasurements (carryUnwindOps (n := n) source target carry previous) = 1 := by
  rfl

@[simp] theorem ccx_carryUnwindOps {n : Nat}
    (source target carry : Wire) (previous : Option Wire) :
    opsCCX (carryUnwindOps (n := n) source target carry previous) = 0 := by
  cases previous <;> rfl

theorem chunkAddOps_metrics {n : Nat} (sources targets work : List Wire)
    (incoming outgoing : Option Wire)
    (hlen : sources.length = targets.length)
    (hpos : 0 < sources.length)
    (hwork : work.length + 1 = sources.length) :
    lookupMeasurements (chunkAddOps (n := n) sources targets work incoming outgoing) =
        work.length /\
      opsCCX (chunkAddOps (n := n) sources targets work incoming outgoing) =
        work.length + if outgoing.isSome then 1 else 0 := by
  induction sources generalizing targets work incoming with
  | nil => simp at hpos
  | cons source sources ih =>
      cases targets with
      | nil => simp at hlen
      | cons target targets =>
          cases work with
          | nil =>
              have hs : sources = [] := List.length_eq_zero_iff.mp (by simpa using hwork.symm)
              have ht : targets = [] := List.length_eq_zero_iff.mp (by simpa [hs] using hlen.symm)
              subst sources
              subst targets
              cases outgoing <;> cases incoming <;>
                constructor <;> rfl
          | cons carry carries =>
              have hpos' : 0 < sources.length := by simp at hwork; omega
              have hlen' : sources.length = targets.length := by simpa using hlen
              have hwork' : carries.length + 1 = sources.length := by simpa using hwork
              have hih := ih targets carries (some carry) hlen' hpos' hwork'
              rcases hih with ⟨hmeasure, hccx⟩
              cases incoming <;> cases outgoing
              all_goals
                constructor
                · simp [chunkAddOps, carryUnwindOps, lookupMeasurements_append,
                    lookupMeasurements, ordinaryOp, hmeasure]
                · simp [chunkAddOps, carryUnwindOps, carryForward,
                    carryIsolate, carryFinishSum, AndGadget.ccxCount, hccx,
                    Nat.add_comm]

@[simp] theorem measurements_carryCompareUnwindOps {n : Nat}
    (source target carry : Wire) (previous : Option Wire) :
    lookupMeasurements (carryCompareUnwindOps (n := n) source target carry previous) = 1 := by
  rfl

@[simp] theorem ccx_carryCompareUnwindOps {n : Nat}
    (source target carry : Wire) (previous : Option Wire) :
    opsCCX (carryCompareUnwindOps (n := n) source target carry previous) = 0 := by
  cases previous <;> rfl

theorem chunkCompareOps_metrics {n : Nat} (sources targets work : List Wire)
    (incoming : Option Wire) (outgoing : Wire)
    (hlen : sources.length = targets.length)
    (hpos : 0 < sources.length)
    (hwork : work.length + 1 = sources.length) :
    lookupMeasurements
        (chunkCompareOps (n := n) sources targets work incoming outgoing) =
        work.length /\
      opsCCX (chunkCompareOps (n := n) sources targets work incoming outgoing) =
        sources.length := by
  induction sources generalizing targets work incoming with
  | nil => simp at hpos
  | cons source sources ih =>
      cases targets with
      | nil => simp at hlen
      | cons target targets =>
          cases work with
          | nil =>
              have hs : sources = [] := List.length_eq_zero_iff.mp (by simpa using hwork.symm)
              have ht : targets = [] := List.length_eq_zero_iff.mp (by simpa [hs] using hlen.symm)
              subst sources
              subst targets
              cases incoming <;> constructor <;> rfl
          | cons carry carries =>
              have hpos' : 0 < sources.length := by simp at hwork; omega
              have hlen' : sources.length = targets.length := by simpa using hlen
              have hwork' : carries.length + 1 = sources.length := by simpa using hwork
              have hih := ih targets carries (some carry) hlen' hpos' hwork'
              rcases hih with ⟨hmeasure, hccx⟩
              cases incoming
              all_goals
                constructor
                · simp [chunkCompareOps, carryCompareUnwindOps,
                    lookupMeasurements_append, lookupMeasurements, ordinaryOp, hmeasure]
                · simp [chunkCompareOps, carryCompareUnwindOps, carryForward,
                    carryIsolate, carryFinishCompare, AndGadget.ccxCount, hccx,
                    Nat.add_comm]

/-! Controlled public-mask carries.  A true mask bit contributes the live
`flag`; a false bit contributes zero.  The true-bit recurrence is quadratic
parity (`flag*target xor flag*previous xor target*previous`), so it needs two
literal CCXs but still has an entirely Clifford X-measurement correction. -/

def maskCarryForward (flag target carry : Wire) (previous : Option Wire)
    (maskBit : Bool) : Circuit :=
  match maskBit, previous with
  | false, none => []
  | false, some p => [.CCX p target carry]
  | true, none => [.CCX flag target carry]
  | true, some p =>
      [.CX p target, .CCX flag target carry, .CX p target,
        .CCX p target carry]

def maskCarryCorrection (flag target : Wire) (previous : Option Wire)
    (maskBit : Bool) : Circuit :=
  match maskBit, previous with
  | false, none => []
  | false, some p => controlledZ p target
  | true, none => controlledZ flag target
  | true, some p =>
      controlledZ flag target ++ controlledZ flag p ++ controlledZ target p

def maskCarryEraseProgram (n start : Nat) (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool) : Straight n start (start + 1) :=
  .measure carry
    (recordGates (Fin.last start) (maskCarryCorrection flag target previous maskBit) .done)

def maskFinishSum (flag target : Wire) (previous : Option Wire)
    (maskBit : Bool) : Circuit :=
  (if maskBit then [.CX flag target] else []) ++
    previous.elim [] (fun p => [.CX p target])

def maskChunkAddProgram (n : Nat) :
    (start : Nat) -> Wire -> List Wire -> List Bool -> List Wire -> Option Wire ->
      Option Wire -> (count : Nat) × Straight n start (start + count)
  | start, flag, [target], [maskBit], [], previous, none =>
      ⟨0, literalProgram (maskFinishSum flag target previous maskBit)⟩
  | start, flag, [target], [maskBit], [], previous, some outgoing =>
      ⟨0, literalProgram (maskCarryForward flag target outgoing previous maskBit ++
        maskFinishSum flag target previous maskBit)⟩
  | start, flag, target :: targets, maskBit :: maskBits, carry :: carries,
      previous, outgoing =>
      let tail := maskChunkAddProgram n start flag targets maskBits carries
        (some carry) outgoing
      let erase : Straight n (start + tail.1) (start + tail.1 + 1) :=
        maskCarryEraseProgram n (start + tail.1) flag target carry previous maskBit
      prependCompiled (maskCarryForward flag target carry previous maskBit)
        (appendCompiled tail ⟨1, castFinish (by omega) erase⟩)
  | start, _, _, _, _, _, _ => ⟨0, .done⟩

def maskCarryCCX (previous : Option Wire) (maskBit : Bool) : Nat :=
  match maskBit, previous with
  | false, none => 0
  | false, some _ => 1
  | true, none => 1
  | true, some _ => 2

@[simp] theorem maskCarryForward_ccx (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool) :
    AndGadget.ccxCount (maskCarryForward flag target carry previous maskBit) =
      maskCarryCCX previous maskBit := by
  cases maskBit <;> cases previous <;> rfl

@[simp] theorem maskCarryCorrection_ccx (flag target : Wire)
    (previous : Option Wire) (maskBit : Bool) :
    AndGadget.ccxCount (maskCarryCorrection flag target previous maskBit) = 0 := by
  cases maskBit <;> cases previous <;>
    simp [maskCarryCorrection, controlledZ, AndGadget.ccxCount]

def maskCarryValue (flag target : Wire) (previous : Option Wire)
    (maskBit : Bool) (state : BasisState) : Bool :=
  match maskBit with
  | false => state target && previousBit previous state
  | true =>
      (state flag && state target) ^^ (state flag && previousBit previous state) ^^
        (state target && previousBit previous state)

def MaskCarryComputed (flag target carry : Wire) (previous : Option Wire)
    (maskBit : Bool) (state : BasisState) : Prop :=
  state carry = maskCarryValue flag target previous maskBit state

def maskCarryCorrectionFamily (flag target : Wire) (previous : Option Wire)
    (maskBit : Bool) : List Bool -> Circuit
  | [true] => maskCarryCorrection flag target previous maskBit
  | _ => []

theorem run_maskCarryCorrection_ket (flag target : Wire)
    (previous : Option Wire) (maskBit : Bool) (state : BasisState)
    (hft : flag ≠ target)
    (hfp : ∀ p ∈ previous, flag ≠ p)
    (htp : ∀ p ∈ previous, target ≠ p) :
    Quantum.run (maskCarryCorrection flag target previous maskBit) (ket state) =
      (if maskCarryValue flag target previous maskBit state then (-1 : ℂ) else 1) •
        ket state := by
  cases previous with
  | none =>
      cases maskBit
      · simp [maskCarryCorrection, maskCarryValue, previousBit]
      · rw [show maskCarryCorrection flag target none true = controlledZ flag target by rfl]
        rw [run_controlledZ_ket flag target state hft]
        simp [maskCarryValue, previousBit]
  | some previous =>
      have hfp' : flag ≠ previous := hfp previous (by simp)
      have htp' : target ≠ previous := htp previous (by simp)
      cases maskBit
      · rw [show maskCarryCorrection flag target (some previous) false =
            controlledZ previous target by rfl]
        rw [run_controlledZ_ket previous target state (Ne.symm htp')]
        cases ht : state target <;> cases hp : state previous <;>
          simp [maskCarryValue, previousBit, ht, hp]
      · simp only [maskCarryCorrection, Quantum.run_append]
        let c₁ : ℂ := if state flag && state target then -1 else 1
        let c₂ : ℂ := if state flag && state previous then -1 else 1
        let c₃ : ℂ := if state target && state previous then -1 else 1
        have h₁ : Quantum.run (controlledZ flag target) (ket state) = c₁ • ket state := by
          simpa [c₁] using run_controlledZ_ket flag target state hft
        have h₂ : Quantum.run (controlledZ flag previous) (ket state) = c₂ • ket state := by
          simpa [c₂] using run_controlledZ_ket flag previous state hfp'
        have h₃ : Quantum.run (controlledZ target previous) (ket state) = c₃ • ket state := by
          simpa [c₃] using run_controlledZ_ket target previous state htp'
        rw [h₁]
        change Quantum.run (controlledZ target previous)
          (Quantum.run (controlledZ flag previous) (c₁ • ket state)) = _
        calc
          _ = Quantum.run (controlledZ target previous)
                (c₁ • Quantum.run (controlledZ flag previous) (ket state)) := by
              exact congrArg (Quantum.run (controlledZ target previous))
                ((Quantum.run (controlledZ flag previous)).map_smul c₁ (ket state))
          _ = c₁ • Quantum.run (controlledZ target previous)
                (Quantum.run (controlledZ flag previous) (ket state)) := by
              exact (Quantum.run (controlledZ target previous)).map_smul c₁ _
          _ = c₁ • Quantum.run (controlledZ target previous) (c₂ • ket state) := by
              rw [h₂]
          _ = c₁ • (c₂ • Quantum.run (controlledZ target previous) (ket state)) := by
              rw [(Quantum.run (controlledZ target previous)).map_smul]
          _ = c₁ • (c₂ • (c₃ • ket state)) := by rw [h₃]
          _ = _ := by
            cases hf : state flag <;> cases ht : state target <;>
              cases hp : state previous <;>
              simp [c₁, c₂, c₃, maskCarryValue, previousBit, hf, ht, hp]

theorem maskCarryCorrection_phase (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool)
    (hnd : (flag :: target :: carry :: previous.toList).Nodup) :
    RegisterXPhaseCorrectionOn [carry]
      (maskCarryCorrectionFamily flag target previous maskBit)
      (MaskCarryComputed flag target carry previous maskBit) := by
  have hft : flag ≠ target := by
    intro h
    apply (List.nodup_cons.mp hnd).1
    simp [h]
  have hfc : flag ≠ carry := by
    intro h
    apply (List.nodup_cons.mp hnd).1
    simp [h]
  have htc : target ≠ carry := by
    intro h
    apply (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    simp [h]
  have hfp : ∀ p ∈ previous, flag ≠ p := by
    cases previous with
    | none => simp
    | some previous =>
        intro p hp
        simp only [Option.mem_some_iff] at hp
        subst p
        intro h
        apply (List.nodup_cons.mp hnd).1
        simp [h]
  have htp : ∀ p ∈ previous, target ≠ p := by
    cases previous with
    | none => simp
    | some previous =>
        intro p hp
        simp only [Option.mem_some_iff] at hp
        subst p
        intro h
        apply (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
        simp [h]
  have hcp : ∀ p ∈ previous, carry ≠ p := by
    cases previous with
    | none => simp
    | some previous =>
        intro p hp
        simp only [Option.mem_some_iff] at hp
        subst p
        intro h
        apply (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
        simp [h]
  intro outcomes hlength state hcomputed
  cases outcomes with
  | nil => simp at hlength
  | cons outcome outcomes =>
      have houtcomes : outcomes = [] := by simpa using hlength
      subst outcomes
      cases outcome
      · simp [maskCarryCorrectionFamily, clearRegister, registerXPhase]
      · simp only [maskCarryCorrectionFamily]
        rw [run_maskCarryCorrection_ket flag target previous maskBit
          (clearRegister [carry] state) hft hfp htp]
        have hvalue :
            maskCarryValue flag target previous maskBit (clearRegister [carry] state) =
              maskCarryValue flag target previous maskBit state := by
          cases previous with
          | none =>
              simp [maskCarryValue, previousBit, clearRegister, upd, hfc, htc]
          | some previous =>
              have hcp' : carry ≠ previous := hcp previous (by simp)
              simp [maskCarryValue, previousBit, clearRegister, upd, hfc, htc,
                Ne.symm hcp']
        rw [hvalue]
        unfold MaskCarryComputed at hcomputed
        rw [← hcomputed]
        simp [registerXPhase, clearRegister]

theorem maskCarryErase_coherent (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool)
    (hnd : (flag :: target :: carry :: previous.toList).Nodup) :
    CoherentlyImplementsOn
      (measureResetWithCorrection [carry]
        (maskCarryCorrectionFamily flag target previous maskBit))
      (clearRegisterMap [carry])
      (MaskCarryComputed flag target carry previous maskBit) := by
  apply measureResetWithCorrection_coherent
  · simp
  · exact maskCarryCorrection_phase flag target carry previous maskBit hnd

theorem maskCarryForward_computed (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool) (state : BasisState)
    (hnd : (flag :: target :: carry :: previous.toList).Nodup)
    (hclean : state carry = false) :
    MaskCarryComputed flag target carry previous maskBit
      (Classical.run (maskCarryForward flag target carry previous maskBit) state) := by
  cases previous with
  | none =>
      simp only [Option.toList_none, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, not_false_eq_true, not_or] at hnd
      rcases hnd with ⟨⟨hft, hfc⟩, htc, _⟩
      cases maskBit <;> cases hf : state flag <;> cases ht : state target <;>
        simp [MaskCarryComputed, maskCarryValue, previousBit, maskCarryForward,
          Classical.run, Classical.applyGate, upd, hclean, hfc, htc, hf, ht]
  | some previous =>
      have hft : flag ≠ target := by
        intro h
        apply (List.nodup_cons.mp hnd).1
        simp [h]
      have hfc : flag ≠ carry := by
        intro h
        apply (List.nodup_cons.mp hnd).1
        simp [h]
      have hfp : flag ≠ previous := by
        intro h
        apply (List.nodup_cons.mp hnd).1
        simp [h]
      have htc : target ≠ carry := by
        intro h
        apply (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
        simp [h]
      have htp : target ≠ previous := by
        intro h
        apply (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
        simp [h]
      have hcp : carry ≠ previous := by
        intro h
        apply (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
        simp [h]
      cases maskBit <;> cases hf : state flag <;> cases ht : state target <;>
        cases hp : state previous <;>
        simp [MaskCarryComputed, maskCarryValue, previousBit, maskCarryForward,
          Classical.run, Classical.applyGate, upd, hclean, hft, hfc,
          htc,
          Ne.symm htc, Ne.symm htp, Ne.symm hcp, hf, ht, hp]

theorem maskCarryEraseProgram_run (n start : Nat) (flag target carry : Wire)
    (previous : Option Wire) (maskBit : Bool) (read : ConstantBit n -> Bool)
    (history : Fin start -> Bool) :
    ((maskCarryEraseProgram n start flag target carry previous maskBit).instantiate
      read history).run =
      (measureResetWithCorrection [carry]
        (maskCarryCorrectionFamily flag target previous maskBit)).run := by
  simp [maskCarryEraseProgram, Straight.instantiate, AdaptiveCircuit.run,
    recordGates_run, measureResetWithCorrection, maskCarryCorrectionFamily]

def tightChunks : List Nat :=
  [23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 8]

theorem tightChunks_sum : tightChunks.sum = 256 := by decide +kernel
theorem tightChunks_prefix : (tightChunks.dropLast).sum = 248 := by decide +kernel
theorem tightChunks_count : tightChunks.length = 17 := by decide +kernel

theorem carryForward_isolated (source target carry : Wire) (previous : Option Wire)
    (state : BasisState)
    (hnd : (source :: target :: carry :: previous.toList).Nodup)
    (hclean : state carry = false) :
    PathAndComputed source target carry
      (Classical.run (carryIsolate carry previous)
        (Classical.run (carryForward source target carry previous) state)) := by
  unfold PathAndComputed
  cases previous with
  | none =>
      simp only [Option.toList_none, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or] at hnd
      simp only [and_true, List.nodup_nil] at hnd
      rcases hnd with ⟨⟨hst, hsc⟩, htc⟩
      simp [carryForward, carryIsolate, Classical.run, Classical.applyGate, upd,
        hclean, hsc, htc]
  | some previous =>
      simp only [Option.toList_some, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, not_false_eq_true, not_or] at hnd
      simp only [and_true, List.nodup_nil] at hnd
      rcases hnd with ⟨⟨hst, hsc, hsp⟩, ⟨htc, htp⟩, hcp⟩
      simp only [carryForward, carryIsolate, Classical.run, Classical.applyGate]
      cases hs : state source <;> cases ht : state target <;>
        cases hp : state previous <;>
        simp [upd, hclean, hst, hsc, htc,
          Ne.symm hst, Ne.symm hsc, Ne.symm hsp, Ne.symm htc,
          Ne.symm htp, Ne.symm hcp, hs, ht, hp]

theorem carryForward_ccx_literal (source target carry : Wire)
    (previous : Option Wire) :
    AndGadget.ccxCount (carryForward source target carry previous) = 1 := by
  cases previous <;> rfl

def terminalCarryPhase (source target : Wire) : Option Wire -> Circuit
  | none => controlledZ target source
  | some previous =>
      controlledZ target source ++ controlledZ target previous ++
        controlledZ source previous

/-- Phase oracle for a measured carry-out.  Carry computations are literal and
unconditional; only the terminal Clifford phases inspect `outcome`. -/
def phaseCarryProgram (n start : Nat) :
    List Wire -> List Wire -> List Wire -> Option Wire -> Fin start ->
      (count : Nat) × Straight n start (start + count)
  | [source], [target], [], previous, outcome =>
      ⟨0, recordGates outcome (terminalCarryPhase source target previous) .done⟩
  | source :: sources, target :: targets, carry :: carries, previous, outcome =>
      let tail := phaseCarryProgram n start sources targets carries (some carry) outcome
      let unwindStart := start + tail.1
      let unwind : Straight n unwindStart (unwindStart + 1) :=
        (literalProgram (carryIsolate carry previous)).append
          ((andEraseProgram n unwindStart source target carry).append
            (literalProgram (carryFinishCompare source target previous)))
      prependCompiled (carryForward source target carry previous)
        (appendCompiled tail ⟨1, unwind⟩)
  | _, _, _, _, _ => ⟨0, .done⟩

def complementCircuit (word : List Wire) : Circuit := word.map Gate.X

def phaseCompareProgram (n start : Nat) (sources targets work : List Wire)
    (incoming : Option Wire) (outcome : Fin start) :
    (count : Nat) × Straight n start (start + count) :=
  surroundCompiled (complementCircuit targets) (complementCircuit targets)
    (phaseCarryProgram n start sources targets work incoming outcome)

@[simp] theorem ccx_carryFinishCompare (source target : Wire)
    (previous : Option Wire) :
    AndGadget.ccxCount (carryFinishCompare source target previous) = 0 := by
  cases previous <;> rfl

@[simp] theorem ccx_terminalCarryPhase (source target : Wire)
    (previous : Option Wire) :
    AndGadget.ccxCount (terminalCarryPhase source target previous) = 0 := by
  cases previous <;> simp [terminalCarryPhase, controlledZ, AndGadget.ccxCount]

theorem phaseCarryProgram_measurements (n start : Nat)
    (sources targets work : List Wire) (incoming : Option Wire) (outcome : Fin start)
    (hlen : sources.length = targets.length)
    (hpos : 0 < sources.length)
    (hwork : work.length + 1 = sources.length) :
    (phaseCarryProgram n start sources targets work incoming outcome).1 = work.length := by
  induction sources generalizing targets work incoming with
  | nil => simp at hpos
  | cons source sources ih =>
      cases targets with
      | nil => simp at hlen
      | cons target targets =>
          cases work with
          | nil =>
              have hs : sources = [] := List.length_eq_zero_iff.mp (by simpa using hwork.symm)
              have ht : targets = [] := List.length_eq_zero_iff.mp (by simpa [hs] using hlen.symm)
              subst sources
              subst targets
              rfl
          | cons carry carries =>
              have hpos' : 0 < sources.length := by simp at hwork; omega
              have hlen' : sources.length = targets.length := by simpa using hlen
              have hwork' : carries.length + 1 = sources.length := by simpa using hwork
              have hih := ih targets carries (some carry) hlen' hpos' hwork'
              simp [phaseCarryProgram, prependCompiled, appendCompiled, hih]

theorem phaseCompareProgram_measurements (n start : Nat)
    (sources targets work : List Wire) (incoming : Option Wire) (outcome : Fin start)
    (hlen : sources.length = targets.length)
    (hpos : 0 < sources.length)
    (hwork : work.length + 1 = sources.length) :
    (phaseCompareProgram n start sources targets work incoming outcome).1 = work.length := by
  exact phaseCarryProgram_measurements n start sources targets work incoming outcome
    hlen hpos hwork

def boundaryEraseProgram (n start : Nat) (sources targets work : List Wire)
    (incoming : Option Wire) (boundary : Wire) :
    (count : Nat) × Straight n start (start + count) :=
  let phase := phaseCompareProgram n (start + 1) sources targets work incoming
    (Fin.last start)
  ⟨1 + phase.1, castFinish (by omega) (.measure boundary phase.2)⟩

/-- Coherently clear a held chunk carry.  For a completed sum, adding the
source to the complemented sum (with the same incoming carry) reproduces the
old outgoing carry.  XORing that predicate into `boundary` clears it. -/
def boundaryClearProgram (n start : Nat) (sources targets work : List Wire)
    (incoming : Option Wire) (boundary : Wire) :
    (count : Nat) × Straight n start (start + count) :=
  surroundCompiled (complementCircuit targets) (complementCircuit targets)
    ⟨lookupMeasurements (chunkCompareOps (n := n) sources targets work incoming boundary),
      chunkCompareProgram n start sources targets work incoming boundary⟩

/-- Exact multi-chunk word addition.  Earlier boundary carries remain in the
front of `pool`; all other pool lanes are reused by the next chunk.  Boundary
erasures run in reverse order after the complete sum has been formed. -/
def wordAddProgram (n start : Nat) :
    List Nat -> List Wire -> List Wire -> List Wire -> Option Wire ->
      (count : Nat) × Straight n start (start + count)
  | [], _, _, _, _ => ⟨0, .done⟩
  | [width], sources, targets, pool, incoming =>
      let work := pool.take (width - 1)
      let ops := chunkAddOps (n := n) (sources.take width) (targets.take width)
        work incoming none
      ⟨lookupMeasurements ops, lookupProgram n ops start⟩
  | width :: nextWidth :: widths, sources, targets, [], incoming =>
      wordAddProgram n start (nextWidth :: widths) (sources.drop width)
        (targets.drop width) (List.nil : List Wire) incoming
  | width :: nextWidth :: widths, sources, targets, boundary :: pool, incoming =>
      let chunkSources := sources.take width
      let chunkTargets := targets.take width
      let work := pool.take (width - 1)
      let firstOps := chunkAddOps (n := n) chunkSources chunkTargets work incoming
        (some boundary)
      let first : (count : Nat) × Straight n start (start + count) :=
        ⟨lookupMeasurements firstOps, lookupProgram n firstOps start⟩
      let tail := wordAddProgram n (start + first.1) (nextWidth :: widths)
        (sources.drop width) (targets.drop width) pool (some boundary)
      let erase := boundaryClearProgram n (start + first.1 + tail.1)
        chunkSources chunkTargets work incoming boundary
      appendCompiled first (appendCompiled tail erase)

def wordAddCCX (chunks : List Nat) : Nat :=
  match chunks with
  | [] => 0
  | _ => chunks.sum - 1 + chunks.dropLast.sum

theorem tightWordAddCCX : wordAddCCX tightChunks = 503 := by decide +kernel

end ShorECDLP.Entrant.FastMul
