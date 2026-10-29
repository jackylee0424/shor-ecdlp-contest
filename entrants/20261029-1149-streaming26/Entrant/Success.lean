import ShorECDLP.Submission.Entrant.Trial
import ShorECDLP.Framework.Quantum.TerminalInterference
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.StreamHistory

/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
The round count is reduced from 56 to 26 using the upstream per-round
0.163 acceptance bound. The entry and decoder share streamingRounds.
Packaged into existing tracked files for the official source policy;
workspace/port_upstream.py and workspace/package_streaming.py reproduce it.
-/

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.TaggedProbability -/
section Port_TaggedProbability

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] fourierOutcomes streamAddress

/-- A terminal instrument may depend on Fourier outcomes, but not erased arithmetic records. -/
noncomputable def fourierContinuationInstrument (prior : List Bool) (next : List Bool → Instrument) : Instrument :=
  (fourierOutcomes 16).flatMap (fun bits => (next bits).map
    (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse streamAddress.reverse prior bits⟩ b))

noncomputable def streamBlockContinuation (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) : Instrument :=
  (streamBlockOutcomes call prior).flatMap (fun tagged => (next tagged.1).map (tagged.2.seq))

theorem streamBlockContinuation_eq (call : AdaptiveCircuit) (prior : List Bool)
    (next : List Bool → Instrument) :
    streamBlockContinuation call prior next =
      (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run.seq
        (call.run.seq (fourierContinuationInstrument prior next)) := by
  simp only [streamBlockContinuation,streamBlockOutcomes,AdaptiveCircuit.run_seq,
    Instrument.seq,fourierContinuationInstrument,
    show streamAddress.length=16 from by simp [streamAddress],
    List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro bits hbits
  apply List.map_congr_left
  intro c hc
  cases a; cases b; cases c
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem unitary_done_seq_bornMass (c : Circuit) (J : Instrument) (ψ : State) :
    ((AdaptiveCircuit.unitary c .done).run.seq J).bornMass ψ = J.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run,Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,
    List.append_nil,Instrument.bornMass,List.map_map,Function.comp_def,InstrumentBranch.seq,LinearMap.comp_apply]
  rfl

/-- Eliminate all arithmetic measurement branches before a Fourier-dependent continuation. -/
theorem streamBlockContinuation_mass {call : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {Valid : BasisState → Prop} (h : CoherentlyImplementsOn call ideal Valid)
    (prior : List Bool) (next : List Bool → Instrument) (ψ : State)
    (hs : SupportedOn Valid (Quantum.run (streamAddress.map Gate.H) ψ)) :
    (streamBlockContinuation call prior next).bornMass ψ =
      (fourierContinuationInstrument prior next).bornMass
        (ideal (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  rw [streamBlockContinuation_eq]
  rw [unitary_done_seq_bornMass]
  exact h.terminalMass hs _


theorem fourierContinuationInstrument_mass (prior : List Bool)
    (next : List Bool → Instrument) (ψ : State) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      ((fourierOutcomes 16).map (fun bits =>
        (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ))).sum := by
  simp only [fourierContinuationInstrument, Instrument.bornMass, List.map_flatMap,
    List.map_map, Function.comp_def, InstrumentBranch.seq,
    LinearMap.comp_apply]
  generalize fourierOutcomes 16 = outcomes
  induction outcomes with
  | nil => rfl
  | cons a outcomes ih => simpa only [List.flatMap_cons, List.sum_append,
      List.map_cons, List.sum_cons] using congrArg (_ + ·) ih

/-- A continuation replacement only needs equality on the reached Fourier states. -/
theorem fourierContinuationInstrument_mass_congr (prior : List Bool)
    (next next' : List Bool → Instrument) (ψ : State)
    (h : ∀ bits ∈ fourierOutcomes 16,
      (next bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ) =
      (next' bits).bornMass (fourierBranch .inverse streamAddress.reverse prior bits ψ)) :
    (fourierContinuationInstrument prior next).bornMass ψ =
      (fourierContinuationInstrument prior next').bornMass ψ := by
  rw [fourierContinuationInstrument_mass, fourierContinuationInstrument_mass]
  congr 1
  exact List.map_congr_left h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_TaggedProbability

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.AxisProbability -/
section Port_AxisProbability

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def selectedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      streamBlockContinuation (call w) prior
        (fun bits => selectedSourceAxis call ws (bits.reverse ++ prior) terminal)

noncomputable def selectedIdealAxis (Q : Point) :
    List OddWindow → List Bool → (List Bool → Instrument) → Instrument
  | [], prior, terminal => terminal prior
  | w :: ws, prior, terminal =>
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).map
        (fun b => InstrumentBranch.seq
          ⟨[], (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))⟩ b)

theorem selectedIdealAxis_cons_mass (Q : Point) (w : OddWindow) (ws : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q (w :: ws) prior terminal).bornMass ψ =
      (fourierContinuationInstrument prior
        (fun bits => selectedIdealAxis Q ws (bits.reverse ++ prior) terminal)).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
  simp only [selectedIdealAxis,Instrument.bornMass,List.map_map,Function.comp_def,
    InstrumentBranch.seq,LinearMap.comp_apply]

/-- All arithmetic records may be summed out, including before an arbitrary selected terminal event. -/
theorem selectedSourceAxis_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal : List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal).bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => rfl
  | cons w ws ih =>
    rw [selectedSourceAxis,streamBlockContinuation_mass (hcall w (by simp)) _ _ _
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ),selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits hbits
    apply ih (fun v hv => hcall v (List.mem_cons_of_mem w hv))
    apply batchedWindowValid_fourierBranch
    · intro v hv
      simpa only [List.mem_reverse] using hv
    · exact actualBatchedWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)


theorem selectedSourceAxis_constant (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (tail : AdaptiveCircuit) :
    selectedSourceAxis call ws prior (fun _ => tail.run) =
      (streamAxis (ws.map call) prior tail).run := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih =>
    simp only [selectedSourceAxis,List.map_cons,streamAxis_cons_run,
      streamBlockContinuation,ih]
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_AxisProbability

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.TwoAxisProbability -/
section Port_TwoAxisProbability

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem selectedIdealAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ws : List OddWindow) (prior : List Bool)
    (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedIdealAxis Q ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  induction ws generalizing prior ψ with
  | nil => exact he prior ψ hψ
  | cons w ws ih =>
    rw [selectedIdealAxis_cons_mass,selectedIdealAxis_cons_mass]
    apply fourierContinuationInstrument_mass_congr
    intro bits _
    apply ih
    apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualBatchedWindowState_supported Q hQ hn w _
        (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ)

theorem selectedSourceAxis_terminal_congr (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (call : OddWindow → AdaptiveCircuit) (ws : List OddWindow)
    (hcall : ∀ w ∈ ws, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (prior : List Bool) (terminal terminal' : List Bool → Instrument)
    (he : ∀ prior ψ, SupportedOn BatchedWindowValid ψ →
      (terminal prior).bornMass ψ = (terminal' prior).bornMass ψ)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    (selectedSourceAxis call ws prior terminal).bornMass ψ =
      (selectedIdealAxis Q ws prior terminal').bornMass ψ := by
  rw [selectedSourceAxis_mass Q hQ hn call ws hcall prior terminal ψ hψ]
  exact selectedIdealAxis_terminal_congr Q hQ hn ws prior terminal terminal' he ψ hψ

noncomputable def selectedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  streamBlockContinuation first List.nil (fun bits =>
    selectedSourceAxis call left bits.reverse (fun lhs =>
      selectedSourceAxis call right List.nil (terminal lhs)))

noncomputable def selectedIdealTwoAxes (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (fourierContinuationInstrument List.nil (fun bits =>
    selectedIdealAxis Q left bits.reverse (fun lhs =>
      selectedIdealAxis Q right List.nil (terminal lhs)))).map
    (fun b => InstrumentBranch.seq
      ⟨List.nil, (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)).comp
        (Quantum.run (streamAddress.map Gate.H))⟩ b)

/-- Exact selected-event probability for both axes, with Fourier history reset between axes. -/
theorem selectedSourceTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (first : AdaptiveCircuit)
    (hfirst : CoherentlyImplementsOn first
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, CoherentlyImplementsOn (call w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid)
    (terminal : List Bool → List Bool → Instrument)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    (selectedSourceTwoAxes first call left right terminal).bornMass ψ =
      (selectedIdealTwoAxes Q left right terminal).bornMass ψ := by
  rw [selectedSourceTwoAxes,streamBlockContinuation_mass hfirst _ _ _
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)]
  have hm : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes,Instrument.bornMass,List.map_map,Function.comp_def,
      InstrumentBranch.seq,LinearMap.comp_apply]
  rw [hm]
  apply fourierContinuationInstrument_mass_congr
  intro bits _
  apply selectedSourceAxis_terminal_congr Q hQ hn call left
    (fun w hw => hcall w (List.mem_append_left _ hw))
  · intro lhs φ hφ
    exact selectedSourceAxis_mass Q hQ hn call right
      (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil (terminal lhs) φ hφ
  · apply batchedWindowValid_fourierBranch
    · intro v hv; simpa only [List.mem_reverse] using hv
    · exact actualFirstWindowState_supported Q _
        (firstWindowInput_prepare _ (fun _ h => h) ψ hψ)



theorem selectedSourceTwoAxes_constant (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (tail : AdaptiveCircuit) :
    selectedSourceTwoAxes first call left right (fun _ _ => tail.run) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run := by
  simp only [selectedSourceTwoAxes,selectedSourceAxis_constant,
    streamAxis_cons_run,streamBlockContinuation,List.append_nil]

theorem actualOddSource_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) :
    CoherentlyImplementsOn (actualOddSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := actualBatchedWindow_coherent Q hQ hn w 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualBatchedWindow_run w 0 Q hQ Fin.elim0] at h
  exact h

theorem actualFirstSource_coherent_input (Q : Point) (hQ : order • Q = 0) :
    CoherentlyImplementsOn (actualFirstSource Q)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  have h := actualFirstWindow_coherent_input Q hQ 0 Fin.elim0
  unfold CoherentlyImplementsOn at h ⊢
  rw [actualFirstWindow_run 0 Q hQ Fin.elim0] at h
  exact h

theorem actualSourcesTwoAxes_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (terminal : List Bool → List Bool → Instrument) :
    (selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right terminal).bornMass
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right terminal).bornMass (ket (zeroBasisState[836 ↦ true])) :=
  selectedSourceTwoAxes_mass Q hQ hn _ (actualFirstSource_coherent_input Q hQ)
    _ left right (fun w _ => actualOddSource_coherent Q hQ hn w) terminal _
    (supportedOn_ket _ _ firstWindowInput_start)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_TwoAxisProbability

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.FixedWord -/
section Port_FixedWord

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The evaluator reads exactly the supplied chronological bits, with its fixed LSB convention. -/
theorem readWord_of_actual_bits (history : List Bool) (positions : List Nat) (bits : List Bool)
    (h : positions.map (fun i => history[i]?) = bits.map some) :
    readWord history positions = some (fourierWordLSB bits) := by
  induction positions generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bits => simp at h
  | cons i positions ih =>
    cases bits with
    | nil => simp at h
    | cons b bits =>
      have hh : history[i]? = some b ∧
          positions.map (fun j => history[j]?) = bits.map some := by
        simpa only [List.map_cons,List.cons.injEq] using h
      simp only [readWord,hh.1,ih bits hh.2,fourierWordLSB]
      cases b <;> rfl

theorem actual_bits_range (before bits after : List Bool) :
    (List.range' before.length bits.length).map
      (fun i => (before ++ bits ++ after)[i]?) = bits.map some := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range'] at hi
    simp only [List.getElem_map,List.getElem_range']
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.one_mul]
    rw [List.getElem?_append_left hi,List.getElem?_eq_getElem hi]

theorem readWord_actual_range (before bits after : List Bool) :
    readWord (before ++ bits ++ after) (List.range' before.length bits.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (actual_bits_range before bits after)


/-- A transcript decomposition records each arithmetic prefix and the next sixteen Fourier bits. -/
inductive AxisTranscript {n : Nat} : List (OuterWindow n) → List Bool → List Bool → Prop
  | nil : AxisTranscript List.nil List.nil List.nil
  | cons (w : OuterWindow n) (ws : List (OuterWindow n)) (a bits rest out : List Bool)
      (ha : a.length = w.count) (hb : bits.length = 16)
      (ht : AxisTranscript ws rest out) :
      AxisTranscript (w :: ws) (a ++ bits ++ rest) (bits ++ out)

theorem AxisTranscript.actual_bits {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    (axisPositions ws before.length).map (fun i => (before ++ history ++ after)[i]?) =
      bits.map some := by
  induction h generalizing before with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    rw [axisPositions,List.map_append,List.map_append]
    have hhead := actual_bits_range (before ++ a) bs (rest ++ after)
    have htail := ih (before ++ a ++ bs)
    simp only [List.length_append,ha,hb,List.append_assoc] at hhead htail
    simp only [List.append_assoc,Nat.add_assoc]
    rw [hhead,htail]

theorem AxisTranscript.readWord {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    ShorECDLP.Challenge.readWord (before ++ history ++ after) (axisPositions ws before.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (h.actual_bits before after)


/-- Transcript blocks are obtained from the actual straight execution, not supplied as an assumption. -/
theorem outerAxis_transcript {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run) :
    ∃ bits, AxisTranscript ws b.history bits := by
  induction ws generalizing start b with
  | nil =>
    simp only [outerAxis,Straight.instantiate,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨[],AxisTranscript.nil⟩
  | cons w ws ih =>
    simp only [outerAxis,castFinish_instantiate] at hb
    obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    obtain ⟨bits,hbits⟩ := ih _ _ h₂ c hc
    have hla : a.history.length = w.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlf : f.history.length = 16 := by
      have h := straight_history_length _ read h₁ f hf
      omega
    refine ⟨f.history ++ bits,?_⟩
    simpa only [InstrumentBranch.seq,List.append_assoc] using
      AxisTranscript.cons w ws a.history f.history c.history bits hla hlf hbits

theorem outerAxis_readWord {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run)
    (suffix : List Bool) :
    ∃ bits, AxisTranscript ws b.history bits ∧
      readWord (List.ofFn history ++ b.history ++ suffix) (axisPositions ws start) =
        some (fourierWordLSB bits) := by
  obtain ⟨bits,h⟩ := outerAxis_transcript wires ws start prior read history b hb
  exact ⟨bits,h,by simpa only [List.length_ofFn] using h.readWord (List.ofFn history) suffix⟩


theorem AxisTranscript.bits_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    bits.length = ws.length * 16 := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,List.length_cons,hb,ih,Nat.add_mul]
    omega

theorem OuterPlan.round_actualWords {n : Nat} (p : OuterPlan n) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round start).instantiate read history).run) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList start) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.run] at hb
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hb
  obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history d hd
  obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
  obtain ⟨left,hl,hlread⟩ := outerAxis_readWord p.wires p.left.toList start List.nil
    read history a ha (f.history ++ c.history ++ suffix)
  obtain ⟨right,hr,hrread⟩ := outerAxis_readWord p.wires p.right.toList _ List.nil
    read h₁ f hf (c.history ++ suffix)
  refine ⟨left,right,?_,?_,?_,?_⟩
  · simpa using hl.bits_length
  · simpa using hr.bits_length
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [InstrumentBranch.seq,List.append_assoc] using hlread
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [he₁,InstrumentBranch.seq,List.append_assoc] using hrread



theorem OuterPlan.repeat_actualWords {n : Nat} (p : OuterPlan n) (count start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.repeat count start).instantiate read history).run)
    (r : Nat) (hr : r < count) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList (start + r*p.stride)) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + r*p.stride + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  induction count generalizing start b r with
  | zero => omega
  | succ count ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate] at hb
    obtain ⟨h₁,a,c,ha,hc,he,rfl⟩ := straight_append_branch _ _ read history b hb
    cases r with
    | zero =>
      simpa only [Nat.zero_mul,Nat.add_zero,InstrumentBranch.seq,List.append_assoc] using
        p.round_actualWords start read history a ha (c.history ++ suffix)
    | succ r =>
      have h := ih (start+p.stride) h₁ c hc r (by omega)
      simpa only [he,InstrumentBranch.seq,List.append_assoc,Nat.succ_mul,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem OuterPlan.entry_actualWords (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) (Q : Secp256k1.Point)
    (b : InstrumentBranch) (hb : b ∈ ((p.entryForStreaming coefficients).instantiate Q).run) (r : Fin streamingRounds) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord b.history (p.positionsForStreaming r).left.toList = some (fourierWordLSB left) ∧
      readWord b.history (p.positionsForStreaming r).right.toList = some (fourierWordLSB right) := by
  simp only [OuterPlan.entryForStreaming,StraightEntry.instantiate,castFinish_instantiate] at hb
  have h := p.repeat_actualWords streamingRounds 0 (readConstant coefficients.get Q) Fin.elim0 b hb r.val r.isLt List.nil
  simpa only [OuterPlan.positionsForStreaming,Vector.toList,List.toList_toArray,List.ofFn_zero,
    List.nil_append,List.append_nil,Nat.zero_add] using h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_FixedWord

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.TaggedAxis -/
section Port_TaggedAxis

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

noncomputable def taggedSourceAxis (call : OddWindow → AdaptiveCircuit) :
    List OddWindow → List Bool → List (List Bool × InstrumentBranch)
  | [], prior => [(prior,⟨[],LinearMap.id⟩)]
  | w :: ws, prior => (streamBlockOutcomes (call w) prior).flatMap (fun a =>
      (taggedSourceAxis call ws (a.1.reverse ++ prior)).map (fun b => (b.1,a.2.seq b.2)))

theorem selectedSourceAxis_tagged (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedSourceAxis call ws prior terminal =
      (taggedSourceAxis call ws prior).flatMap (fun a =>
        (terminal a.1).map a.2.seq) := by
  induction ws generalizing prior with
  | nil =>
    simp only [selectedSourceAxis,taggedSourceAxis,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    have he : (InstrumentBranch.seq ⟨[],LinearMap.id⟩) = (fun b => b) := by
      funext b
      cases b
      simp [InstrumentBranch.seq]
    rw [he,List.map_id']
  | cons w ws ih =>
    simp only [selectedSourceAxis,streamBlockContinuation,taggedSourceAxis,ih,
      List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    apply List.flatMap_congr
    intro b hb
    apply List.map_congr_left
    intro c hc
    cases a with | mk atag a =>
      cases b with | mk btag b =>
        cases a; cases b; cases c
        simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem streamBlockOutcomes_split (call : AdaptiveCircuit) (count : Nat)
    (hcount : ∀ b ∈ call.run, b.history.length = count) (prior : List Bool)
    (tagged : List Bool × InstrumentBranch) (ht : tagged ∈ streamBlockOutcomes call prior) :
    ∃ a : List Bool, a.length = count ∧ tagged.1.length = 16 ∧
      tagged.2.history = a ++ tagged.1 := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp ht
  have hl : bs.length = 16 := by
    simpa only [streamAddress,List.length_range'] using
      (fourierOutcomes_mem streamAddress.length bs).mp hbs
  simp only [AdaptiveCircuit.seq,AdaptiveCircuit.run] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact ⟨b.history,hcount b hb,hl,rfl⟩

theorem taggedSourceAxis_transcript (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (prior : List Bool) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws prior) :
    ∃ bits, AxisTranscript (ws.map actualBatchedWindow) tagged.2.history bits ∧
      tagged.1 = bits.reverse ++ prior := by
  induction ws generalizing prior tagged with
  | nil =>
    simp only [taggedSourceAxis,List.mem_singleton] at ht
    subst tagged
    exact ⟨[],AxisTranscript.nil,rfl⟩
  | cons w ws ih =>
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    obtain ⟨ar,har,hbits,hhist⟩ := streamBlockOutcomes_split (call w) _ (hcount w (by simp)) prior a ha
    obtain ⟨bits,htrans,hprior⟩ := ih (fun v hv => hcount v (List.mem_cons_of_mem w hv)) _ b hb
    refine ⟨a.1 ++ bits,?_,?_⟩
    · simpa only [List.map_cons,InstrumentBranch.seq,hhist,List.append_assoc] using
        AxisTranscript.cons (actualBatchedWindow w) (ws.map actualBatchedWindow)
          ar a.1 b.2.history bits har hbits htrans
    · simpa only [List.reverse_append,List.append_assoc] using hprior

theorem actualOddSource_history_length (Q : Point) (hQ : order • Q = 0) (w : OddWindow)
    (b : InstrumentBranch) (hb : b ∈ (actualOddSource Q w).run) :
    b.history.length = (actualBatchedWindow w).count := by
  have he := actualBatchedWindow_run w 0 Q hQ Fin.elim0
  change _ = (actualOddSource Q w).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length ((actualBatchedWindow w).program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Fixed positions read the same Fourier tag used by selectedSourceAxis, not arithmetic records. -/
theorem taggedSourceAxis_readWord (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis call ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits,htrans,htag⟩ := taggedSourceAxis_transcript call ws hcount List.nil tagged ht
  rw [htag,List.append_nil,List.reverse_reverse]
  exact htrans.readWord before after

theorem actualTaggedAxis_readWord (Q : Point) (hQ : order • Q = 0)
    (ws : List OddWindow) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedSourceAxis (actualOddSource Q) ws List.nil)
    (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (ws.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.reverse) :=
  taggedSourceAxis_readWord _ ws (fun w _ b hb => actualOddSource_history_length Q hQ w b hb)
    tagged ht before after


/-- Event filtering by fixed record positions is exactly Fourier-tag selection. -/
theorem selectedSourceAxis_fixed_filter (call : OddWindow → AdaptiveCircuit)
    (ws : List OddWindow)
    (hcount : ∀ w ∈ ws, ∀ b ∈ (call w).run, b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Bool) :
    selectedSourceAxis call ws List.nil
      (fun tag => if accept (fourierWordLSB tag.reverse) then tail.run else []) =
      (streamAxis (ws.map call) List.nil tail).run.filter
        (fun b => (readWord b.history (axisPositions (ws.map actualBatchedWindow) 0)).any accept) := by
  rw [← selectedSourceAxis_constant call ws List.nil tail]
  rw [selectedSourceAxis_tagged,selectedSourceAxis_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      (readWord (a.2.seq b).history (axisPositions (ws.map actualBatchedWindow) 0)).any accept =
        accept (fourierWordLSB a.1.reverse) := by
    have h := taggedSourceAxis_readWord call ws hcount a ha List.nil b.history
    change (readWord (a.2.history ++ b.history) _).any accept = _
    simpa only [List.nil_append,List.length_nil,Option.any_some] using congrArg (fun x => x.any accept) h
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_TaggedAxis

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.TaggedTwoAxes -/
section Port_TaggedTwoAxes

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] fourierOutcomes streamAddress

theorem AxisTranscript.history_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    history.length = axisCount ws := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,ha,hb,ih,axisCount]

noncomputable def taggedSourceTwoAxes (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (streamBlockOutcomes first List.nil).flatMap (fun a =>
    (taggedSourceAxis call left a.1.reverse).flatMap (fun l =>
      (taggedSourceAxis call right List.nil).map (fun r => ((l.1,r.1),a.2.seq (l.2.seq r.2)))))

theorem selectedSourceTwoAxes_tagged (first : AdaptiveCircuit)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) :
    selectedSourceTwoAxes first call left right terminal =
      (taggedSourceTwoAxes first call left right).flatMap (fun a =>
        (terminal a.1.1 a.1.2).map a.2.seq) := by
  simp only [selectedSourceTwoAxes,streamBlockContinuation,selectedSourceAxis_tagged,
    taggedSourceTwoAxes,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro l hl
  apply List.flatMap_congr
  intro r hr
  apply List.map_congr_left
  intro b hb
  rcases a with ⟨atag,a⟩; rcases l with ⟨lt,l⟩; rcases r with ⟨rt,r⟩
  cases a; cases l; cases r; cases b
  simp only [InstrumentBranch.seq,List.append_assoc,LinearMap.comp_assoc]

theorem taggedSourceTwoAxes_readWords (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tagged : (List Bool × List Bool) × InstrumentBranch)
    (ht : tagged ∈ taggedSourceTwoAxes first call left right) (before after : List Bool) :
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) before.length) =
        some (fourierWordLSB tagged.1.1.reverse) ∧
    readWord (before ++ tagged.2.history ++ after)
      (axisPositions (right.map actualBatchedWindow)
        (before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow))) =
        some (fourierWordLSB tagged.1.2.reverse) := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨l,hl,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
  obtain ⟨ar,har,hbs,hah⟩ := streamBlockOutcomes_split first _ hfirst List.nil a ha
  obtain ⟨lbs,hlt,hltag⟩ := taggedSourceAxis_transcript call left
    (fun w hw => hcall w (List.mem_append_left _ hw)) a.1.reverse l hl
  obtain ⟨rbs,hrt,hrtag⟩ := taggedSourceAxis_transcript call right
    (fun w hw => hcall w (List.mem_append_right _ hw)) List.nil r hr
  have hleft : AxisTranscript (actualFirstWindow :: left.map actualBatchedWindow)
      (a.2.history ++ l.2.history) (a.1 ++ lbs) := by
    rw [hah]
    exact AxisTranscript.cons _ _ ar a.1 l.2.history lbs har hbs hlt
  have hlword := hleft.readWord before (r.2.history ++ after)
  have hrword := hrt.readWord (before ++ a.2.history ++ l.2.history) after
  have hllength := hleft.history_length
  constructor
  · simpa only [InstrumentBranch.seq,List.append_assoc,hltag,← List.reverse_append,
      List.reverse_reverse] using hlword
  · have he : (before ++ a.2.history ++ l.2.history).length =
        before.length + axisCount (actualFirstWindow :: left.map actualBatchedWindow) := by
      simpa only [List.length_append,Nat.add_assoc] using congrArg (before.length + ·) hllength
    rw [he] at hrword
    simpa only [InstrumentBranch.seq,List.append_assoc,hrtag,List.append_nil,
      List.reverse_reverse] using hrword

theorem actualFirstSource_history_length (Q : Point) (hQ : order • Q = 0)
    (b : InstrumentBranch) (hb : b ∈ (actualFirstSource Q).run) :
    b.history.length = actualFirstWindow.count := by
  have he := actualFirstWindow_run 0 Q hQ Fin.elim0
  change _ = (actualFirstSource Q).run at he
  rw [← he] at hb
  simpa only [Nat.zero_add,Nat.sub_zero] using
    straight_history_length (actualFirstWindow.program 0) (readConstant coefficientAt Q) Fin.elim0 b hb


/-- Select a pair of evaluator words, rejecting either missing word. -/
def fixedPairAccept (left right : List Nat) (accept : Nat → Nat → Bool)
    (history : List Bool) : Bool :=
  ((readWord history left).bind (fun lhs => (readWord history right).map (accept lhs))).getD false

theorem selectedSourceTwoAxes_fixed_filter (first : AdaptiveCircuit)
    (hfirst : ∀ b ∈ first.run, b.history.length = actualFirstWindow.count)
    (call : OddWindow → AdaptiveCircuit) (left right : List OddWindow)
    (hcall : ∀ w ∈ left ++ right, ∀ b ∈ (call w).run,
      b.history.length = (actualBatchedWindow w).count)
    (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    selectedSourceTwoAxes first call left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else []) =
      (streamAxis (first :: left.map call) List.nil
        (streamAxis (right.map call) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
          fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
            (axisPositions (right.map actualBatchedWindow)
              (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history) := by
  rw [← selectedSourceTwoAxes_constant first call left right tail]
  rw [selectedSourceTwoAxes_tagged,selectedSourceTwoAxes_tagged,List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
        (axisPositions (right.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept (a.2.seq b).history =
      accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedSourceTwoAxes_readWords first hfirst call left right hcall a ha List.nil b.history
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at h
    simp only [fixedPairAccept,InstrumentBranch.seq,h.1,h.2,Option.bind_some,
      Option.map_some,Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def,hp]
  split <;> simp_all

/-- The same two fixed words drive event selection on the actual source and on its ideal image. -/
theorem actualSources_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (left right : List OddWindow) (tail : AdaptiveCircuit) (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((streamAxis (actualFirstSource Q :: left.map (actualOddSource Q)) List.nil
      (streamAxis (right.map (actualOddSource Q)) List.nil tail)).run.filter (fun (b : InstrumentBranch) =>
        fixedPairAccept (axisPositions (actualFirstWindow :: left.map actualBatchedWindow) 0)
          (axisPositions (right.map actualBatchedWindow)
            (axisCount (actualFirstWindow :: left.map actualBatchedWindow))) accept b.history))
      (ket (zeroBasisState[836 ↦ true])) =
    (selectedIdealTwoAxes Q left right (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then tail.run else [])).bornMass
      (ket (zeroBasisState[836 ↦ true])) := by
  rw [← selectedSourceTwoAxes_fixed_filter (actualFirstSource Q)
    (fun b hb => actualFirstSource_history_length Q hQ b hb) (actualOddSource Q) left right
    (fun w _ b hb => actualOddSource_history_length Q hQ w b hb) tail accept]
  exact actualSourcesTwoAxes_mass Q hQ hn left right _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_TaggedTwoAxes

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.SourceAxis -/
section Port_SourceAxis

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fourierContinue_seq (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (tail : AdaptiveCircuit) :
    (fourierContinue dir ws prior next).seq tail =
      fourierContinue dir ws prior (fun h => (next h).seq tail) := by
  induction ws generalizing prior with
  | nil => rfl
  | cons w ws ih => simp only [fourierContinue,AdaptiveCircuit.seq,ih]

theorem sourceOuterAxis_seq_streamAxis (calls : List AdaptiveCircuit) (prior : List Bool)
    (tail : AdaptiveCircuit) :
    (sourceOuterAxis streamAddress.reverse calls prior).seq tail = streamAxis calls prior tail := by
  induction calls generalizing prior with
  | nil => rfl
  | cons call calls ih =>
    simp only [sourceOuterAxis,streamAxis,List.reverse_reverse,AdaptiveCircuit.seq]
    rw [circuit_seq_assoc,fourierContinue_seq]
    simp only [ih]

theorem sourceOuterRound_streamAxis (left right : List AdaptiveCircuit) (reset : List Wire) :
    sourceOuterRound streamAddress.reverse left right reset =
      AdaptiveCircuit.unitary [.X 836] (streamAxis left List.nil
        (streamAxis right List.nil (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => []))))) := by
  simp only [sourceOuterRound,sourceOuterAxis_seq_streamAxis]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_SourceAxis

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ActualPair -/
section Port_ActualPair

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstWindow actualBatchedWindow actualFirstSource actualOddSource
attribute [local irreducible] streamAddress fourierOutcomes streamAxis sourceOuterRound measureResetWithCorrection batchedResetWires actualRoundSource selectedIdealTwoAxes

def leftOddIndices : List OddWindow := List.ofFn (fun k : Fin 15 => .left ⟨14-k.val,by omega⟩)
def rightOddIndices : List OddWindow := List.ofFn (fun k : Fin 13 => .right ⟨12-k.val,by omega⟩)

theorem actualLeftSources_indices (Q : Point) : actualLeftSources Q =
    actualFirstSource Q :: leftOddIndices.map (actualOddSource Q) := by
  simp only [actualLeftSources,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightSources_indices (Q : Point) : actualRightSources Q =
    rightOddIndices.map (actualOddSource Q) := by
  simp only [actualRightSources,rightOddIndices,List.map_ofFn,Function.comp_def]
theorem actualLeftWindows_indices : actualLeftWindows =
    actualFirstWindow :: leftOddIndices.map actualBatchedWindow := by
  simp only [actualLeftWindows,leftOddIndices,List.map_ofFn,Function.comp_def]
theorem actualRightWindows_indices : actualRightWindows =
    rightOddIndices.map actualBatchedWindow := by
  simp only [actualRightWindows,rightOddIndices,List.map_ofFn,Function.comp_def]

theorem unitary_history_filter_mass (g : Circuit) (next : AdaptiveCircuit)
    (accept : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((AdaptiveCircuit.unitary g next).run.filter (fun b => accept b.history)) ψ =
      Instrument.bornMass (next.run.filter (fun b => accept b.history)) (Quantum.run g ψ) := by
  simp only [AdaptiveCircuit.run,List.filter_map,Instrument.bornMass,List.map_map,Function.comp_def]
  rfl

def actualRoundFixedAccept (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  fixedPairAccept (batchedOuterPlan.positions ⟨0,by decide⟩).left.toList
    (batchedOuterPlan.positions ⟨0,by decide⟩).right.toList accept history

private theorem port_ActualPair_positions_zero {n : Nat} (p : OuterPlan n) :
    (p.positions ⟨0,by decide⟩).left.toList = axisPositions p.left.toList 0 ∧
    (p.positions ⟨0,by decide⟩).right.toList = axisPositions p.right.toList (axisCount p.left.toList) := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,Nat.zero_add]
  trivial

private theorem port_ActualPair_actual_left : batchedOuterPlan.left.toList = actualLeftWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]
private theorem port_ActualPair_actual_right : batchedOuterPlan.right.toList = actualRightWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem actualRoundFixedAccept_positions (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history =
      fixedPairAccept (axisPositions (actualFirstWindow :: leftOddIndices.map actualBatchedWindow) 0)
        (axisPositions (rightOddIndices.map actualBatchedWindow)
          (axisCount (actualFirstWindow :: leftOddIndices.map actualBatchedWindow))) accept history := by
  rw [actualRoundFixedAccept,(port_ActualPair_positions_zero batchedOuterPlan).1,(port_ActualPair_positions_zero batchedOuterPlan).2,
    port_ActualPair_actual_left,port_ActualPair_actual_right,actualLeftWindows_indices,actualRightWindows_indices]

/-- Fixed positions of the actual layout select the same event in the actual round and ideal two-axis model. -/
theorem actualRoundSource_fixedPair_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept accept b.history)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,unitary_history_filter_mass]
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  rw [hx,actualLeftSources_indices,actualRightSources_indices]
  simp only [actualRoundFixedAccept_positions]
  exact actualSources_fixedPair_mass Q hQ hn leftOddIndices rightOddIndices _ accept


noncomputable def wrappedPairAccept (params : DecoderParams) (Q : Point) (left right : Nat) : Bool := by
  classical
  exact ((fixedCandidates params left right).toList.find? (fun c => decide (c.val • G = Q))).isSome

def actualSingleRoundLayout : DecodeLayout :=
  ⟨.wrappedShift,legacyDecoderParams,[batchedOuterPlan.positions ⟨0,by decide⟩],by decide⟩

theorem wrappedTrial_verified_isSome (params : DecoderParams) (Q : Point)
    (positions : TrialPositions params) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,[positions],by simp⟩ Q history).isSome =
      fixedPairAccept positions.left.toList positions.right.toList (wrappedPairAccept params Q) history := by
  classical
  simp only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    decodeTrial,trialCandidates,fixedPairAccept]
  cases hl : readWord history positions.left.toList <;>
    cases hr : readWord history positions.right.toList <;>
    simp only [Option.bind_none,Option.bind_some,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.find?_nil,Option.isSome_none,fixedCandidates_take]
  rfl

theorem actualSingleRound_verified_isSome (Q : Point) (history : List Bool) :
    (verifiedCandidate actualSingleRoundLayout Q history).isSome =
      actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) history :=
  wrappedTrial_verified_isSome _ Q _ history

/-- The compiled round's acceptance is evaluated by the protected verifiedCandidate function. -/
theorem actualCompiledRound_verified_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Instrument.bornMass
      (((batchedOuterPlan.round 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate actualSingleRoundLayout Q b.history).isSome)) (ket zeroBasisState) =
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if wrappedPairAccept legacyDecoderParams Q (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) := by
  rw [batchedOuterPlan_round_run Q hQ 0 Fin.elim0]
  simp only [actualSingleRound_verified_isSome]
  exact actualRoundSource_fixedPair_mass Q hQ hn _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ActualPair

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.LookupSlots -/
section Port_LookupSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every fixed gate slot counts, including disabled constant/record controls. -/
def lookupSlots {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + lookupSlots ops
  | .erase _ _ _ :: ops => 3 + lookupSlots ops

theorem recordGates_slots {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e) :
    (recordGates i gs next).gateSlots = gs.length + next.gateSlots := by
  induction gs <;> simp_all [recordGates,Straight.gateSlots,Nat.add_assoc,Nat.add_left_comm]

theorem lookupProgram_slots (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n ops start).gateSlots = lookupSlots ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [lookupProgram,Straight.gateSlots_append,gateProgram_slots,ih,lookupSlots]
    | erase a b t =>
      simp only [lookupProgram,castFinish_gateSlots,Straight.gateSlots_append,andEraseProgram,
        Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil,ih,lookupSlots]

theorem lookupSlots_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupSlots (xs++ys) = lookupSlots xs + lookupSlots ys := by
  induction xs with
  | nil => simp [lookupSlots]
  | cons x xs ih => cases x <;> simp_all [lookupSlots,Nat.add_assoc]

theorem unaryLookupOps_slots_le {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (bound : Nat) (hleaf : ∀ l q, (leaf l q).length ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    lookupSlots (unaryLookupOps leaf tree q anc) ≤
      bound * (tree.internalNodes+1) + 10*tree.internalNodes := by
  induction tree generalizing q anc with
  | leaf l => simpa [unaryLookupOps,lookupSlots,UnaryActionTree.internalNodes] using hleaf l q
  | node bit zero one ihz iho =>
    cases anc with
    | nil => simp [unaryLookupOps,lookupSlots]
    | cons path rest =>
      have hz := ihz path rest
      have ho := iho path rest
      simp only [unaryLookupOps,lookupSlots_append,lookupSlots,ordinaryOp,List.length_map,
        computeZeroAnd,List.length_cons,List.length_nil,UnaryActionTree.internalNodes,
        Nat.mul_add,Nat.mul_one] at *
      omega

theorem pointLeaf_slots {n : Nat} (row : Fin n) (q : Wire) : (pointLeaf row q).length ≤ 513 := by
  simp only [pointLeaf,lookupLeafGates,List.length_map,List.length_zip]
  apply Nat.min_le_left _ _ |>.trans
  simp only [pointRefs,List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
  decide

theorem actualFirstWindow_slots (start : Nat) :
    (actualFirstWindow.program start).gateSlots ≤ 34275318 := by
  have h := unaryLookupOps_slots_le
    (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
    513 (fun _ q => pointLeaf_slots _ q)
    (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)
  have hn := tableAddressTree_nodes (List.range' 855 16) 0 1
  change (tableAddressTree (List.range' 855 16) 0 1).internalNodes+1 = 65536 at hn
  simpa only [actualFirstWindow,reindexStraight_gateSlots,firstLookupProgram,
    castFinish_gateSlots,lookupProgram_slots,firstLookupOps] using
    (show lookupSlots (unaryLookupOps (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
      (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)) ≤ 34275318 by omega)

/-- For a unitary list the five primitive counters partition its actual gates. -/
theorem circuit_length_primitive (gs : Circuit) :
    gs.length = (primitiveResources (.unitary gs .done)).x +
      (primitiveResources (.unitary gs .done)).h +
      (primitiveResources (.unitary gs .done)).cnot +
      (primitiveResources (.unitary gs .done)).toffoli +
      (primitiveResources (.unitary gs .done)).phase := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost] <;> omega

theorem zeroBitCount_bound (value bit width : Nat) : zeroBitCount value bit width ≤ width := by
  induction width generalizing bit with
  | zero => rfl
  | succ width ih =>
    simp only [zeroBitCount]
    have h := ih (bit+1)
    split <;> omega

theorem registerEqualCircuit_length_le (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire)
    (hl : cells.length = 513) (hs : 511 ≤ scratch.length) :
    (registerEqualCircuit cells flag scratch).length ≤ 3075 := by
  have hx : (xorWordCircuit cells).length = cells.length := by
    simp only [xorWordCircuit,List.length_map]
  have hc := computeEqConst_primitive (cells.map Prod.snd) 0 flag scratch
    (by simpa only [List.length_map,hl] using hs)
  have hlen := circuit_length_primitive (computeEqConst (cells.map Prod.snd) 0 flag scratch)
  rw [hc] at hlen
  simp only [List.length_map,hl] at hlen
  have hz := zeroBitCount_bound 0 0 513
  simp only [registerEqualCircuit,List.length_append,hx,hl]
  norm_num only [mcxVChainCnotCost,mcxVChainToffoliCost] at hlen
  simp only [ite_false] at hlen
  omega

theorem batchOpCircuit_length_le (base : Wire) (source : Fin 4) (target : Fin 6) :
    (batchOpCircuit base source target).length ≤ 13326 := by
  have he (a t : Fin 513 → Wire) :
      (registerEqualCircuit (equalityCells a t) (batchFlag base) (batchScratch base)).length ≤ 3075 :=
    registerEqualCircuit_length_le _ _ _ (by simp only [equalityCells,List.length_ofFn]) (by simp only [batchScratch,List.length_ofFn]; decide)
  unfold batchOpCircuit endpointTranspositionCircuit endpointTests
  simp only [List.length_append,endpointWordCircuit_length,endpointUpdateCells,List.length_ofFn]
  have ha := he (batchWord base ⟨source.val,by omega⟩) (batchWord base target)
  have hb := he (batchWord base 4) (batchWord base target)
  omega

theorem endpointSelectGates_length_le {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates q ports).length ≤ ports.length := by
  induction ports with
  | nil => rfl
  | cons port ports ih =>
    rcases port with ⟨w,tag⟩
    cases tag with
    | inl b =>
      cases b
      · simp_all [endpointSelectGates,endpointSelectGate]; omega
      · simp_all [endpointSelectGates,endpointSelectGate]
    | inr r => simp_all [endpointSelectGates,endpointSelectGate]

theorem batchLeaf_length_le {n : Nat} (row : Fin n) (base q : Wire) (selection : List (Fin 8 × Fin 5)) :
    (batchLeaf row base q selection).length ≤ 514 * selection.length := by
  have hp : (batchPorts row base selection).length = 513 * selection.length := by
    induction selection with
    | nil => simp only [batchPorts,List.flatMap_nil,List.length_nil,Nat.mul_zero]
    | cons x xs ih =>
      simp only [batchPorts,List.flatMap_cons,List.length_append,List.length_ofFn] at ih ⊢
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
  have he := endpointSelectGates_length_le q (batchPorts row base selection)
  have ht : (batchTags base selection).length ≤ selection.length := by
    simpa only [batchTags,List.length_map] using List.length_filter_le (fun p => endpointTagMask p.1 512) selection
  simp only [batchLeaf,List.length_append,List.length_map]
  omega

def batchSlotBound (nodes : Nat) : List BatchOp → Nat
  | [] => 0
  | .query _ _ :: ops => 2570*(nodes+1)+10*nodes+batchSlotBound nodes ops
  | .swap _ _ :: ops => 13326+batchSlotBound nodes ops

theorem batchOps_slots_le {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (q : Wire) (paths : List Wire) (ops : List BatchOp) :
    lookupSlots (batchOps rows base tree q paths ops) ≤ batchSlotBound tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query sources target =>
      have hl (l : Nat) (control : Wire) :
          (batchLeaf (rows l) base control (batchSelection sources target)).length ≤ 2570 := by
        have h := batchLeaf_length_le (rows l) base control (batchSelection sources target)
        have hs : (batchSelection sources target).length ≤ 5 := by
          cases sources <;> simp only [batchSelection,Bool.false_eq_true,ite_false,ite_true,
            List.length_append,List.length_cons,List.length_nil] <;> decide
        omega
      have h := unaryLookupOps_slots_le _ 2570 hl tree q paths
      simp only [batchOps,lookupSlots_append,batchSlotBound]
      omega
    | swap source target =>
      have h := batchOpCircuit_length_le base source target
      simp only [batchOps,lookupSlots,ordinaryOp,List.length_map,batchSlotBound]
      omega

theorem relabelStraight_slots {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    (relabelStraight e p).gateSlots = p.gateSlots := by
  induction p <;> simp_all only [relabelStraight,Straight.gateSlots]

theorem batchSlotBound_schedule (nodes : Nat) :
    batchSlotBound nodes batchSchedule = 14*(2570*(nodes+1)+10*nodes)+16*13326 := by
  simp only [batchSchedule,batchSlotBound]
  omega

theorem placedBatchProgram_slots (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).2.gateSlots ≤ 1183793236 := by
  simp only [placedBatchProgram,relabelCompiled,relabelStraight_slots,batchedEndpointProgram,
    lookupProgram_slots]
  have h := batchOps_slots_le (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath batchSchedule
  rw [batchSlotBound_schedule] at h
  have hn := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at hn
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_LookupSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ArithmeticSlots -/
section Port_ArithmeticSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def nonCarryCost : Gate → Nat
  | .CX _ _ | .CCX _ _ _ => 0
  | _ => 1

theorem circuit_length_carry (gs : Circuit) :
    gs.length = eeaCnotCount gs + eeaToffoliCount gs + (gs.map nonCarryCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [eeaCnotCount,eeaToffoliCount,nonCarryCost] <;> omega

theorem carryXor_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (controlledConstCarryXor input dirty constant q c).length ≤ 9*input.length := by
  have hw (bs : List Bool) : constantBitWeight bs ≤ bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b <;> simp only [constantBitWeight,List.map_cons,List.sum_cons,List.length_cons,
        Bool.toNat_false,Bool.toNat_true] at ih ⊢ <;> omega
  cases input with
  | nil => simp [controlledConstCarryXor]
  | cons a input =>
    cases constant with
    | nil => simp at hk
    | cons k constant =>
      have h := controlledConstCarryXor_counts a input dirty k constant q c (by simpa using hk.symm) hd
      have hz := controlledConstCarryXor_cost_zero nonCarryCost (by intros; rfl) (by intros; rfl)
        (a::input) dirty (k::constant) q c
      have hwc := hw constant
      rw [circuit_length_carry,h.2.1,h.2.2.1,hz]
      have hb : k.toNat ≤ 1 := by cases k <;> decide
      simp only [List.length_cons] at hk ⊢
      omega

theorem gidneyAddCleanup_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length+1) (hk : constant.length=input.length) :
    (gidneyAddCleanup input dirty constant q c).length ≤ 11*input.length := by
  have h := carryXor_length_le (input.take dirty.length) dirty (constant.take dirty.length) q c
    (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
  simp only [gidneyAddCleanup,gidneyFlipWord,List.length_append,List.length_map]
  simp only [List.length_take] at h
  omega

theorem deferredCorrectionSlots_le (targets cleanup prior : Nat) (cells : List (Circuit × Wire)) :
    deferredCorrectionSlots targets cleanup prior cells ≤
      (cells.map (fun c => c.1.length)).sum + 6*targets + cleanup := by
  induction cells generalizing prior with
  | nil => simp only [deferredCorrectionSlots,List.map_nil,List.sum_nil]; omega
  | cons c cells ih =>
    rcases c with ⟨gs,w⟩
    simp only [deferredCorrectionSlots,List.map_cons,List.sum_cons]
    have h := ih (prior+1)
    omega

theorem gidneyCarryCells_slots_le (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length+1) (hk : constant.length=input.length) :
    ((gidneyCarryCells q current spare ancilla input dirty constant).map (fun c => c.1.length)).sum ≤
      9*input.length := by
  induction input generalizing current spare dirty constant with
  | nil => simp at hd
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases input with
      | nil =>
        have hd' : dirty=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        have hk' : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        subst dirty; subst ks
        cases k <;> simp [gidneyCarryCells]
      | cons b bs =>
        cases dirty with
        | nil => simp at hd
        | cons d ds =>
          have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
          simp only [gidneyCarryCells,List.map_cons,List.sum_cons,List.length_cons]
          have hc : (gidneyAddCarryCell q current spare ancilla a d k).length ≤ 9 := by
            cases k <;> simp [gidneyAddCarryCell]
          simp only [List.length_cons] at h
          omega
theorem gidneyNontrivialProgram_slots_le (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length=ds.length+1) (hk : ks.length=as.length) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).gateSlots ≤
      26*(as.length+1) := by
  have ht := gidneyCarryCells_slots_le q spare carry ancilla as ds ks hd hk
  have hc := gidneyAddCleanup_length_le (a::as) (d::ds) (k::ks) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf : (gidneyAddCarryCell q carry spare ancilla a d k).length ≤ 9 := by
    cases k <;> simp [gidneyAddCarryCell]
  have hb := deferredCorrectionSlots_le (d::ds).length
    (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry).length 0
    (gidneyCarryCells q spare carry ancilla as ds ks)
  simp only [gidneyNontrivialProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem gidneyProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1)
    (hk : constant.length=input.length) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.gateSlots ≤ 26*input.length := by
  by_cases hz : constant.all (fun k => !k) = true
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = ⟨0,.done⟩ by simp only [gidneyProgram,hz,ite_true]]; exact Nat.zero_le _
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = _ by exact if_neg hz]
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          subst as; subst ks
          cases k <;> simp [literalProgram_slots]
        | cons d ds =>
          have h := gidneyNontrivialProgram_slots_le n start a d q carry spare ancilla as ds k ks
            (by simpa using hd) (by simpa using hk)
          cases as with
          | nil => simp at hd
          | cons b bs => exact h

theorem compareCarryCell_length_le (q c r t a d f : Wire) (k last : Bool) :
    (gidneyCompareCarryCell q c r t a d f k last).length ≤ 10 := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell]

theorem compareCarryCells_slots_le (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    ((compareCarryCells q current spare ancilla flag input dirty constant).map (fun c => c.1.length)).sum ≤
      10*input.length := by
  induction input generalizing current spare dirty constant with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty; subst constant
    rfl
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil => simp at hd
      | cons d ds =>
        have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
        have hc := compareCarryCell_length_le q current spare ancilla a d flag k input.isEmpty
        simp only [compareCarryCells,List.map_cons,List.sum_cons,List.length_cons]
        omega

theorem compareCarryProgram_slots_le (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).gateSlots ≤
      25*(input.length+1) := by
  have ht := compareCarryCells_slots_le q spare carry ancilla flag input dirty constant hd hk
  have hc := carryXor_length_le (a::input) (d::dirty) (k::constant) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf := compareCarryCell_length_le q carry spare ancilla a d flag k input.isEmpty
  have hb := deferredCorrectionSlots_le (d::dirty).length
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry).length 0
    (compareCarryCells q spare carry ancilla flag input dirty constant)
  simp only [compareCarryProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem compareCoreProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hk : constant.length=input.length) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.gateSlots ≤ 25*input.length := by
  cases input with
  | nil => simp [compareCoreProgram,Straight.gateSlots]
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_slots_le n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk)

theorem compareGEProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.gateSlots ≤ 25*input.length+1 := by
  by_cases hz : threshold=0
  · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,literalProgram [.CX q flag]⟩ by exact if_pos hz]
    simp only [literalProgram_slots,List.length_cons,List.length_nil]; omega
  · by_cases hh : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,.done⟩ by simp only [compareGEProgram, hz,ite_false,hh,ite_true]]
      exact Nat.zero_le _
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = _ by exact if_neg hz]
      rw [if_neg hh]
      have h := compareCoreProgram_slots_le n start input dirty
        ((List.range input.length).map (Nat.testBit (2^input.length-threshold))) q carry spare ancilla flag hd
        (by simp only [List.length_map,List.length_range])
      omega

theorem appendCompiled_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    (appendCompiled p q).2.gateSlots = p.2.gateSlots+q.2.gateSlots := by
  simp only [appendCompiled,castFinish_gateSlots,Straight.gateSlots_append]

theorem prependCompiled_slots {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (prependCompiled gs p).2.gateSlots = gs.length+p.2.gateSlots := by
  simp only [prependCompiled,Straight.gateSlots_append,literalProgram_slots]

attribute [local irreducible] compareGEProgram gidneyProgram

theorem modularNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+2 := by
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have ht (s : Nat) := compareGEProgram_slots_le n s target dirty 1 q c r t f hd
  have hi (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t htake
    (by simp only [List.length_map,List.length_range])
  have ha (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1)) modulus f c r t htake hk
  simp only [modularNegateProgram,appendCompiled_slots,prependCompiled_slots]
  have hc : (controlledComplement target q).length=target.length := by
    simp only [controlledComplement,List.length_map]
  rw [hc]
  grind only

theorem negativeNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+4 := by
  have h := modularNegateProgram_slots_le n start target dirty modulus q c r t f hd hk hpos
  simp only [negativeNegateProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,
    List.length_cons,List.length_nil]
  omega

theorem yNegateProgram_slots_le (start : Nat) : (yNegateProgram start).2.gateSlots ≤ 26372 := by
  have h := negativeNegateProgram_slots_le 32768 start (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
    (by simp only [List.length_range']) (by rw [constantBits_length,List.length_range']) (by simp only [List.length_range']; decide)
  change (yNegateProgram start).2.gateSlots ≤ _ at h
  simpa only [List.length_range'] using h

theorem uncontrolledCompareProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.gateSlots ≤ 25*input.length+1 := by
  simp only [uncontrolledCompareProgram,constantStraight_slots]
  exact compareGEProgram_slots_le n start input dirty threshold _ c r t f hd

theorem controlledAddCarry_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledAddCarry bs as q c f).length=1793 := by
  rw [circuit_length_primitive,controlledAddCarry256_primitive _ _ _ _ _ hb ha .done]
  rfl

theorem controlledCompareLT_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledCompareLT bs as q c f).length=2053 := by
  rw [circuit_length_primitive,controlledCompareLT256_primitive _ _ _ _ _ hb ha .done]
  rfl

attribute [local irreducible] uncontrolledCompareProgram

theorem modularAddProgram_slots256 (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    (modularAddProgram n start input acc correction p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) correction f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularAddProgram,appendCompiled_slots,Straight.gateSlots_append,literalProgram_slots,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem circuit_adjoint_length (gs : Circuit) : gs.adjoint.length=gs.length := by
  simp only [Circuit.adjoint,List.length_map,List.length_reverse]

theorem modularSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    (modularSubProgram n start input acc bits p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) bits f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularSubProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
    controlledSubCarry,circuit_adjoint_length,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem doublingShift_length256 (acc : List Wire) (f : Wire) (ha : acc.length=256) :
    (doublingShift acc f).length=767 := by
  rw [circuit_length_primitive,doublingShift256_primitive _ _ ha .done]
  rfl

theorem modularDoubleProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularDoubleProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularDoubleProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,hb]
    simp only [ha] at ht hg
    grind only

theorem modularHalveProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularHalveProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularHalveProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,circuit_adjoint_length,hb]
    simp only [ha] at ht hg
    grind only

theorem compiledIf_slots {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    (if b then p else q).2.gateSlots = if b then p.2.gateSlots else q.2.gateSlots := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := modularAddProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem hornerInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerInverseProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := modularSubProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareAddProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareAddProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularAddProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareAddProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem squareSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareSubProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularSubProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareSubProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

attribute [local irreducible] squareAddProgram squareSubProgram
theorem squareProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := squareAddProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareInverseProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := squareSubProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_slots256 (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256)
    (hk : correction.length=256) (hm : modulus.length=256) :
    (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2.gateSlots ≤ 15750663 := by
  have hs (s : Nat) := squareProgram_slots256 n s y y acc correction p copied c r t f hy ha hk
  have hu (s : Nat) := squareInverseProgram_slots256 n s y y acc modulus p copied c r t f hy ha hm
  have hb (s : Nat) := modularSubProgram_slots256 n s acc x modulus p q copied f r c ha hx hm
  simp only [squareSubtractProgram,appendCompiled_slots]
  simp only [hy] at hs hu
  grind only

theorem fieldLeaf_slots {n : Nat} (row : Fin n) (field : PointField) (q : Wire) :
    (fieldLeaf row field q).length=256 := by
  simp only [fieldLeaf,lookupLeafGates,List.length_map,List.length_zip,fieldRefs,List.length_ofFn,List.length_range']
  rfl

theorem fieldLoadProgram_slots (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).gateSlots ≤ 8716278 := by
  simp only [fieldLoadProgram,castFinish_gateSlots,lookupProgram_slots,fieldLoadOps]
  have h := unaryLookupOps_slots_le
    (fun l q => fieldLeaf (⟨l%32768,Nat.mod_lt _ (by decide)⟩ : Fin 32768) field q)
    256 (fun l q => (fieldLeaf_slots _ field q).le)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath
  have hn := tableAddressTree_nodes pointLookupAddress 0 1
  change (tableAddressTree pointLookupAddress 0 1).internalNodes + 1 = 32768 at hn
  omega

theorem fieldLookupAddProgram_slots (field : PointField) (acc : List Wire) (start : Nat)
    (ha : acc.length=256) : (fieldLookupAddProgram field acc start).2.gateSlots ≤ 17449459 := by
  have h (s : Nat) := fieldLoadProgram_slots field s
  have ha' (s : Nat) := modularAddProgram_slots256 32768 s (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
    (by simp only [List.length_range']) ha (by simp [secp256k1ReductionConstantBits])
  simp only [fieldLookupAddProgram,appendCompiled_slots]
  grind only

theorem signedFieldProgram_slots (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.gateSlots ≤ 17502203 := by
  have hy (s : Nat) := yNegateProgram_slots_le s
  have hf (s : Nat) := fieldLookupAddProgram_slots field (List.range' 580 256) s (by simp only [List.length_range'])
  simp only [signedFieldProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ArithmeticSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.DecoderSlots -/
section Port_DecoderSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (andEraseProgram n s a b w).gateSlots=3 := by
  simp only [andEraseProgram,Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil]

theorem vchainTailProgram_slots (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    (vchainTailProgram n controls acc target scratch start).2.gateSlots ≤ 4*controls.length := by
  induction controls generalizing acc scratch start with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp only [vchainTailProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons c' cs =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons work scratch =>
        have h := ih work scratch start
        simp only [vchainTailProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
          List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem vchainProgram_slots (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (vchainProgram n start controls target scratch).2.gateSlots ≤ 4*controls.length+1 := by
  cases controls with
  | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
  | cons a rest =>
    cases rest with
    | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons b bs =>
      have h := vchainTailProgram_slots n (a::bs) b target scratch start
      change (vchainTailProgram n (a::bs) b target scratch start).2.gateSlots ≤ _
      simp only [List.length_cons] at h ⊢
      omega

theorem zeroEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (zeroEraseProgram n s a b w).2.gateSlots=5 := by
  simp only [zeroEraseProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
    literalProgram_slots,List.length_cons,List.length_nil]

theorem unaryProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l q s, (leaf l q s).2.gateSlots ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (start : Nat) :
    (unaryProgram n order leaf tree q paths start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+10*tree.internalNodes := by
  induction tree generalizing q paths start with
  | leaf l =>
    rw [unaryProgram]
    simpa only [UnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l q start
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact Nat.zero_le _
    | cons path rest =>
      have hz (s : Nat) := ihz path rest s
      have ho (s : Nat) := iho path rest s
      rw [unaryProgram]
      cases order <;>
        simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
          prependCompiled_slots,appendCompiled_slots,zeroEraseProgram_slots,computeZeroAnd,
          List.length_cons,List.length_nil,UnaryActionTree.internalNodes]
      all_goals grind only

theorem zeroMaskFrom_length_le (register : List Wire) (v k : Nat) :
    (zeroMaskFrom register v k).length ≤ register.length := by
  induction register generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [zeroMaskFrom,List.length_append,List.length_cons]
    have h := ih (k+1)
    split <;> simp only [List.length_cons,List.length_nil] <;> omega

theorem equalityProgram_slots (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) :
    (equalityProgram n start register value flag scratch).2.gateSlots ≤ 6*register.length+1 := by
  have hb := vchainProgram_slots n start register flag scratch
  have hm := zeroMaskFrom_length_le register value 0
  simp only [equalityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,zeroMask]
  omega

theorem toggleEqualityProgram_slots (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.gateSlots ≤ 12*register.length+3 := by
  have he (s : Nat) := equalityProgram_slots n s register value flag scratch
  simp only [toggleEqualityProgram,appendCompiled_slots,prependCompiled_slots,List.length_cons,List.length_nil]
  grind only

theorem rippleMajProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleMajInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajInvProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaInvProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem dualEraseProgram_slots (n s : Nat) (a i x b j y : Wire) :
    (dualEraseProgram n s a i x b j y).2.gateSlots=10 := by
  simp only [dualEraseProgram,appendCompiled_slots,zeroEraseProgram_slots]

theorem dualProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l a b s, (leaf l a b s).2.gateSlots ≤ bound)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    (dualProgram n order leaf tree a b xs ys start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+20*tree.internalNodes := by
  induction tree generalizing a b xs ys start with
  | leaf l =>
    rw [dualProgram]
    simpa only [DualUnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil =>
      rw [dualProgram]
      · exact Nat.zero_le _
      · simp
    | cons x xs =>
      cases ys with
      | nil =>
        rw [dualProgram]
        · exact Nat.zero_le _
        · simp
      | cons y ys =>
        have hz (s : Nat) := ihz x y xs ys s
        have ho (s : Nat) := iho x y xs ys s
        rw [dualProgram]
        cases order <;>
          simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
            prependCompiled_slots,appendCompiled_slots,dualEraseProgram_slots,computeZeroAnd,
            List.length_cons,List.length_nil,DualUnaryActionTree.internalNodes]
        all_goals grind only

theorem rippleFirstProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleMajProgram_slots n start control target addend carry scratch
  · exact rippleUmaInvProgram_slots n start control target addend carry scratch

theorem rippleSecondProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleUmaProgram_slots n start control target addend carry scratch
  · exact rippleMajInvProgram_slots n start control target addend carry scratch

theorem endpointLeafToggle_length_le (topSpecial : Bool) (label : Nat) (endpoint control acc : Wire) :
    (endpointLeafToggle topSpecial label endpoint control acc).length ≤ 3 := by
  unfold endpointLeafToggle
  split <;> simp only [List.length_cons,List.length_nil] <;> decide

theorem intervalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry scratch
  simp only [intervalFirstProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem intervalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry scratch
  simp only [intervalSecondProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem topFirstProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry work
  simp only [topFirstProgram,appendCompiled_slots]
  grind only

theorem topSecondProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry work
  simp only [topSecondProgram,appendCompiled_slots]
  grind only

theorem traversalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalFirstProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalFirstProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem traversalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalSecondProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalSecondProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem intervalTopFirstProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopFirstProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopFirstProgram,compiledIf_slots]
  split
  · exact topFirstProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem intervalTopSecondProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopSecondProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopSecondProgram,compiledIf_slots]
  split
  · exact topSecondProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem prepareIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (prepareIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,prepareIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem restoreIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (restoreIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,restoreIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem intervalSignUpdate_length_le (r : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    (intervalSignUpdate r k K signUpdate).length ≤ 1 := by
  cases signUpdate <;> simp only [intervalSignUpdate,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide

theorem intervalProgram_slots9 (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hw : 9≤r.endpointScratch.length) :
    (intervalProgram n start r width k K mode signUpdate target).2.gateSlots ≤
      84*(intervalTree r k K).internalNodes+1273 := by
  have hp := prepareIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hr := restoreIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hsg := intervalSignUpdate_length_le r k K signUpdate
  have ht1 (s : Nat) := intervalTopFirstProgram_slots n s r k K mode target
  have ht2 (s : Nat) := intervalTopSecondProgram_slots n s r k K mode target
  have hf (s : Nat) := traversalFirstProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  have hb (s : Nat) := traversalSecondProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  simp only [hs,hq] at ht1 ht2
  simp only [intervalProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_DecoderSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEACellSlots -/
section Port_EEACellSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem sequenceProgram_slots_le (n : Nat) (ps : List (FixedSegment n)) (bounds : List Nat)
    (h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound) ps bounds) (start : Nat) :
    (sequenceProgram n ps start).2.gateSlots ≤ bounds.sum := by
  induction h generalizing start with
  | nil => exact Nat.zero_le _
  | cons hp hs ih =>
    rw [sequenceProgram,appendCompiled_slots]
    simp only [List.sum_cons]
    exact Nat.add_le_add (hp start) (ih _)

theorem coefficientFirstProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientFirstProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleFirstProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientFirstProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientSecondProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientSecondProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleSecondProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientSecondProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientProgram n start r k K mode signUpdate target).2.gateSlots ≤
      54*(coefficientPrefixTree r k K).internalNodes+37 := by
  have hf (s : Nat) := unaryProgram_slots_le n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientFirstProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hb (s : Nat) := unaryProgram_slots_le n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientSecondProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hs : (coefficientPrefixSignCircuit r k K signUpdate).length ≤ 1 := by
    cases signUpdate <;> simp only [coefficientPrefixSignCircuit,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide
  simp only [coefficientProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  grind only
theorem phaseSegments_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit) :
    (sequenceProgram n (phaseSegments n r shift core) start).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+18+core.length := by
  let inner := r.withShiftEpoch shift
  let a := 4*inner.lengthQ.length+1
  let b := 4*inner.lengthRPrime.length+1
  let c := 4*inner.lengthS.length+1
  have h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound)
      (phaseSegments n r shift core) ([a,b,1,c,1,core.length,1,c,1,b,a] : List Nat) := by
    unfold phaseSegments
    repeat' apply List.Forall₂.cons
    all_goals first | exact List.Forall₂.nil | intro cursor
    all_goals first | exact vchainProgram_slots n cursor _ _ _ | (simp only [literalProgram_slots,List.length_cons,List.length_nil]; rfl)
  have hb := sequenceProgram_slots_le n _ _ h start
  simp only [List.sum_cons,List.sum_nil,a,b,c,inner,PhaseUpdateRegisters.withShiftEpoch,
    List.length_append,List.length_cons,List.length_nil] at hb
  omega

theorem phaseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseCoreGates (r.withShiftEpoch shift))
  simp only [phaseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem phaseInverseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseInverseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseInverseCoreGates (r.withShiftEpoch shift))
  simp only [phaseInverseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem zeroCellProgram_slots (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    (zeroCellProgram n start base r bit guard target temporary).2.gateSlots ≤ 7 := by
  cases base <;> simp only [zeroCellProgram,prependCompiled_slots,andEraseProgram_slots,measuredZeroPrefix,
    Bool.false_eq_true,ite_false,ite_true,List.length_append,List.length_cons,List.length_nil] <;> decide

theorem upperForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem upperReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem rangeLeafProgram_slots (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label control cursor, (leaf label control cursor).2.gateSlots ≤ bound)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    (rangeLeafProgram n after r leaf label dynamic start).2.gateSlots ≤ bound+1 := by
  have h := hl label r start
  cases after <;> simp only [rangeLeafProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem rangeScanProgram_slots (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label dynamic cursor, (leaf label dynamic cursor).2.gateSlots ≤ bound) (start : Nat) :
    (rangeScanProgram n after order tree control r path leaf start).2.gateSlots ≤
      (bound+1)*(tree.internalNodes+1)+10*tree.internalNodes+1 := by
  have h (a : Bool) := unaryProgram_slots_le n order (rangeLeafProgram n a r leaf) (bound+1)
    (fun label dynamic cursor => rangeLeafProgram_slots n a r leaf bound hl label dynamic cursor)
    tree control path start
  have hf := h false
  have ht := h true
  cases after <;> simp only [rangeScanProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem upperMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .inc tree control r path
    (fun label dynamic cursor => upperForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .dec tree control r path
    (fun label dynamic cursor => upperReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [upperMapProgram,appendCompiled_slots]
  grind only

theorem lowerMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .dec tree control r path
    (fun label dynamic cursor => lowerForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .inc tree control r path
    (fun label dynamic cursor => lowerReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [lowerMapProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEACellSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEALengthSlots -/
section Port_EEALengthSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem controlledXorConstant_length_le (control : Wire) (targets : List Wire) (value : Nat) :
    (controlledXorConstant control targets value).length ≤ targets.length := by
  induction targets generalizing value with
  | nil => exact Nat.zero_le _
  | cons target targets ih =>
    simp only [controlledXorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem dirtyConstantWrites_length_le (targets : List Wire) (dirtyAt valueAt : Nat → Nat) (labels : List Nat) :
    (dirtyConstantWrites targets dirtyAt valueAt labels).length ≤ labels.length*targets.length := by
  induction labels with
  | nil => exact Nat.zero_le _
  | cons label labels ih =>
    have h := controlledXorConstant_length_le (dirtyAt label) targets (valueAt label)
    simp only [dirtyConstantWrites,List.length_append,List.length_cons]
    nlinarith

theorem upperWriterProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := upperMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (truthMinusOneValue targets.length K)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (highestPositionWriteValue targets.length k) (zeroMapLabels k K).reverse
  simp only [List.length_reverse] at hd
  simp only [upperWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,highestPositionDirtyWrites]
  grind only

theorem lowerWriterProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := lowerMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (rightLengthValue width targets.length k)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (rightLengthWriteValue width targets.length K) (zeroMapLabels k K)
  simp only [lowerWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,rightLengthDirtyWrites]
  grind only

theorem surroundCompiled_slots {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).2.gateSlots = before.length+p.2.gateSlots+after.length := by
  simp only [surroundCompiled,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  omega


theorem xorConstant_length_le (wires : List Wire) (value : Nat) :
    (xorConstant wires value).length ≤ wires.length := by
  induction wires generalizing value with
  | nil => exact Nat.zero_le _
  | cons w ws ih =>
    simp only [xorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem cuccaroAdd_length_le (as bs : List Wire) (carry : Wire) :
    (cuccaroAdd as bs carry).length ≤ 6*as.length := by
  induction as generalizing bs carry with
  | nil => cases bs <;> exact Nat.zero_le _
  | cons a as ih =>
    cases bs with
    | nil => exact Nat.zero_le _
    | cons b bs =>
      have h := ih bs a
      simp only [cuccaroAdd,List.length_append,cuccaroMaj,cuccaroUma,List.length_cons,List.length_nil]
      omega

theorem addConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (addConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [addConstant,List.length_append]
  omega

theorem subConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (subConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [subConstant,List.length_append,cuccaroSub,circuit_adjoint_length]
  omega

theorem notRegister_length (register : List Wire) : (notRegister register).length=register.length := by
  induction register with
  | nil => rfl
  | cons w ws ih => simpa only [notRegister,List.length_cons] using congrArg Nat.succ ih

theorem incrementTail_length_le (bits : List Wire) (carry : Wire) (carries : List Wire) :
    (incrementTail bits carry carries).length ≤ 3*bits.length := by
  induction bits generalizing carry carries with
  | nil => exact Nat.zero_le _
  | cons bit bits ih =>
    cases bits with
    | nil => cases carries <;> simp [incrementTail]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := ih c cs
        simp only [incrementTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem uncontrolledIncrement_length_le (bits carries : List Wire) :
    (uncontrolledIncrement bits carries).length ≤ 3*bits.length := by
  cases bits with
  | nil => exact Nat.zero_le _
  | cons low bits =>
    cases bits with
    | nil => simp [uncontrolledIncrement]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := incrementTail_length_le (next::rest) c (cs.take rest.length)
        simp only [uncontrolledIncrement,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem constMinus_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (constMinus register constants carry value).length ≤ 4*register.length+8*constants.length := by
  have h := uncontrolledIncrement_length_le register (constants.take (register.length-1))
  have ha := addConstant_length_le register constants carry value
  simp only [constMinus,List.length_append,notRegister_length]
  omega


theorem ltUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthT.length+4*((zeroMapLabels k K).length*lengthT.length)+144*tree.internalNodes+72+
        8*lengthRP.length+16*constants.length := by
  have h1 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work2At work1At lengthT s
  have h2 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work1At work2At lengthT s
  have hc := constMinus_length_le lengthRP constants carry (width+2)
  simp only [ltUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only

theorem lrpUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthRP.length+4*((zeroMapLabels k K).length*lengthRP.length)+144*tree.internalNodes+72+
        16*constants.length := by
  have h1 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work1At work2At lengthRP s
  have h2 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work2At work1At lengthRP s
  have ha := addConstant_length_le lengthT constants carry 3
  have hs := subConstant_length_le lengthT constants carry 3
  simp only [lrpUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only


def endUpperSlotBound (r : EndIterationRegisters) (w : EndIterationWindows) : Nat :=
  2*r.lengthT.length+4*((zeroMapLabels w.k4 w.K4).length*r.lengthT.length)+
    144*(r.upperTree w).internalNodes+72+8*r.lengthRP.length+16*r.constants.length

def endLowerSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  2*r.lengthRP.length+4*((zeroMapLabels w.k5 (w.K5Decode width)).length*r.lengthRP.length)+
    144*(r.lowerTree width w).internalNodes+72+16*r.constants.length

theorem upperEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (upperEndProgram n start r width w).2.gateSlots ≤ endUpperSlotBound r w :=
  ltUpdateProgram_slots n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4)
    (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem lowerEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (lowerEndProgram n start r width w).2.gateSlots ≤ endLowerSlotBound r width w :=
  lrpUpdateProgram_slots n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry
    (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem controlledWorkSwap_length_le (control : Wire) (left right : List Wire) :
    (controlledWorkSwap control left right).length ≤ 3*left.length := by
  induction left generalizing right with
  | nil => cases right <;> exact Nat.zero_le _
  | cons l ls ih =>
    cases right with
    | nil => exact Nat.zero_le _
    | cons r rs =>
      have h := ih rs
      simp only [controlledWorkSwap,controlledSwap,List.length_append,List.length_cons,List.length_nil]
      omega

def endSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  3*r.work1.length+endUpperSlotBound r w+endLowerSlotBound r width w

theorem endProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu := upperEndProgram_slots n start r width w
  have hl (s : Nat) := lowerEndProgram_slots n s r width w
  have hs := controlledWorkSwap_length_le r.control r.work1 r.work2
  simp only [endProgram,prependCompiled_slots,appendCompiled_slots,endSlotBound]
  grind only

theorem endInverseProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endInverseProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu (s : Nat) := upperEndProgram_slots n s r width w
  have hl := lowerEndProgram_slots n start r width w
  have hs := controlledWorkSwap_length_le r.control r.work1.reverse r.work2.reverse
  simp only [List.length_reverse] at hs
  simp only [endInverseProgram,appendCompiled_slots,literalProgram_slots,controlledWorkSwapInverse,endSlotBound]
  grind only


theorem mcxVChainTail_length_le (acc : Wire) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainTail acc controls target scratch).length ≤ 2*controls.length := by
  induction controls generalizing acc scratch with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp [mcxVChainTail]
    | cons next rest =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons s ss =>
        have h := ih s ss
        simp only [mcxVChainTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem mcxVChain_length_le (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChain controls target scratch).length ≤ 2*controls.length+1 := by
  cases controls with
  | nil => simp [mcxVChain]
  | cons c cs =>
    cases cs with
    | nil => simp [mcxVChain]
    | cons next rest =>
      have h := mcxVChainTail_length_le next (c::rest) target scratch
      simp only [mcxVChain,List.length_cons]
      simp only [List.length_cons] at h
      omega

theorem blockHPrefix_length_le (r : IndexedStepRegisters) :
    (blockHPrefix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHPrefix,List.length_append,List.length_cons,List.length_nil]
  omega

theorem blockHSuffix_length_le (r : IndexedStepRegisters) :
    (blockHSuffix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHSuffix,List.length_append,List.length_cons,List.length_nil]
  omega

def hSlotBound (r : IndexedStepRegisters) (width T : Nat) : Nat :=
  4*r.lengthQ.length+4*r.lengthS.length+15+
    endSlotBound (r.endIteration width T) width (endIterationWindowsAt width T)

theorem hProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

theorem hInverseProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hInverseProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endInverseProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hInverseProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEALengthSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEAScheduleSlots -/
section Port_EEAScheduleSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem computeControl_length_le (controls : List Wire) (value : Nat) (target : Wire) (scratch : List Wire) :
    (computeControl controls value target scratch).length ≤ 4*controls.length+1 := by
  have hm := zeroMaskFrom_length_le controls value 0
  have hc := mcxVChain_length_le controls target scratch
  simp only [computeControl,List.length_append,circuit_adjoint_length,zeroMask]
  omega

theorem rControlNonterminal_length_le (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire) (scratch : List Wire) :
    (rControlNonterminal conditions value control lengthRPrime zeroRPrime scratch).length ≤
      4*lengthRPrime.length+4*conditions.length+7 := by
  have hr := mcxVChain_length_le lengthRPrime zeroRPrime scratch
  have hc := computeControl_length_le (conditions++[zeroRPrime]) (value%2^conditions.length) control scratch
  simp only [List.length_append,List.length_cons,List.length_nil] at hc
  simp only [rControlNonterminal,List.length_append]
  omega

theorem blockB2_length_le (r : IndexedStepRegisters) :
    (blockB2 r).length ≤ 8*r.lengthRPrime.length+31 := by
  have h := rControlNonterminal_length_le [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
  change ((rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch ++
    [Gate.CX r.control r.sign]) ++ rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).length ≤ _
  simp only [List.length_cons,List.length_nil] at h
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

theorem prepareLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (prepareLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,prepareLatestPaperTBoundary256_primitive r hl hw]
  rfl

theorem restoreLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (restoreLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,restoreLatestPaperTBoundary256_primitive r hl hw]
  rfl


theorem remainderBlockProgram_slots9 (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (ht : (r.remainder w).lengthT.length=9) (hq : (r.remainder w).lengthQ.length=9)
    (hs : (r.remainder w).lengthS.length=9) (hw : 9≤(r.remainder w).endpointScratch.length) :
    (remainderBlockProgram n start r width w).2.gateSlots ≤
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder w) w.start w.stop).internalNodes+2633 := by
  let b := 84*(intervalTree (r.remainder w) w.start w.stop).internalNodes+1273
  let a := 4*r.lengthRPrime.length+11
  let c := 4*r.lengthRPrime.length+17
  have hi (s : Nat) (m : RippleMode) (sg : Bool) := intervalProgram_slots9 n s (r.remainder w) width w.start w.stop m sg .work1 ht hq hs hw
  have h1 := rControlNonterminal_length_le [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
  have h2 := rControlNonterminal_length_le [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)
  have hb := blockB2_length_le r
  simp only [List.length_cons,List.length_nil] at h1 h2
  have h := sequenceProgram_slots_le n (remainderBlockSegments n r width w)
    ([a,b,a,8*r.lengthRPrime.length+31,c,b,c] : List Nat) (by
      unfold remainderBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; exact hi s .sub true
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; simpa only [literalProgram_slots] using hb
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega
      · intro s; exact hi s .add false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega) start
  simp only [List.sum_cons,List.sum_nil,a,b,c] at h
  unfold remainderBlockProgram
  omega

theorem coefficientBlockProgram_slots256 (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (coefficientBlockProgram n start r 256 w).2.gateSlots ≤
      108*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+597 := by
  let b := 54*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+37
  have hc (s : Nat) (m : RippleMode) (sg : Bool) := coefficientProgram_slots n s (r.coefficient w) w.start w.stop m sg .work2
  have h1 := computeControl_length_le [r.phase2,r.sign] 2 r.terminal r.blockScratch
  have h2 := computeControl_length_le [r.phase1,r.terminal] 1 r.control r.blockScratch
  have h3 := computeControl_length_le [r.phase1] 1 r.control r.blockScratch
  have hp := prepareLatestPaperTBoundary_length256 r.tBoundary hb hw
  have hr := restoreLatestPaperTBoundary_length256 r.tBoundary hb hw
  simp only [List.length_cons,List.length_nil] at h1 h2 h3
  have h := sequenceProgram_slots_le n (coefficientBlockSegments n r 256 w)
    ([256,b,33,b,234] : List Nat) (by
      unfold coefficientBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,List.length_append]; omega
      · intro s; exact hc s .sub false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact hc s .add true
      · intro s; simp only [literalProgram_slots,List.length_append]; omega) start
  simp only [List.sum_cons,List.sum_nil,b] at h
  unfold coefficientBlockProgram
  omega


def measuredStepSlotBound (r : IndexedStepRegisters) (T : Nat) : Nat :=
  (blockAForward r).length+
    (24*r.lengthRPrime.length+168*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder)
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+2633)+
    (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length+
    (108*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+597)+
    (blockFForward r).length+
    (8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32)+hSlotBound r 256 T

theorem measuredStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (measuredStepProgram n start r 256 T).2.gateSlots ≤ measuredStepSlotBound r T := by
  let rem := (certifiedActiveWindows 256 T).remainder
  let coef := (certifiedActiveWindows 256 T).coefficient
  have h := sequenceProgram_slots_le n (measuredStepSegments n r 256 T)
    ([(blockAForward r).length,
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder rem) rem.start rem.stop).internalNodes+2633,
      (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length,
      108*(coefficientPrefixTree (r.coefficient coef) coef.start coef.stop).internalNodes+597,
      (blockFForward r).length,
      8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
      hSlotBound r 256 T] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact remainderBlockProgram_slots9 n s r 256 rem ht hq hs he
      · intro s; simp only [literalProgram_slots,List.length_append]; exact Nat.le_refl _
      · intro s; exact coefficientBlockProgram_slots256 n s r coef hb hw
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s r.phaseUpdate r.shiftEpoch
      · intro s; exact hProgram_slots n s r 256 T) start
  simp only [List.sum_cons,List.sum_nil,rem,coef] at h
  unfold measuredStepProgram measuredStepSlotBound
  omega

theorem measuredScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (width count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredStepProgram n cursor r width T).2.gateSlots≤bound) (start : Nat) :
    (measuredScheduleProgram n r width count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hf := hstep first (by omega) (by omega) start
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega))
      (start+(measuredStepProgram n start r width first).1)
    rw [measuredScheduleProgram,appendCompiled_slots]
    nlinarith


def measuredInverseStepSlotBounds (r : IndexedStepRegisters) (T : Nat) : List Nat :=
  [ hSlotBound r 256 T,
    8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
    (((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase1] 1 r.control r.blockScratch ++ [Gate.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]))).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    (((([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    ((rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)).length ]

theorem measuredInverseStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length) :
    (measuredInverseStepProgram n start r T).2.gateSlots ≤ (measuredInverseStepSlotBounds r T).sum := by
  unfold measuredInverseStepProgram
  apply sequenceProgram_slots_le
  unfold measuredInverseStepSegments measuredInverseStepSlotBounds
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro s; exact hInverseProgram_slots n s r 256 T
  · intro s; exact phaseInverseProgram_slots n s r.phaseUpdate r.shiftEpoch
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.add.inverse) true .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.sub.inverse) false .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.add.inverse) false .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.sub.inverse) true .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _


theorem measuredInverseScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredInverseStepProgram n cursor r T).2.gateSlots≤bound) (start : Nat) :
    (measuredInverseScheduleProgram n r count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega)) start
    have hf := hstep first (by omega) (by omega)
      (start+(measuredInverseScheduleProgram n r count (first+1) start).1)
    rw [measuredInverseScheduleProgram,appendCompiled_slots]
    nlinarith

theorem intervalTree_nodes_le (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).internalNodes ≤ K := by
  have hn := dualUnaryAction_internalNodes_add_one (intervalTree r k K)
  have hl := dualUnaryAction_leaves_eq_labels_length (intervalTree r k K)
  rw [intervalTree_labels,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (intervalMainLabels k K)
  have hb : (intervalMainLabels k K).length ≤ K+1 := by
    simp only [intervalMainLabels]
    split <;> simp only [List.length_range,intervalLaneCount] <;> omega
  omega

theorem quotientSwapTree_nodes_le (r : QuotientSwapRegisters) (k K : Nat) (hk : k≤K) :
    (quotientSwapTree r k K).internalNodes ≤ K := by
  have hn := unaryAction_internalNodes_add_one (quotientSwapTree r k K)
  have hl := unaryAction_leaves_eq_labels_length (quotientSwapTree r k K)
  rw [quotientSwapTree_labels r hk,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (quotientSwapLabels k K)
  simp only [quotientSwapLabels,List.length_range'] at hc hl
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEAScheduleSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.StructuralSupport -/
section Port_StructuralSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every mentioned wire, including disabled constant-controlled gates. -/
def templateGateWires {n : Nat} : TemplateGate n → List Wire
  | .literal g => gateWires g
  | .whenBit _ _ g => gateWires g

/-- Syntactic support includes measurement targets and all record-controlled gates. -/
def straightWires {n s e : Nat} : Straight n s e → List Wire
  | .done => []
  | .gate g p => templateGateWires g ++ straightWires p
  | .recordGate _ _ g p => gateWires g ++ straightWires p
  | .measure w p => w :: straightWires p

private theorem port_StructuralSupport_subset_append {a b c d : List Wire} (h : a ⊆ c) (k : b ⊆ d) :
    a ++ b ⊆ c ++ d := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (h hx)
  · exact List.mem_append_right _ (k hx)

theorem templateGate_instantiate_support {n : Nat} (g : TemplateGate n)
    (read : ConstantBit n → Bool) : circuitWires (g.instantiate read) ⊆ templateGateWires g := by
  cases g <;> simp only [TemplateGate.instantiate,templateGateWires]
  · simp [circuitWires]
  · split <;> simp [circuitWires]

theorem straight_instantiate_support {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact port_StructuralSupport_subset_append (templateGate_instantiate_support g read) (ih history)
  | recordGate i v g p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.wires,straightWires]
    apply port_StructuralSupport_subset_append _ (ih history)
    split <;> simp [circuitWires]
  | measure w p ih =>
    intro x hx
    simp only [Straight.instantiate,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hx)
    · exact List.mem_cons_of_mem _ (ih _ hx)

theorem straightWires_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    straightWires (p.append q)=straightWires p ++ straightWires q := by
  induction p <;> simp_all only [Straight.append,straightWires,List.nil_append,List.append_assoc,List.cons_append]

theorem straightWires_castFinish {n s e f : Nat} (h : e=f) (p : Straight n s e) :
    straightWires (castFinish h p)=straightWires p := by subst f; rfl

theorem straightWires_shift {n s e : Nat} (p : Straight n s e) (offset : Nat) :
    straightWires (shiftStraight offset p)=straightWires p := by
  induction p <;> simp_all only [shiftStraight,straightWires]

theorem templateGateWires_reindex {n m : Nat} (f : Fin n → Fin m) (g : TemplateGate n) :
    templateGateWires (reindexGate f g)=templateGateWires g := by cases g <;> rfl

theorem straightWires_reindex {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    straightWires (reindexStraight f p)=straightWires p := by
  induction p <;> simp_all only [reindexStraight,straightWires,templateGateWires_reindex]

theorem gateProgram_support {n s : Nat} (gs : List (TemplateGate n)) :
    straightWires (gateProgram (cursor := s) gs)=gs.flatMap templateGateWires := by
  induction gs <;> simp_all only [gateProgram,straightWires,List.flatMap_nil,List.flatMap_cons]

theorem literalProgram_support (n start : Nat) (gs : Circuit) :
    straightWires (literalProgram (n := n) (s := start) gs)=circuitWires gs := by
  simp only [literalProgram,gateProgram_support,List.flatMap_map,templateGateWires,circuitWires]

theorem recordGates_support {n s e : Nat} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    straightWires (recordGates i gs p)=circuitWires gs ++ straightWires p := by
  induction gs <;> simp_all only [recordGates,straightWires,circuitWires,List.flatMap_nil,List.flatMap_cons,List.nil_append,List.append_assoc]

theorem appendCompiled_support {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    straightWires (appendCompiled p q).2=straightWires p.2 ++ straightWires q.2 := by
  simp only [appendCompiled,straightWires_castFinish,straightWires_append]

theorem surroundCompiled_support {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (surroundCompiled before after p).2=
      circuitWires before ++ straightWires p.2 ++ circuitWires after := by
  simp only [surroundCompiled,prependCompiled,appendCompiled_support,straightWires_append,literalProgram_support,List.append_assoc]


theorem templateGateWires_relabel {n : Nat} (e : Wire ≃ Wire) (g : TemplateGate n) :
    templateGateWires (relabelTemplateGate e g)=(templateGateWires g).map e := by
  cases g <;> rename_i g <;> cases g <;> rfl

theorem straightWires_relabel {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    straightWires (relabelStraight e p)=(straightWires p).map e := by
  have hg (g : Gate) : gateWires (g.relabel e)=(gateWires g).map e := by cases g <;> rfl
  induction p <;> simp_all only [relabelStraight,straightWires,templateGateWires_relabel,List.map_nil,List.map_append,List.map_cons]

theorem reindexCompiled_support {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (reindexCompiled f p).2=straightWires p.2 := by
  exact straightWires_reindex f p.2

theorem relabelCompiled_support {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (relabelCompiled e p).2=(straightWires p.2).map e := by
  exact straightWires_relabel e p.2

theorem sequenceProgram_support (n : Nat) (ps : List (FixedSegment n)) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, straightWires (p start).2 ⊆ support) (start : Nat) :
    straightWires (sequenceProgram n ps start).2 ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h p (by simp) start hw
    · exact ih (fun p hp => h p (by simp [hp])) _ hw

theorem collectProgram_support (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (support : List Wire) (h : ∀ cursor prior, straightWires (next cursor prior).2 ⊆ support)
    (ws : List Wire) (hw : ws ⊆ support) (start : Nat) (prior : List (Fin start)) :
    straightWires (collectProgram n next ws start prior).2 ⊆ support := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,straightWires_castFinish,straightWires,List.cons_subset]
    exact ⟨hw List.mem_cons_self,ih (fun _ hx => hw (List.mem_cons_of_mem _ hx)) _ _⟩

theorem resetProgram_support_static (n start : Nat) (ws : List Wire) :
    straightWires (resetProgram n start ws)=ws := by
  induction ws generalizing start <;> simp_all only [resetProgram,straightWires_castFinish,straightWires]

/-- A syntactic allocation is a sound support certificate for every readout and
history, including disabled constant gates and both measurement outcomes. -/
theorem compiled_support_of_static {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count)) (support : List Wire)
    (hp : straightWires p.2 ⊆ support) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (p.2.instantiate read history).wires ⊆ support :=
  (straight_instantiate_support p.2 read history).trans hp


def lookupOpWires {n : Nat} : LookupOp n → List Wire
  | .gates gs => gs.flatMap templateGateWires
  | .erase a b t => t :: circuitWires (controlledZ a b)

theorem lookupProgram_support (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n ops start)=ops.flatMap lookupOpWires := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [lookupProgram,straightWires_castFinish,straightWires_append,
      gateProgram_support,andEraseProgram,straightWires,recordGates_support,List.append_nil,
      List.flatMap_cons,lookupOpWires,ih]

theorem ordinaryOp_support {n : Nat} (gs : Circuit) :
    lookupOpWires (@ordinaryOp n gs)=circuitWires gs := by
  simp only [ordinaryOp,lookupOpWires,List.flatMap_map,templateGateWires,circuitWires]

theorem unaryLookupOps_support {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths support : List Wire)
    (hq : q ∈ support) (hp : paths ⊆ support) (hb : tree.indexWires ⊆ support)
    (hl : ∀ l c, c ∈ support → (leaf l c).flatMap templateGateWires ⊆ support) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, lookupOpWires op ⊆ support := by
  induction tree generalizing q paths with
  | leaf l => simpa only [unaryLookupOps,List.forall_mem_singleton,lookupOpWires] using hl l q hq
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hpath := hp List.mem_cons_self
      have hrest : rest ⊆ support := fun _ hx => hp (List.mem_cons_of_mem _ hx)
      have hbit : bit ∈ support := hb List.mem_cons_self
      have hz : zero.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have ho : one.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hz' := ihz path rest hpath hrest hz
      have ho' := iho path rest hpath hrest ho
      simp only [unaryLookupOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
      refine ⟨⟨⟨⟨⟨?_,fun _ => trivial⟩,hz'⟩,⟨?_,fun _ => trivial⟩⟩,ho'⟩,?_,?_,?_,?_,fun _ => trivial⟩
      all_goals simp [ordinaryOp,templateGateWires,lookupOpWires,computeZeroAnd,controlledZ,circuitWires,gateWires,hbit,hq,hpath]

theorem lookupLeafGates_support {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (support : List Wire) (hq : q ∈ support) (hp : ∀ p ∈ ports, p.2 ∈ support) :
    (lookupLeafGates q ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  simp only [lookupLeafGates,List.flatMap_map,List.mem_flatMap] at hw
  obtain ⟨p,hp',hw⟩ := hw
  simp only [templateGateWires,gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
  rcases hw with rfl | rfl
  · exact hq
  · exact hp p hp'

theorem pointLeaf_support {n : Nat} (row : Fin n) (q : Wire) (support : List Wire)
    (hq : q ∈ support) (hp : pointLogicalWires ⊆ support) :
    (pointLeaf row q).flatMap templateGateWires ⊆ support := by
  apply lookupLeafGates_support q _ support hq
  intro p hp'
  exact hp (List.of_mem_zip hp').2

theorem firstLookupOps_support : ∀ op ∈ firstLookupOps, lookupOpWires op ⊆ resetWires := by
  apply unaryLookupOps_support
  · simp [resetWires]
  · intro w hw
    apply List.mem_append_left
    apply List.mem_append_left
    simp only [List.mem_range'_1] at hw
    simp only [List.mem_range]
    omega
  · intro w hw
    have h := (tableAddressTree_mem_index (List.range' 855 16) 0 1 w).mp hw
    exact List.mem_append_right _ h
  · intro l q hq
    apply pointLeaf_support _ q resetWires hq
    intro w hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_range'_1,List.mem_cons,List.mem_nil_iff,or_false] at hw
    simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    rcases hw with hw | hw | hw
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr hw)

theorem actualFirstWindow_support_static (start : Nat) :
    straightWires (actualFirstWindow.program start) ⊆ resetWires := by
  simp only [actualFirstWindow,straightWires_reindex,firstLookupProgram,
    straightWires_castFinish,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact firstLookupOps_support op hop hw

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_StructuralSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchSupport -/
section Port_BatchSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Turn the source gate-by-gate support judgment into the wire collector used
by the challenge. No semantic equivalence is used to infer support. -/
theorem circuitWires_subset_of_usesOnly {support : List Wire} {gs : Circuit}
    (h : PaperCircuitUsesOnly support gs) : circuitWires gs ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact h g hg w hw

theorem registerEqualCircuit_support (cells : List (Wire × Wire)) (flag : Wire)
    (scratch support : List Wire) (hf : flag ∈ support) (hs : scratch ⊆ support)
    (hc : ∀ c ∈ cells, c.1 ∈ support ∧ c.2 ∈ support) :
    circuitWires (registerEqualCircuit cells flag scratch) ⊆ support := by
  have hx : circuitWires (xorWordCircuit cells) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hg
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact (hc c hc').1
    · exact (hc c hc').2
  have he : circuitWires (computeEqConst (cells.map Prod.snd) 0 flag scratch) ⊆ support := by
    apply (circuitWires_subset_of_usesOnly (computeEqConst_usesOnly _ _ _ _)).trans
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hw
      exact (hc c hc').2
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hf
      · exact hs hw
  simpa only [registerEqualCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro hx he) hx

theorem endpointTranspositionCircuit_support {n : Nat} (a b target : Fin n → Wire)
    (flag : Wire) (scratch support : List Wire)
    (ha : ∀ i, a i ∈ support) (hb : ∀ i, b i ∈ support) (ht : ∀ i, target i ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    circuitWires (endpointTranspositionCircuit a b target flag scratch) ⊆ support := by
  have he (r : Fin n → Wire) (hr : ∀ i, r i ∈ support) :
      circuitWires (registerEqualCircuit (equalityCells r target) flag scratch) ⊆ support := by
    apply registerEqualCircuit_support _ _ _ _ hf hs
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨hr i,ht i⟩
  have hu : circuitWires (endpointWordCircuit flag (endpointUpdateCells a b target)) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    simp only [endpointBitCircuit,List.mem_cons,List.mem_nil_iff,or_false] at hg
    rcases hg with rfl | rfl
    all_goals simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    all_goals rcases hw with rfl | rfl | rfl
    all_goals first | exact hf | exact ha i | exact hb i | exact ht i
  have he' : circuitWires (endpointTests a b target flag scratch) ⊆ support := by
    simpa only [endpointTests,circuitWires,List.flatMap_append,List.append_subset] using And.intro (he a ha) (he b hb)
  simpa only [endpointTranspositionCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro he' hu) he'


/-- Static support of a constant-controlled leaf, including disabled slots. -/
theorem endpointSelectGates_support {n : Nat} (control : Wire)
    (ports : List (Wire × EndpointBit n)) (support : List Wire)
    (hq : control ∈ support) (hp : ∀ p ∈ ports, p.1 ∈ support) :
    (endpointSelectGates control ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨p,hp',hg⟩ := List.mem_flatMap.mp hg
  have hpw := hp p hp'
  rcases p with ⟨port,bit⟩
  cases bit with
  | inl bit =>
    cases bit with
    | false => simp [endpointSelectGate] at hg
    | true =>
      simp only [endpointSelectGate,List.mem_singleton] at hg
      subst g
      rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
      · exact hq
      · exact hpw
  | inr bit =>
    simp only [endpointSelectGate,List.mem_singleton] at hg
    subst g
    rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchLeaf_support {n : Nat} (row : Fin n) (base control : Wire)
    (selection : List (Fin 8 × Fin 5)) (support : List Wire)
    (hq : control ∈ support) (hb : List.range' base 2565 ⊆ support) :
    (batchLeaf row base control selection).flatMap templateGateWires ⊆ support := by
  simp only [batchLeaf,List.flatMap_append,List.append_subset]
  constructor
  · apply endpointSelectGates_support _ _ _ hq
    intro p hp
    exact hb (List.mem_range'_1.mpr (batchPorts_bounds row base p.1 selection (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  · intro w hw
    simp only [List.flatMap_map,List.mem_flatMap] at hw
    obtain ⟨p,hp,hw⟩ := hw
    have hpw := hb (List.mem_range'_1.mpr (batchTags_bounds base p selection hp))
    rcases (show w = control ∨ w = p by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchOpCircuit_support (base : Wire) (source : Fin 4) (target : Fin 6) :
    circuitWires (batchOpCircuit base source target) ⊆ List.range' base 3590 := by
  apply endpointTranspositionCircuit_support
  all_goals simp only [List.mem_range'_1,batchWord,batchFlag,batchScratch]
  all_goals try (intro i; have := i.isLt; dsimp only [Wire] at *; omega)
  · dsimp only [Wire] at *; omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    have := i.isLt
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega

theorem batchOps_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (ops : List BatchOp) :
    ∀ op ∈ batchOps rows base tree control paths ops, lookupOpWires op ⊆ support := by
  have hsmall : List.range' base 2565 ⊆ support := by
    intro w hw
    apply hb
    simp only [List.mem_range'_1] at hw ⊢
    omega
  induction ops with
  | nil => simp [batchOps]
  | cons op ops ih =>
    cases op with
    | query sources target =>
      simp only [batchOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_support _ _ _ _ _ hc hp ht
        (fun l q hq => batchLeaf_support _ _ _ _ _ hq hsmall),ih⟩
    | swap source target =>
      simp only [batchOps,List.forall_mem_cons,ordinaryOp_support]
      exact ⟨(batchOpCircuit_support base source target).trans hb,ih⟩

theorem batchedEndpointProgram_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (start : Nat) :
    straightWires (batchedEndpointProgram rows base tree control paths start).2 ⊆ support := by
  simp only [batchedEndpointProgram,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact batchOps_support rows base tree control paths support hc hp ht hb batchSchedule op hop hw


/-- Component allocation before the data-bank permutation. -/
def batchRawSupport : List Wire :=
  836 :: pointLookupPath ++ pointLookupAddress ++ List.range' 1024 3590

theorem batchWindow_support_raw (w : OddWindow) (start : Nat) :
    straightWires (batchedEndpointProgram (batchWindowRows w) 1024
      batchWindowTree 836 pointLookupPath start).2 ⊆ batchRawSupport := by
  apply batchedEndpointProgram_support
  · simp [batchRawSupport]
  · intro z hz; simp [batchRawSupport,hz]
  · intro z hz
    have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
    simp [batchRawSupport,h]
  · intro z hz; simp [batchRawSupport,hz]

/-- Both real wire permutations place the complete correction block inside the
same reset allocation. In particular the temporary sixth word is replaced by
accumulator ports; it is not counted as an additional resident word. -/
theorem batchRawSupport_placed (z : Wire) (hz : z ∈ batchRawSupport) :
    windowAddressPerm 855 (by decide) (batchPlacement z) ∈ batchedResetWires := by
  change windowAddressSwap 855 (batchPlacementFn z) ∈ batchedResetWires
  simp only [batchRawSupport,pointLookupPath,pointLookupAddress,List.mem_cons,
    List.mem_append,List.mem_range'_1] at hz
  simp only [batchedResetWires,resetWires,List.mem_append,List.mem_range,
    List.mem_singleton,List.mem_range'_1]
  unfold batchPlacementFn windowAddressSwap
  split_ifs <;> dsimp only [Wire] at * <;> omega

attribute [local irreducible] batchedEndpointProgram

theorem placedBatchProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (placedBatchProgram w start).2).map (windowAddressPerm 855 (by decide))
      ⊆ batchedResetWires := by
  simp only [placedBatchProgram,relabelCompiled_support,List.map_map]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact batchRawSupport_placed v (batchWindow_support_raw w start hv)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_BatchSupport
