import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.Entrant.Single.Fourier
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources

/-!
Merged public-work provenance (Apache-2.0 lineage): upstream VerifiedQC/ShorECDLP;
ArthurOstapenko; dadon c6a88fc and bcad5b2; spariev c5e75ef and 070b740;
e-man07; and this Brief 17 integration of dadon's verified temporary-AND compiler
with spariev's asymmetric 30-window, four-EEA-cancellation entrant.
-/


/-! EDITABLE. Single-trial entrant: protected certificate assembly.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Certificate ====

section
/-! Single-trial certificate for the 263/263-bit protected nearest-pair decoder.
The fixed-table packaging follows the Apache-2.0 VerifiedQC Streaming certificate
(PR #551), for the construction of arXiv:2607.13816v2. See LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).finalCursor = e := rfl

theorem fixedEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).coefficients.length = n := List.length_ofFn


end ShorECDLP.Entrant.Single
end

namespace ShorECDLP.Entrant.Rounded
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open RoundedReadout
noncomputable section
set_option maxRecDepth 4096

def finePositions : List (Fin 921302466) :=
  Single.trialPositions.right.toList.attach.map fun i =>
    ⟨i.val, (Single.right_position_bound i.val i.property).2.trans (by decide)⟩

theorem finePositions_length : finePositions.length = 224 := by
  simp [finePositions, Single.params]

theorem finePositions_vals : finePositions.map Fin.val = Single.trialPositions.right.toList := by
  simp [finePositions, List.map_map]

def carryPosition : Fin 921302466 := finePositions[20]'(by rw [finePositions_length]; decide)
def inputPositions : List (Fin 921302466) := finePositions.drop 21

theorem inputPositions_length : inputPositions.length = 203 := by
  simp [inputPositions, finePositions_length]

def readout : Straight 901120 921302466 921302872 :=
  castFinish (by rw [inputPositions_length]) (addWord 921302466 carryPosition inputPositions)

def program : Straight 901120 0 921302872 := Single.program.append readout

def positions : TrialPositions decoderParams where
  left := Single.trialPositions.left
  right := Vector.ofFn fun i : Fin 203 => 921302466 + 2*i.val+1

def layout : DecodeLayout := ⟨.wrappedShift, decoderParams, [positions], by simp⟩

theorem readout_wellFormed : readout.WellFormed := by
  unfold readout
  rw [castFinish_wellFormed]
  exact addWord_wellFormed _ _ _

theorem readout_t (read : ConstantBit 901120 → Bool) (history : Fin 921302466 → Bool) :
    (readout.instantiate read history).tCount = 0 := by
  unfold readout
  rw [castFinish_instantiate]
  exact addWord_t _ _ _ _ _

theorem readout_support (read : ConstantBit 901120 → Bool) (history : Fin 921302466 → Bool) :
    (readout.instantiate read history).wires ⊆ completeBatchedSupport := by
  unfold readout
  rw [castFinish_instantiate]
  apply (addWord_support _ _ _ _ _).trans
  simp [List.subset_def, completeBatchedSupport, resetWires]

theorem program_clean (read : ConstantBit 901120 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (Single.program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [Single.Distribution.program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean resetWires resetWires_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 (by simp [resetWires]), h s hs 1 (by simp [resetWires])⟩

theorem word_eq (bits : List Bool) : fourierWordLSB bits = boolWordToNat bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [fourierWordLSB, boolWordToNat_cons, ih]

theorem fine_read (history : Fin 921302466 → Bool) :
    readWord (List.ofFn history) Single.trialPositions.right.toList =
      some (boolWordToNat (finePositions.map history)) := by
  rw [← finePositions_vals]
  have h := readWord_of_actual_bits (List.ofFn history) (finePositions.map Fin.val)
    (finePositions.map history) (by simp only [List.map_map, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Fin.eta, Function.comp_def])
  simpa only [word_eq] using h

theorem rounded_read (history : Fin 921302466 → Bool) :
    readWord (List.ofFn history ++ carryBits (history carryPosition) (inputPositions.map history))
      positions.right.toList = some (coarseRound (boolWordToNat (finePositions.map history))) := by
  let bits := finePositions.map history
  have hl : bits.length = 224 := by simp [bits, finePositions_length]
  have hc : history carryPosition = bits[20]'(by omega) := by
    simp [bits, carryPosition]
  have hi : inputPositions.map history = bits.drop 21 := by
    simp [bits, inputPositions, List.map_drop]
  rw [hc, hi]
  have hactual : positions.right.toList.map
      (fun i => (List.ofFn history ++ carryBits bits[20] (bits.drop 21))[i]?) =
      (sumBits bits[20] (bits.drop 21)).map some := by
    apply List.ext_getElem
    · simp only [List.length_map, positions, Vector.toList_ofFn, List.length_ofFn, sumBits_length, List.length_drop, hl]
      rfl
    · intro i hi hj
      simp only [List.length_map, positions, Vector.toList_ofFn, List.length_ofFn] at hi
      simp only [List.getElem_map, positions, Vector.toList_ofFn, List.getElem_ofFn]
      rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn]
      rw [show 921302466 + 2*i+1-921302466=2*i+1 by omega]
      rw [carryBits_odd, List.getElem?_eq_getElem (by simpa [sumBits_length, hl] using hi)]
  rw [readWord_of_actual_bits _ _ _ hactual, word_eq, rounded_word_value bits 20 (by omega)]
  simp only [hl, coarseRound]
  rfl


theorem readWord_append_left (before after : List Bool) (ps : List Nat)
    (h : ∀ i ∈ ps, i < before.length) : readWord (before ++ after) ps = readWord before ps := by
  induction ps with
  | nil => rfl
  | cons i ps ih =>
    simp only [readWord, List.getElem?_append_left (h i (by simp)),
      ih (fun j hj => h j (by simp [hj]))]

theorem readout_branch (read : ConstantBit 901120 → Bool) (history : Fin 921302466 → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ (readout.instantiate read history).run) (hn : b.kraus ψ ≠ 0) :
    b.history = carryBits (history carryPosition) (inputPositions.map history) := by
  unfold readout at hb
  rw [castFinish_instantiate] at hb
  exact (addWord_branch _ _ _ _ _ _ hψ b hb hn).2

theorem verified_of_reads (ps : TrialPositions decoderParams) (Q : Point) (d : Nat)
    (hd : Q = d • G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist ps.left.toList = some a)
    (hr : readWord hist ps.right.toList = some b)
    (hm : (d : ZMod order) ∈ fixedCandidates decoderParams a b) :
    (verifiedCandidate ⟨.wrappedShift, decoderParams, [ps], by simp⟩ Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order), ?_, ?_⟩
  · simpa only [candidates, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      decodeTrial, trialCandidates, hl, hr, fixedCandidates_take, Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq, ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem pairAccept_value (left right : List Nat) (accept : Nat → Nat → Bool)
    (before : List Bool) (v : Nat) (hr : readWord before right = some v)
    (hf : Single.Distribution.pairAccept left right accept before = true) :
    ∃ a, readWord before left = some a ∧ accept a v = true := by
  unfold Single.Distribution.pairAccept at hf
  rw [hr] at hf
  cases ha : readWord before left with
  | none => simp only [ha, Option.bind_none, Option.getD_none, Bool.false_eq_true] at hf
  | some a =>
    exact ⟨a, rfl, by simpa only [ha, Option.bind_some, Option.map_some, Option.getD_some] using hf⟩

theorem pairRecovered_mem (d a b : Nat) (h : pairRecovered d a b = true) :
    (d : ZMod order) ∈ fixedCandidates decoderParams a (coarseRound b) :=
  of_decide_eq_true h

theorem history_verified (ps : TrialPositions decoderParams) (left right : List Nat) (Q : Point) (d : Nat) (hd : Q = d • G)
    (before after : List Bool) (v : Nat)
    (hl : readWord (before ++ after) ps.left.toList = readWord before left)
    (hr : readWord (before ++ after) ps.right.toList = some (coarseRound v))
    (hfine : readWord before right = some v)
    (hf : Single.Distribution.pairAccept left right (pairRecovered d) before = true) :
    (verifiedCandidate ⟨.wrappedShift, decoderParams, [ps], by simp⟩ Q (before ++ after)).isSome := by
  obtain ⟨a, ha, hp⟩ := pairAccept_value left right (pairRecovered d) before v hfine hf
  exact verified_of_reads ps Q d hd _ a _ (hl.trans ha) hr (pairRecovered_mem d a v hp)

theorem verified_append_congr (Q : Point) (before a b : List Bool) (h : a = b)
    (ha : (verifiedCandidate layout Q (before ++ a)).isSome) :
    (verifiedCandidate layout Q (before ++ b)).isSome := by
  subst b
  exact ha

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q = d • G)
    (read : ConstantBit 901120 → Bool) (history : Fin 921302466 → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : Single.Distribution.fineEvent (pairRecovered d) (List.ofFn history) = true)
    (b : InstrumentBranch) (hb : b ∈ (readout.instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    (verifiedCandidate layout Q (List.ofFn history ++ b.history)).isSome := by
  classical
  have hhist := readout_branch read history ψ hψ b hb hn
  apply verified_append_congr Q (List.ofFn history) _ b.history hhist.symm
  have hr := rounded_read history
  have hl : readWord (List.ofFn history ++ carryBits (history carryPosition) (inputPositions.map history))
      positions.left.toList = readWord (List.ofFn history) Single.trialPositions.left.toList := by
    apply readWord_append_left
    intro i hi
    have h := Single.left_position_bound i hi
    simpa only [List.length_ofFn] using h.trans (by decide : 491391446 < 921302466)
  exact history_verified positions Single.trialPositions.left.toList Single.trialPositions.right.toList Q d hd _ _ _ hl hr (fine_read history) hf

theorem normSq_ge_zero (ψ : State) : 0 ≤ normSq ψ := by
  have h := normSq_interference (0 : State) ψ
  have hz : normSq (0 : State) = 0 := by simp [normSq]
  simp only [zero_add, hz, mul_zero, zero_add] at h
  linarith [h.2]

theorem mass_ge_zero (I : Instrument) (ψ : State) : 0 ≤ I.bornMass ψ :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact normSq_ge_zero _)

theorem mass_filter_eq (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State)
    (h : ∀ b ∈ I, b.kraus ψ ≠ 0 → p b = true) :
    Instrument.bornMass (I.filter p) ψ = I.bornMass ψ := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have ht := ih (fun c hc => h c (by simp [hc]))
    by_cases hb : p b = true
    · simpa [Instrument.bornMass, hb] using congrArg (normSq (b.kraus ψ) + ·) ht
    · have hz : b.kraus ψ = 0 := by
        by_contra hn
        exact hb (h b (by simp) hn)
      simpa [Instrument.bornMass, hb, hz, normSq] using ht

theorem appended_mass_lower (I : Instrument) (J : InstrumentBranch → Instrument)
    (p : InstrumentBranch → Bool) (q : InstrumentBranch → Bool) (ψ : State)
    (hn : ∀ a ∈ I, (J a).bornMass (a.kraus ψ) = normSq (a.kraus ψ))
    (hq : ∀ a ∈ I, p a = true → ∀ b ∈ J a,
      b.kraus (a.kraus ψ) ≠ 0 → q (a.seq b) = true) :
    Instrument.bornMass (I.filter p) ψ ≤
      Instrument.bornMass ((I.flatMap fun a => (J a).map a.seq).filter q) ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons a I ih =>
    have ht := ih (fun c hc => hn c (by simp [hc]))
      (fun c hc => hq c (by simp [hc]))
    have he : Instrument.bornMass (((J a).map a.seq).filter q) ψ =
        Instrument.bornMass ((J a).filter (fun b => q (a.seq b))) (a.kraus ψ) := by
      simp only [List.filter_map, Instrument.bornMass, List.map_map,
        InstrumentBranch.seq, LinearMap.comp_apply, Function.comp_def]
    simp only [List.flatMap_cons, List.filter_append, Instrument.bornMass,
      List.map_append, List.sum_append] at ht ⊢
    by_cases hp : p a = true
    · have heq := mass_filter_eq (J a) (fun b => q (a.seq b)) (a.kraus ψ)
        (hq a (by simp) hp)
      simp only [Instrument.bornMass] at he heq
      rw [he, heq]
      have hna := hn a (by simp)
      simp only [Instrument.bornMass] at hna
      rw [hna]
      simpa [Instrument.bornMass, hp] using add_le_add_left ht (normSq (a.kraus ψ))
    · have hpos := mass_ge_zero (((J a).map a.seq).filter q) ψ
      simp only [Instrument.bornMass] at hpos
      simpa [hp] using ht.trans (le_add_of_nonneg_left hpos)

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (Single.Distribution.program_rounded_success Q d hn hd).trans
  unfold program
  rw [Single.append_run_history]
  apply appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = 921302466 := by
      have h := straight_history_length Single.program (readConstant Single.mixedCoefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter 921302466 Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant Single.mixedCoefficientAt Q)
      (Single.historyAfter 921302466 Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

def entry : StraightEntry := Single.fixedEntry Single.mixedCoefficientAt program

def bounds : Bounds := ⟨855, 15398440784, 921302872⟩

theorem program_wellFormed : program.WellFormed :=
  straight_append_wellFormed _ _ Single.program_wellFormed readout_wellFormed

theorem program_support (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ completeBatchedSupport :=
  outer_append_support _ _ read Fin.elim0 completeBatchedSupport (Single.program_support read)
    (readout_support read)

theorem program_qubits (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).qubitCount ≤ 855 := by
  have hs : (program.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      completeBatchedSupport.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (program_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount, completeBatchedSupport_length] using hc

attribute [local irreducible] readout

theorem program_t (Q : Point) :
    (program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 15398440784 := by
  have h := outer_append_t_le Single.program readout (readConstant Single.mixedCoefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  rw [Nat.add_zero] at h
  change ((Single.program.append readout).instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 15398440784
  exact h.trans (Single.program_t Q)

theorem program_slots : program.gateSlots ≤ 93000061339 := by
  unfold program readout
  rw [Straight.gateSlots_append, castFinish_gateSlots, addWord_slots, inputPositions_length]
  have h := Single.program_slots
  omega

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact program_slots.trans (by decide)
  recordBudget := by
    change 921302872 ≤ officialLimits.measurements
    decide
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 1 * (2*(order/2^203+2)) ≤ 56*(2^49+2)
    simpa using one_trial_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact program_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨program_qubits _, program_t Q, (program.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Rounded


section


/-! Exact cancellation of reversible gates across commuting classical operations.
The rewrite preserves the full quantum operator, including on nonzero workspace. -/
namespace ShorECDLP.Entrant.Cancellation
open Quantum
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

def controls : Gate → List Wire
  | .CX a _ => [a]
  | .CCX a b _ => [a,b]
  | _ => []

def target : Gate → Wire
  | .X t | .H t | .CX _ t | .CCX _ _ t | .P _ _ t => t

def classicalGate : Gate → Bool
  | .X _ | .CX _ _ | .CCX _ _ _ => true
  | _ => false

def commutes (a b : Gate) : Bool :=
  classicalGate a && classicalGate b &&
    !(controls a).contains (target b) && !(controls b).contains (target a)

private theorem classical_commute (a b : Gate) (hc : commutes a b = true)
    (s : BasisState) :
    Classical.applyGate a (Classical.applyGate b s) =
      Classical.applyGate b (Classical.applyGate a s) := by
  cases a <;> cases b <;>
    simp_all [commutes, classicalGate, controls, target]
  all_goals
    funext w
    simp only [Classical.applyGate, upd]
    split_ifs <;> subst_vars <;> try contradiction
  all_goals simp only [eq_self, not_true_eq_false, false_and, and_false] at *
  all_goals try simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_not]

private theorem quantum_commute (a b : Gate) (hc : commutes a b = true)
    (ψ : State) :
    Quantum.applyGate a (Quantum.applyGate b ψ) =
      Quantum.applyGate b (Quantum.applyGate a ψ) := by
  have ha : Classical.IsClassicalGate a := by
    cases a <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hb : Classical.IsClassicalGate b := by
    cases b <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hk (s : BasisState) :
      Quantum.applyGate a (Quantum.applyGate b (ket s)) =
        Quantum.applyGate b (Quantum.applyGate a (ket s)) := by
    simp only [applyGate_ket_agrees_classical _ _ ha,
      applyGate_ket_agrees_classical _ _ hb, classical_commute a b hc]
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, hk]

/-- Search only through commuting gates. Failure leaves the input untouched. -/
def erase (g : Gate) : Circuit → Option Circuit
  | [] => none
  | h :: hs =>
    if g = h ∧ g.adjoint = g then some hs
    else if commutes g h then (erase g hs).map (List.cons h)
    else none

/-- Append one gate to a reverse-order accumulation, cancelling when possible. -/
def push (g : Gate) (gs : Circuit) : Circuit :=
  match erase g gs with
  | some rest => rest
  | none => g :: gs

/-- The list is processed from right to left. -/
def optimize : Circuit → Circuit
  | [] => []
  | g :: gs => push g (optimize gs)

theorem erase_sublist (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact List.Sublist.cons _ (List.Sublist.refl _)
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          exact List.Sublist.cons₂ _ (ih zs he)
      · simp at h

theorem push_sublist (g : Gate) (xs : Circuit) : (push g xs).Sublist (g :: xs) := by
  unfold push
  cases h : erase g xs with
  | none => exact List.Sublist.refl _
  | some ys => exact List.Sublist.cons _ (erase_sublist g xs ys h)

theorem optimize_sublist (xs : Circuit) : (optimize xs).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons g xs ih =>
    exact (push_sublist g (optimize xs)).trans (List.Sublist.cons₂ g ih)

private theorem erase_mem (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ∀ a ∈ ys, a ∈ xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact fun b hb => List.mem_cons_of_mem _ hb
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih zs he b hb)
      · simp at h

theorem push_mem (g : Gate) (xs : Circuit) :
    ∀ a ∈ push g xs, a ∈ g :: xs := by
  unfold push
  cases h : erase g xs with
  | none => exact fun _ ha => ha
  | some ys => exact fun a ha => List.mem_cons_of_mem _ (erase_mem g xs ys h a ha)

theorem optimize_mem (xs : Circuit) : ∀ a ∈ optimize xs, a ∈ xs := by
  induction xs with
  | nil => simp [optimize]
  | cons g xs ih =>
    intro a ha
    rcases List.mem_cons.mp (push_mem g (optimize xs) a ha) with rfl | hh
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih a hh)

theorem optimize_wellFormed (xs : Circuit) (h : CircuitWellFormed xs) :
    CircuitWellFormed (optimize xs) :=
  fun a ha => h a (optimize_mem xs a ha)

private theorem erase_run (g : Gate) (xs ys : Circuit)
    (hg : g.WellFormed) (h : erase g xs = some ys) (ψ : State) :
    Quantum.run (g :: xs) ψ = Quantum.run ys ψ := by
  induction xs generalizing ys ψ with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · rename_i he
      rcases he with ⟨rfl, hadj⟩
      cases h
      simp only [Quantum.run_cons]
      have hi := applyGate_adjoint_applyGate g hg ψ
      rw [hadj] at hi
      rw [hi]
    · split at h
      · rename_i hc
        cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          simp only [Quantum.run_cons]
          rw [← quantum_commute g a hc]
          exact ih zs he (Quantum.applyGate a ψ)
      · simp at h

theorem push_run (g : Gate) (xs : Circuit) (hg : g.WellFormed) (ψ : State) :
    Quantum.run (push g xs) ψ = Quantum.run (g :: xs) ψ := by
  unfold push
  cases h : erase g xs with
  | none => rfl
  | some ys => exact (erase_run g xs ys hg h ψ).symm

theorem optimize_run (xs : Circuit) (h : CircuitWellFormed xs) :
    Quantum.run (optimize xs) = Quantum.run xs := by
  induction xs with
  | nil => rfl
  | cons g xs ih =>
    have hg := h g (by simp)
    have ht : CircuitWellFormed xs := fun a ha => h a (by simp [ha])
    apply LinearMap.ext
    intro ψ
    rw [optimize, push_run _ _ hg, Quantum.run_cons, ih ht, Quantum.run_cons]

end ShorECDLP.Entrant.Cancellation

namespace ShorECDLP.Entrant.Cancellation
open Paper2607_13816

/-- The terminal-epoch restore has two redundant traversals of its predicate v-chain. -/
def epochSource : Circuit := blockCForward indexedStepProductionRegisters

def reducedEpoch : Circuit := optimize epochSource

private instance gateWellFormedDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

theorem epochSource_wellFormed : CircuitWellFormed epochSource := by
  unfold CircuitWellFormed
  decide +kernel

theorem reducedEpoch_run : Quantum.run reducedEpoch = Quantum.run epochSource :=
  optimize_run epochSource epochSource_wellFormed

theorem reducedEpoch_sublist : reducedEpoch.Sublist epochSource := optimize_sublist epochSource

theorem reducedEpoch_counts : ShorECDLP.tCount epochSource = 245 ∧
    ShorECDLP.tCount reducedEpoch = 133 ∧ reducedEpoch.length = 24 := by
  decide +kernel

end ShorECDLP.Entrant.Cancellation


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

/-- A syntactic subsequence retaining every measurement and classical control. -/
inductive Drops {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Nat → Prop
  | refl {s e} (p : Straight n s e) : Drops p p 0
  | skip {s e} (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate (.literal g) p) q (tCost g + d)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate g p) (.gate g q) d
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.recordGate i v g p) (.recordGate i v g q) d
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} {d : Nat} :
      Drops p q d → Drops (.measure w p) (.measure w q) d

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h <;> simp_all [Straight.gateSlots]; omega

theorem Drops.tCount {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (q.instantiate read history).tCount + d = (p.instantiate read history).tCount := by
  induction h with
  | refl => omega
  | skip g h ih =>
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hh := ih history
    omega
  | gate g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | record i v g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | measure w h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hf := ih (Fin.lastCases false history)
    have ht := ih (Fin.lastCases true history)
    omega

theorem Drops.wires {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ∀ w ∈ (q.instantiate read history).wires, w ∈ (p.instantiate read history).wires := by
  induction h with
  | refl => exact fun _ hw => hw
  | skip g h ih =>
    intro w hw
    exact List.mem_append_right _ (ih history w hw)
  | gate g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | record i v g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | measure v h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hw ⊢
    rcases hw with he | hf | ht
    · exact Or.inl he
    · exact Or.inr (Or.inl (ih (Fin.lastCases false history) w hf))
    · exact Or.inr (Or.inr (ih (Fin.lastCases true history) w ht))

private theorem Drops.append_right {n a b c d} (p : Straight n a b)
    {q q' : Straight n b c} (h : Drops q q' d) : Drops (p.append q) (p.append q') d := by
  induction p with
  | done => exact h
  | gate g p ih => exact Drops.gate g (ih h)
  | recordGate i v g p ih => exact Drops.record i v g (ih h)
  | measure w p ih => exact Drops.measure w (ih h)

theorem Drops.append {n a b c d f} {p p' : Straight n a b} {q q' : Straight n b c}
    (hp : Drops p p' d) (hq : Drops q q' f) :
    Drops (p.append q) (p'.append q') (d+f) := by
  induction hp with
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | gate g h ih => exact Drops.gate g (ih hq)
  | record i v g h ih => exact Drops.record i v g (ih hq)
  | measure w h ih => exact Drops.measure w (ih hq)

private theorem tCount_le_of_sublist {xs ys : Circuit} (h : xs.Sublist ys) :
    ShorECDLP.tCount xs ≤ ShorECDLP.tCount ys := by
  induction h <;> simp_all [ShorECDLP.tCount]; omega

theorem Drops.literal {n s} {xs ys : Circuit} (h : ys.Sublist xs) :
    Drops (literalProgram xs : Straight n s s) (literalProgram ys)
      (ShorECDLP.tCount xs - ShorECDLP.tCount ys) := by
  induction h with
  | slnil => exact Drops.refl _
  | cons a h ih =>
    have ht := tCount_le_of_sublist h
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_assoc ht]
      using Drops.skip a ih
  | cons₂ a h ih =>
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_add_left] using Drops.gate (.literal a) ih

/-- Structural circuit rewrites, with exact operator equality at unitary leaves. -/
inductive Rewrites {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Prop
  | refl {s e} (p : Straight n s e) : Rewrites p p
  | literal {s} (xs ys : Circuit) : Quantum.run xs = Quantum.run ys →
      Rewrites (literalProgram xs : Straight n s s) (literalProgram ys)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.gate g p) (.gate g q)
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.recordGate i v g p) (.recordGate i v g q)
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} :
      Rewrites p q → Rewrites (.measure w p) (.measure w q)
  | append {a b c} {p p' : Straight n a b} {q q' : Straight n b c} :
      Rewrites p p' → Rewrites q q' → Rewrites (p.append q) (p'.append q')

private noncomputable def branchPrefix (history : List Bool) (u : State →ₗ[ℂ] State)
    (branches : Instrument) : Instrument :=
  branches.map fun b => ⟨history ++ b.history, b.kraus.comp u⟩

private theorem prefix_prefix (a b : List Bool) (u v : State →ₗ[ℂ] State) (bs : Instrument) :
    branchPrefix a u (branchPrefix b v bs) = branchPrefix (a++b) (v.comp u) bs := by
  simp only [branchPrefix, List.map_map]
  congr 1
  funext branch
  simp only [Function.comp_apply, List.append_assoc, LinearMap.comp_assoc]

/-- Continuation evaluator used only to prove context closure, never as submitted data. -/
private noncomputable def evaluate {n s e} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : Instrument :=
  match p with
  | .done => tail history
  | .gate g p => branchPrefix [] (Quantum.run (g.instantiate read)) (evaluate p read history tail)
  | .recordGate i v g p => branchPrefix [] (Quantum.run (if history i=v then [g] else []))
      (evaluate p read history tail)
  | .measure w p =>
      branchPrefix [false] (xResetKraus w false) (evaluate p read (Fin.lastCases false history) tail) ++
      branchPrefix [true] (xResetKraus w true) (evaluate p read (Fin.lastCases true history) tail)

private theorem evaluate_append {n a b c} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (tail : (Fin c → Bool) → Instrument) :
    evaluate (p.append q) read history tail =
      evaluate p read history (fun h => evaluate q read h tail) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, evaluate, ih]
  | recordGate i v g p ih => simp only [Straight.append, evaluate, ih]
  | measure w p ih => simp only [Straight.append, evaluate, ih]

private theorem evaluate_literal {n s} (xs : Circuit) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (tail : (Fin s → Bool) → Instrument) :
    evaluate (literalProgram xs) read history tail = branchPrefix [] (Quantum.run xs) (tail history) := by
  induction xs with
  | nil => simp [literalProgram, gateProgram, evaluate, branchPrefix, Quantum.run]
  | cons g xs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, evaluate, TemplateGate.instantiate] at ⊢
    change branchPrefix [] (Quantum.run [g]) (evaluate (literalProgram xs) read history tail) = _
    rw [ih, prefix_prefix]
    simp [Quantum.run]

private theorem Rewrites.eval_eq {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : evaluate p read history tail = evaluate q read history tail := by
  induction h with
  | refl => rfl
  | literal xs ys he => simp only [evaluate_literal, he]
  | gate g h ih =>
    simp only [evaluate, ih]
  | record i v g h ih =>
    simp only [evaluate, ih]
  | measure w h ih =>
    simp only [evaluate, ih]
  | append hp hq ip iq =>
    simp only [evaluate_append]
    rw [ip]
    congr 1
    funext hist
    exact iq hist tail

private theorem evaluate_run {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    evaluate p read history (fun _ => [{history := [], kraus := LinearMap.id}]) =
      (p.instantiate read history).run := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | recordGate i v g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | measure w p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl

theorem Rewrites.run {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).run = (q.instantiate read history).run := by
  rw [← evaluate_run, ← evaluate_run]
  exact h.eval_eq read history _

private theorem reindex_append {n m a b c} (f : Fin n → Fin m)
    (p : Straight n a b) (q : Straight n b c) :
    reindexStraight f (p.append q) = (reindexStraight f p).append (reindexStraight f q) := by
  induction p <;> simp_all [reindexStraight, Straight.append]

private theorem reindex_literal {n m s} (f : Fin n → Fin m) (xs : Circuit) :
    reindexStraight f (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, reindexStraight, reindexGate]

theorem Rewrites.reindex {n m s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Fin n → Fin m) : Rewrites (reindexStraight f p) (reindexStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [reindex_literal] using Rewrites.literal (n := m) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [reindex_append] using Rewrites.append ip iq

theorem Drops.reindex {n m s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Fin n → Fin m) : Drops (reindexStraight f p) (reindexStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem relabel_append {n a b c} (f : Wire ≃ Wire)
    (p : Straight n a b) (q : Straight n b c) :
    relabelStraight f (p.append q) = (relabelStraight f p).append (relabelStraight f q) := by
  induction p <;> simp_all [relabelStraight, Straight.append]

private theorem relabel_literal {n s} (f : Wire ≃ Wire) (xs : Circuit) :
    relabelStraight f (literalProgram xs : Straight n s s) = literalProgram (xs.map (Gate.relabel f)) := by
  induction xs <;> simp_all [literalProgram, gateProgram, relabelStraight, relabelTemplateGate]

private theorem relabel_run_eq (f : Wire ≃ Wire) (xs ys : Circuit)
    (h : Quantum.run xs = Quantum.run ys) :
    Quantum.run (xs.map (Gate.relabel f)) = Quantum.run (ys.map (Gate.relabel f)) := by
  apply LinearMap.ext
  intro ψ
  have hx := Quantum.run_relabel f xs (relabelState f.symm ψ)
  have hy := Quantum.run_relabel f ys (relabelState f.symm ψ)
  simp only [relabelState_symm_right] at hx hy
  rw [hx, hy, h]

theorem Rewrites.relabel {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Wire ≃ Wire) : Rewrites (relabelStraight f p) (relabelStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he =>
    simpa only [relabel_literal] using Rewrites.literal (n := n)
      (xs.map (Gate.relabel f)) (ys.map (Gate.relabel f)) (relabel_run_eq f xs ys he)
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [relabel_append] using Rewrites.append ip iq

theorem Drops.relabel {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Wire ≃ Wire) : Drops (relabelStraight f p) (relabelStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih =>
    have he : tCost (g.relabel f) = tCost g := by cases g <;> rfl
    simpa only [he] using Drops.skip (g.relabel f) ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem shift_append {n a b c} (offset : Nat)
    (p : Straight n a b) (q : Straight n b c) :
    shiftStraight offset (p.append q) = (shiftStraight offset p).append (shiftStraight offset q) := by
  induction p <;> simp_all [shiftStraight, Straight.append]

private theorem shift_literal {n s} (offset : Nat) (xs : Circuit) :
    shiftStraight offset (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, shiftStraight]

theorem Rewrites.shift {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (offset : Nat) : Rewrites (shiftStraight offset p) (shiftStraight offset q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [shift_literal] using Rewrites.literal (n := n) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [shift_append] using Rewrites.append ip iq

theorem Drops.shift {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (offset : Nat) : Drops (shiftStraight offset p) (shiftStraight offset q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

theorem Rewrites.castFinish {n s e f} {p q : Straight n s e} (h : Rewrites p q)
    (he : e=f) : Rewrites (castFinish he p) (castFinish he q) := by
  subst f
  exact h

theorem Drops.castFinish {n s e f d} {p q : Straight n s e} (h : Drops p q d)
    (he : e=f) : Drops (castFinish he p) (castFinish he q) d := by
  subst f
  exact h

private theorem qubitCount_mono (a b : AdaptiveCircuit)
    (h : ∀ w ∈ a.wires, w ∈ b.wires) : a.qubitCount ≤ b.qubitCount := by
  have hh : a.wires.toFinset ⊆ b.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h w (List.mem_toFinset.mp hw))
  simpa only [AdaptiveCircuit.qubitCount, List.card_toFinset] using Finset.card_le_card hh

/-- Retain the exact table and decoder cursor while substituting an equivalent program. -/
def replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) : StraightEntry :=
  ⟨e.coefficients,e.finalCursor,p⟩

/-- Transport the protected certificate along a verified gate deletion with exact T savings. -/
theorem replacement_certificate {limits : Limits} {layout : DecodeLayout}
    {entry : StraightEntry} {bounds : Bounds} (original : Certificate limits layout entry bounds)
    {p : Straight entry.coefficients.length 0 entry.finalCursor} {saving : Nat}
    (hd : Drops entry.program p saving) (he : Rewrites entry.program p) :
    Certificate limits layout (replaceEntry entry p)
      ⟨bounds.qubits,bounds.tModel-saving,bounds.measurements⟩ := by
  refine ⟨hd.slots.trans original.gateBudget, original.recordBudget, original.tableBudget,
    original.candidateBudget, hd.wellFormed original.wellFormed, ?_, ?_⟩
  · intro Q
    have ho := original.resources Q
    have hq := qubitCount_mono (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0)
      (entry.instantiate Q) (hd.wires _ _)
    have ht := hd.tCount (readConstant entry.coefficients.get Q) Fin.elim0
    have hm := Straight.measurementCount p (readConstant entry.coefficients.get Q) Fin.elim0
    have hm' := Straight.measurementCount entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    change (entry.instantiate Q).qubitCount ≤ bounds.qubits ∧
      (entry.instantiate Q).tCount ≤ bounds.tModel ∧
      (entry.instantiate Q).measurementCount ≤ bounds.measurements at ho
    change (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).qubitCount ≤ bounds.qubits ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel-saving ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ bounds.measurements
    exact ⟨hq.trans ho.1, by dsimp only [StraightEntry.instantiate] at ho; omega,
      by dsimp only [StraightEntry.instantiate] at ho; omega⟩
  · intro Q d hQ hdQ
    have hh := he.run (readConstant entry.coefficients.get Q) Fin.elim0
    change (99 : ℝ)/100 ≤ Instrument.bornMass
      (((p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run).filter _) (ket zeroBasisState)
    rw [← hh]
    exact original.success Q d hQ hdQ

/-- A program together with the exact proof needed to replace a fixed source context. -/
structure Patch {n s e : Nat} (source : Straight n s e) (saving : Nat) where
  program : Straight n s e
  drops : Drops source program saving
  rewrites : Rewrites source program

namespace Patch
noncomputable section

def refl {n s e} (p : Straight n s e) : Patch p 0 := ⟨p, Drops.refl p, Rewrites.refl p⟩

def castSaving {n s e a b} {p : Straight n s e} (h : Patch p a) (he : a=b) : Patch p b := he ▸ h

def literal {n s d} (xs ys : Circuit) (hs : ys.Sublist xs)
    (hr : Quantum.run xs = Quantum.run ys)
    (ht : ShorECDLP.tCount ys + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d := by
  refine ⟨literalProgram ys, ?_, Rewrites.literal xs ys hr⟩
  have hd : ShorECDLP.tCount xs - ShorECDLP.tCount ys = d := by omega
  simpa only [hd] using Drops.literal (n := n) (s := s) hs

def append {n a b c d f} {p : Straight n a b} {q : Straight n b c}
    (hp : Patch p d) (hq : Patch q f) : Patch (p.append q) (d+f) :=
  ⟨hp.program.append hq.program, hp.drops.append hq.drops, hp.rewrites.append hq.rewrites⟩

def castFinish {n s e f d} {p : Straight n s e} (hp : Patch p d) (he : e=f) :
    Patch (Paper2607_13816.ChallengeMigration.castFinish he p) d :=
  ⟨Paper2607_13816.ChallengeMigration.castFinish he hp.program, hp.drops.castFinish he, hp.rewrites.castFinish he⟩

def appendCompiled {n start d f}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : Patch p.2 d) (hq : Patch q.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.appendCompiled p q).2 (d+f) :=
  (hp.append hq).castFinish (Nat.add_assoc start p.1 q.1)

def sequenceCons {n start d f} (head : FixedSegment n) (tail : List (FixedSegment n))
    (hp : Patch (head start).2 d)
    (hq : Patch (sequenceProgram n tail (start+(head start).1)).2 f) :
    Patch (sequenceProgram n (head::tail) start).2 (d+f) :=
  appendCompiled (head start) (sequenceProgram n tail (start+(head start).1)) hp hq

def gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : Patch p d) :
    Patch (.gate g p) d := ⟨.gate g hp.program, Drops.gate g hp.drops, Rewrites.gate g hp.rewrites⟩

def record {n s e d} (i : Fin s) (v : Bool) (g : Gate) {p : Straight n s e}
    (hp : Patch p d) : Patch (.recordGate i v g p) d :=
  ⟨.recordGate i v g hp.program, Drops.record i v g hp.drops, Rewrites.record i v g hp.rewrites⟩

def measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : Patch p d) :
    Patch (.measure w p) d :=
  ⟨.measure w hp.program, Drops.measure w hp.drops, Rewrites.measure w hp.rewrites⟩

def reindex {n m s e d} {p : Straight n s e} (hp : Patch p d) (f : Fin n → Fin m) :
    Patch (reindexStraight f p) d :=
  ⟨reindexStraight f hp.program, hp.drops.reindex f, hp.rewrites.reindex f⟩

def relabel {n s e d} {p : Straight n s e} (hp : Patch p d) (f : Wire ≃ Wire) :
    Patch (relabelStraight f p) d :=
  ⟨relabelStraight f hp.program, hp.drops.relabel f, hp.rewrites.relabel f⟩

def shift {n s e d} {p : Straight n s e} (hp : Patch p d) (offset : Nat) :
    Patch (shiftStraight offset p) d :=
  ⟨shiftStraight offset hp.program, hp.drops.shift offset, hp.rewrites.shift offset⟩

end
end Patch

end ShorECDLP.Entrant.Optimization


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
open Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
  preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
  measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
  measuredInverseStepProgram measuredEEAReverseProgram measuredReverseWrapperProgram
  hInverseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplicationProgram
  multiplicationAfterResetProgram multiplicationCorrectionProgram multiplicationCleanupProgram
  multiplyDataProgram unmultiplyDataProgram divisionCorrectionProgram collectProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram


def Patch.prependCompiled {n start d} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram gs)).append hp).castSaving (Nat.zero_add d)

def Patch.surroundCompiled {n start d} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram before)).append
    ((Patch.appendCompiled p ⟨0, literalProgram after⟩ hp (Patch.refl _)).castSaving (Nat.add_zero d))).castSaving (Nat.zero_add d)

/-- Rewrite one terminal-epoch restore inside an otherwise untouched literal segment. -/
def epochPatch (n s : Nat) (tail : Circuit) :
    Patch (literalProgram (Cancellation.epochSource ++ tail) : Straight n s s) 112 := by
  apply Patch.literal _ (Cancellation.reducedEpoch ++ tail)
  · exact Cancellation.reducedEpoch_sublist.append (List.Sublist.refl _)
  · simp only [Quantum.run_append_map, Cancellation.reducedEpoch_run]
  · have h := Cancellation.reducedEpoch_counts
    simp only [ShorECDLP.tCount_append, h.1, h.2.1]
    omega



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def aSource : Circuit := blockAForward indexedStepProductionRegisters
def aMiddle : Circuit := (aSource.drop 837).take 33
def aReduced : Circuit := aSource.take 837 ++ Cancellation.optimize aMiddle ++ aSource.drop 870

private theorem split_three (xs : Circuit) (a b : Nat) :
    xs = xs.take a ++ (xs.drop a).take b ++ xs.drop (a+b) := by
  rw [List.append_assoc, ← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

private theorem aSplit : aSource = aSource.take 837 ++ aMiddle ++ aSource.drop 870 :=
  split_three aSource 837 33

private theorem aMiddle_wellFormed : CircuitWellFormed aMiddle := by
  unfold CircuitWellFormed
  decide +kernel

private theorem aMiddle_counts : ShorECDLP.tCount aMiddle = 105 ∧
    ShorECDLP.tCount (Cancellation.optimize aMiddle) = 7 := by
  decide +kernel

def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 98 := by
  apply Patch.literal _ aReduced
  · conv_rhs => rw [aSplit]
    exact ((List.Sublist.refl _).append (Cancellation.optimize_sublist aMiddle)).append (List.Sublist.refl _)
  · have h := Cancellation.optimize_run aMiddle aMiddle_wellFormed
    conv_lhs => rw [aSplit]
    simp only [aReduced, Quantum.run_append_map, h]
  · conv_rhs => rw [aSplit]
    have h := aMiddle_counts
    simp only [aReduced, ShorECDLP.tCount_append, h.1, h.2]
    omega


set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b2Source : Circuit := blockB2 indexedStepProductionRegisters
private theorem b2_wellFormed : CircuitWellFormed b2Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b2_counts : ShorECDLP.tCount b2Source = 462 ∧
    ShorECDLP.tCount (Cancellation.optimize b2Source) = 238 := by
  decide +kernel

def b2Patch (n start : Nat) : Patch (literalProgram b2Source : Straight n start start) 224 := by
  apply Patch.literal _ (Cancellation.optimize b2Source)
  · exact Cancellation.optimize_sublist b2Source
  · exact (Cancellation.optimize_run b2Source b2_wellFormed).symm
  · have h := b2_counts
    omega

def remainderPatch (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 224 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b1Source : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
private theorem b1_wellFormed : CircuitWellFormed b1Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b1_counts : ShorECDLP.tCount b1Source = 217 ∧
    ShorECDLP.tCount (Cancellation.optimize b1Source) = 119 := by decide +kernel

def b1Patch (n start : Nat) : Patch (literalProgram b1Source : Straight n start start) 98 := by
  apply Patch.literal _ (Cancellation.optimize b1Source)
  · exact Cancellation.optimize_sublist b1Source
  · exact (Cancellation.optimize_run b1Source b1_wellFormed).symm
  · have h := b1_counts; omega

def remainderPatchAll (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 420 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 322) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 322) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 98) (f := 224) _ _ (b1Patch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

def ePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary 256

def eCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

private theorem ePrep_wellFormed : CircuitWellFormed ePrepSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem eClean_wellFormed : CircuitWellFormed eCleanSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem ePrep_counts : ShorECDLP.tCount ePrepSource = 560 ∧
    ShorECDLP.tCount (Cancellation.optimize ePrepSource) = 518 := by decide +kernel
private theorem eClean_counts : ShorECDLP.tCount eCleanSource = 539 ∧
    ShorECDLP.tCount (Cancellation.optimize eCleanSource) = 497 := by decide +kernel

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize ePrepSource)
  · exact Cancellation.optimize_sublist ePrepSource
  · exact (Cancellation.optimize_run ePrepSource ePrep_wellFormed).symm
  · have h := ePrep_counts; omega

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize eCleanSource)
  · exact Cancellation.optimize_sublist eCleanSource
  · exact (Cancellation.optimize_run eCleanSource eClean_wellFormed).symm
  · have h := eClean_counts; omega

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 84 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 42) (f := 42) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 42) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 98) (f := 616) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 420) (f := 196) _ _ (remainderPatchAll n _ 256 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 112) (f := 84) _ _ (epochPatch n _ _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 84) (f := 0) _ _ (coefficientPatch n _ _) (Patch.refl _)).castSaving (by omega)

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 :=
  candidateStepPatch n start T

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*714)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredScheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by omega)


def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 1156680 := by
  unfold measuredEEAForwardProgram
  exact schedulePatch n 1620 1 start


def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 1156680 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


/-- Literal concatenation supports mirrored segments without changing their context. -/
private theorem literal_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append, literalProgram, List.map_nil, gateProgram, Straight.append]
  | cons g xs ih => simpa only [literalProgram, List.map_cons, gateProgram, Straight.append] using congrArg (Straight.gate (.literal g)) ih

def Patch.joinLiteral {n s d f} {xs ys : Circuit}
    (hp : Patch (literalProgram xs : Straight n s s) d)
    (hq : Patch (literalProgram ys : Straight n s s) f) :
    Patch (literalProgram (xs ++ ys) : Straight n s s) (d+f) := by
  rw [literal_append]
  exact hp.append hq

def optimizedLiteralPatch (n s d : Nat) (xs : Circuit)
    (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (Cancellation.optimize xs) + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d :=
  Patch.literal xs (Cancellation.optimize xs) (Cancellation.optimize_sublist xs)
    (Cancellation.optimize_run xs hw).symm ht

def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reverseCleanSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reversePrepSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseEpochPatch (n s : Nat) :
    Patch (literalProgram (blockCInverse indexedStepProductionRegisters) : Straight n s s) 112 :=
  optimizedLiteralPatch n s 112 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

/-- The reverse A literal is split around the terminal-padding epoch test.
Source arithmetic: VerifiedQC/ShorECDLP PR #551, Apache-2.0. -/
def aTerminalSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl (r.phase1 :: r.lengthRPrime) (2 ^ (r.lengthRPrime.length + 1) - 2) r.terminal r.blockScratch

def aInverseBefore : Circuit :=
  let r := indexedStepProductionRegisters
  aTerminalSource ++ terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow ++
    [.CX r.terminal r.phase1] ++ (preShiftUnitary r.preShift).adjoint ++ [.CX r.terminal r.phase1]

def aInverseEpoch : Circuit := terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding

def aInverseAfter : Circuit :=
  let r := indexedStepProductionRegisters.terminalPadding
  controlledDecrement r.terminal r.lengthS r.carries ++ controlledRotateRightOne r.terminal r.work2 ++ aTerminalSource

private theorem aInverseEpoch_wellFormed : CircuitWellFormed aInverseEpoch := by
  unfold CircuitWellFormed
  decide +kernel
private theorem aInverseEpoch_saving :
    ShorECDLP.tCount (Cancellation.optimize aInverseEpoch) + 98 = ShorECDLP.tCount aInverseEpoch := by
  decide +kernel

def aInversePatch (n s : Nat) :
    Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n s s) 98 := by
  have hp := (((Patch.refl (literalProgram aInverseBefore : Straight n s s)).joinLiteral
    (optimizedLiteralPatch n s 98 aInverseEpoch aInverseEpoch_wellFormed aInverseEpoch_saving)).joinLiteral
    (Patch.refl (literalProgram aInverseAfter : Straight n s s))).castSaving (show 0+98+0=98 by omega)
  simpa only [aInverseBefore, aInverseAfter, aInverseEpoch, aTerminalSource,
    blockAInverse, terminalPaddingInverse, List.append_assoc] using hp

def b3Source : Circuit :=
  let r := indexedStepProductionRegisters
  ([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]

def reverseFrontPatch (n s : Nat) :
    Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint ++
      prepareLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256 ++
      computeControl [indexedStepProductionRegisters.phase1] 1 indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch) : Straight n s s) 42 := by
  have hp := ((Patch.refl (literalProgram (blockFForward indexedStepProductionRegisters).adjoint : Straight n s s)).joinLiteral
    (reverseCleanPatch n s)).castSaving (show 0+42=42 by omega)
  simpa only [reverseCleanSource, List.append_assoc] using hp

def reverseCombinedPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (let r := indexedStepProductionRegisters;
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
      computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++
      blockDInverse r w ++ blockCInverse r ++
      (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) : Straight n s s) 154 := by
  have hp := ((((reversePrepPatch n s).joinLiteral
    (Patch.refl (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n s s))).joinLiteral
    (reverseEpochPatch n s)).joinLiteral (Patch.refl (literalProgram b3Source : Straight n s s))).castSaving
    (show 42+0+112+0=154 by omega)
  simpa only [reversePrepSource, b3Source, List.append_assoc] using hp

def reverseRemainderPatch (n s : Nat) :
    Patch (literalProgram (b3Source ++ b2Source ++ b1Source) : Straight n s s) 322 := by
  have hp := (((Patch.refl (literalProgram b3Source : Straight n s s)).joinLiteral
    (b2Patch n s)).joinLiteral (b1Patch n s)).castSaving (show 0+224+98=322 by omega)
  simpa only [List.append_assoc] using hp

def reverseStepPatch (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 714 := by
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := 0) (f := 714) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 714) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 42) (f := 672) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 672) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 154) (f := 518) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap
  refine (Patch.sequenceCons (d := 0) (f := 518) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 322) (f := 196) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 196) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 196) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 (count*714)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredInverseScheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatch n _ first)).castSaving (by omega)

def eeaReversePatch (n start : Nat) :
    Patch (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 1156680 := by
  unfold measuredEEAReverseProgram
  exact reverseSchedulePatch n 1620 1 start

def reverseWrapperPatch (n start : Nat) :
    Patch (measuredReverseWrapperProgram n start).2 1156680 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (eeaReversePatch n _) (Patch.refl _)).castSaving (by omega)

def Patch.relabelCompiled {n start d} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.relabelCompiled e p).2 d :=
  hp.relabel e

def forwardDataPatch (n start : Nat) : Patch (measuredForwardDataBankProgram n start).2 1156680 := by
  unfold measuredForwardDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

def reverseDataPatch (n start : Nat) : Patch (measuredReverseDataBankProgram n start).2 1156680 := by
  unfold measuredReverseDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (reverseWrapperPatch n start)

def collectPatch {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hp : ∀ cursor prior, Patch (next cursor prior).2 d) :
    (ws : List Wire) → (start : Nat) → (prior : List (Fin start)) →
      Patch (collectProgram n next ws start prior).2 d
  | [], start, prior => by simpa only [collectProgram] using hp start prior
  | w::ws, start, prior => by
    simp only [collectProgram]
    exact (Patch.measure w (collectPatch next hp ws (start+1) _)).castFinish _

def divisionAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (divisionAfterResetProgram n start prior).2 1156680 := by
  unfold divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1156680) (f := 0) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (reverseDataPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)

def divisionPatch (n start : Nat) : Patch (divisionProgram n start).2 2313360 := by
  unfold divisionProgram
  exact (Patch.appendCompiled (d := 1156680) (f := 1156680) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (wrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (collectPatch _ (divisionAfterResetPatch n) _ _ _)).castSaving (by omega)

def multiplicationCleanupPatch (n start : Nat) :
    Patch (multiplicationCleanupProgram n start).2 1156680 := by
  unfold multiplicationCleanupProgram appendLiteral
  exact (Patch.appendCompiled (d := 0) (f := 1156680) _ _ (Patch.refl _)
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (reverseDataPatch n _) (Patch.refl _)).castSaving (by omega))).castSaving (by omega)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationCorrectionProgram n start prior).2 1156680 := by
  unfold multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 1156680)
    (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+1156680=1156680 by omega)

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationAfterResetProgram n start prior).2 2313360 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1156680) (f := 1156680) _ _
    ((Patch.appendCompiled (d := 1156680) (f := 0) _ _ (forwardDataPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

def multiplicationPatch (n start : Nat) : Patch (multiplicationProgram n start).2 2313360 := by
  unfold multiplicationProgram
  exact (Patch.appendCompiled (d := 0) (f := 2313360) _ _ (Patch.refl _)
    (collectPatch _ (multiplicationAfterResetPatch n) _ _ _)).castSaving (by omega)




end
end ShorECDLP.Entrant.Optimization
namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram ShorECDLP.Entrant.ZeroAdaptive.adaptiveCoordinateProgram ShorECDLP.Entrant.ZeroAdaptive.zDivisionProgram ShorECDLP.Entrant.ZeroAdaptive.zMultiplicationProgram
  Single.axis Rounded.entry

def zeroDivisionPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.ZeroAdaptive.zDivisionProgram n start).2 2313360 := by
  unfold ShorECDLP.Entrant.ZeroAdaptive.zDivisionProgram
  dsimp only
  refine (Patch.appendCompiled (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine Patch.prependCompiled _ _ ?_
  exact (Patch.appendCompiled (d := 2313360) (f := 0) _ _
    (divisionPatch n _) (Patch.refl _)).castSaving (by omega)

def zeroMultiplicationPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.ZeroAdaptive.zMultiplicationProgram n start).2 2313360 := by
  unfold ShorECDLP.Entrant.ZeroAdaptive.zMultiplicationProgram
  dsimp only
  refine (Patch.appendCompiled (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine Patch.prependCompiled _ _ ?_
  exact (Patch.appendCompiled (d := 2313360) (f := 0) _ _
    (multiplicationPatch n _) (Patch.refl _)).castSaving (by omega)

def coordinatePatch (start : Nat) : Patch (ShorECDLP.Entrant.ZeroAdaptive.adaptiveCoordinateProgram start).2 4626720 := by
  unfold ShorECDLP.Entrant.ZeroAdaptive.adaptiveCoordinateProgram ShorECDLP.Entrant.ZeroAdaptive.adaptiveCoordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 4626720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 4626720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 2313360) (f := 2313360) _ _ (zeroDivisionPatch 32768 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2313360) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 2313360) (f := 0) _ _ (zeroMultiplicationPatch 32768 _) (Patch.refl _)).castSaving (by omega)

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 4626720 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 4626720) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 4626720 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 4626720 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 4626720 := by
  unfold Single.signedWindow
  exact (actualPatch start).reindex (Single.signedRow w)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def leftPatches : List (PatchedWindow 901120) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,4626720,signedPatch w⟩)
def rightPatches : List (PatchedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,4626720,signedPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 74027520 := by
  simp [leftPatches, Single.leftSigned]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 64774080 := by
  simp [rightPatches, Single.rightSigned]

def axisPatch {n} : (ps : List (PatchedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    Patch (Single.axis (ps.map PatchedWindow.source) start prior) ((ps.map PatchedWindow.saving).sum)
  | [], _, _ => Patch.refl _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine Patch.castFinish ?_ _
    refine Patch.castSaving (Patch.append (f := (ps.map PatchedWindow.saving).sum) (preparePatch _ (p.patch start)) ?_) (by omega)
    exact (Patch.append (Patch.refl _) (axisPatch ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castSaving (by omega)

def axisPatchFor {n} (ps : List (PatchedWindow n)) (ws : List (Single.Window n))
    (he : ps.map PatchedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    Patch (Single.axis ws start prior) ((ps.map PatchedWindow.saving).sum) := by
  subst ws
  exact axisPatch ps start prior

def Patch.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : Patch p dl) (hq : Patch q dr) :
    Patch (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact Patch.gate _ ((Patch.append hp ((Patch.append hq (Patch.gate _ (Patch.refl _))).castSaving (Nat.add_zero dr))).castFinish h)

def trialPatch (start : Nat) : Patch (Single.trial start) 138801600 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 138801600 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Rounded.entry.program 138801600 := by
  unfold Rounded.entry Rounded.program
  exact Patch.fixedEntry Single.mixedCoefficientAt _
    ((Patch.append programPatch (Patch.refl Rounded.readout)).castSaving (by omega))
end
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Parent
open Challenge
noncomputable def entry : StraightEntry := Optimization.replaceEntry Rounded.entry Optimization.entryPatch.program
def layout : DecodeLayout := Rounded.layout
def bounds : Bounds := ⟨Rounded.bounds.qubits, Rounded.bounds.tModel - 138801600, Rounded.bounds.measurements⟩
theorem certificate : Certificate officialLimits layout entry bounds :=
  Optimization.replacement_certificate Rounded.certificate Optimization.entryPatch.drops Optimization.entryPatch.rewrites
end ShorECDLP.Entrant.Parent
end


section

/-! Measurement-assisted Toffoli synthesis using a reusable clean ancillary wire.
The temporary AND follows Gidney, Quantum 2, 74 (2018). Its four T rotations and
one S rotation cost five in the challenge's P-count model. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Paper2607_13816
noncomputable section
set_option maxHeartbeats 200000

attribute [local irreducible] Quantum.applyGate Quantum.run Quantum.ket
set_option linter.unusedSimpArgs false


private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]
private theorem upd_self (s : BasisState) (q : Wire) : s[q ↦ s q] = s := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

private theorem phase_square (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir (k+1)^2 = phaseCoeff dir k := by
  rw [phaseCoeff, ← Complex.exp_nat_mul, phaseCoeff]
  congr 1
  cases dir <;> simp only [phaseAngle, pow_succ] <;> push_cast <;> field_simp

private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

private theorem phase_two_inverse : phaseCoeff .inverse 2 = -Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

/-- Diagonal phase on the XOR of a control and target. -/
def xorPhase (dir : PhaseDir) (a q : Wire) : Circuit :=
  [.CX a q, .P dir 3 q, .CX a q]

private theorem xorPhase_ket (dir : PhaseDir) (a q : Wire) (ha : a ≠ q)
    (s : BasisState) :
    Quantum.run (xorPhase dir a q) (ket s) =
      (if s q ^^ s a then phaseCoeff dir 3 else 1) • ket s := by
  simp only [xorPhase, Quantum.run_cons, Quantum.run_nil, applyGate_CX_ket,
    applyGate_P_ket, map_smul, upd_same, upd_other _ _ _ ha,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self]

/-- Four diagonal parity phases; additional Clifford CNOTs keep the proof modular. -/
def parityPhase (a b q : Wire) : Circuit :=
  [.P .forward 3 q] ++ xorPhase .inverse a q ++
    [.CX a q] ++ xorPhase .forward b q ++ [.CX a q] ++ xorPhase .inverse b q

private theorem parityPhase_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) :
    Quantum.run (parityPhase a b q) (ket s) =
      (if s a && s b then (if s q then Complex.I else -Complex.I) else 1) • ket s := by
  have hmul := phaseCoeff_mul_adjoint .forward 3
  have himul := phaseCoeff_adjoint_mul .forward 3
  have hsq := phase_square .forward 2
  have hisq := phase_square .inverse 2
  rw [phase_two] at hsq
  rw [phase_two_inverse] at hisq
  change phaseCoeff .forward 3 * phaseCoeff .inverse 3 = 1 at hmul
  change phaseCoeff .inverse 3 * phaseCoeff .forward 3 = 1 at himul
  simp only [parityPhase, Quantum.run_append, Quantum.run_singleton,
    applyGate_P_ket, applyGate_CX_ket, map_smul, xorPhase_ket _ a q ha,
    xorPhase_ket _ b q hb, upd_same, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self, smul_smul]
  cases ha' : s a <;> cases hb' : s b <;> cases hq : s q <;>
    simp only [ha', hb', hq, Bool.false_and, Bool.true_and,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, mul_one, one_mul,
      ← pow_two, hsq, hisq, mul_assoc, hmul, himul, one_pow]

/-- Exact temporary AND on a clean target; S is counted as one P rotation. -/
def andCompute (a b q : Wire) : Circuit :=
  [.H q] ++ parityPhase a b q ++ [.H q, .P .forward 2 q]

private theorem invSqrtTwo_square :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℂ) := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

/-- No data-dependent phase remains on the clean-target subspace. -/
theorem andCompute_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) (hq : s q = false) :
    Quantum.run (andCompute a b q) (ket s) = ket (s[q ↦ s a && s b]) := by
  have hs : s[q ↦ false] = s := by simpa only [hq] using upd_self s q
  have hsq : ((↑(Real.sqrt 2) : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
    simpa [pow_two] using invSqrtTwo_square
  simp only [andCompute, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, map_add, map_smul,
    parityPhase_ket a b q ha hb, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_same, hq, Bool.false_eq_true, if_false, if_true, mul_one,
    applyGate_P_ket, phase_two, upd_twice]
  cases ha' : s a <;> cases hb' : s b <;>
    simp [ha', hb', hs, hq, smul_add, smul_smul, mul_add, add_mul,
      invSqrtTwo_square, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [hsq, Complex.I_sq]

/-- One branch of AND-compute, target update, and corrected X erasure. -/
def toffoliBranch (a b t q : Wire) (outcome : Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (if outcome then controlledZ a b else [])).comp
    ((xResetKraus q outcome).comp (Quantum.run (andCompute a b q ++ [.CX q t])))

private theorem reset_after_update (s : BasisState) (q t : Wire) (hqt : q ≠ t)
    (hq : s q = false) (v z : Bool) :
    s[q ↦ v][t ↦ z][q ↦ false] = s[t ↦ z] := by
  funext w
  by_cases hwq : w = q <;> by_cases hwt : w = t <;> simp_all [upd]

/-- Both outcomes have the same data-independent amplitude, with no residual phase. -/
theorem toffoliBranch_ket (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (s : BasisState) (hq : s q = false) :
    toffoliBranch a b t q outcome (ket s) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) (ket s) := by
  simp only [toffoliBranch, LinearMap.comp_apply, Quantum.run_append,
    andCompute_ket a b q haq hbq s hq, Quantum.run_singleton, applyGate_CX_ket,
    upd_same, upd_other _ _ _ (Ne.symm hqt), xResetKraus_ket,
    upd_other _ _ _ hqt, reset_after_update s q t hqt hq, map_smul,
    applyGate_CCX_ket, xResetCoeff]
  cases outcome <;> simp only [Bool.false_eq_true, if_false, if_true,
    Quantum.run_nil, run_controlledZ_ket a b _ hab,
    upd_other _ _ _ hat, upd_other _ _ _ hbt]
  all_goals cases ha : s a <;> cases hb : s b <;>
    simp [ha, hb, smul_smul]

/-- The primitive also holds on arbitrary supported superpositions. -/
theorem toffoliBranch_supported (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    toffoliBranch a b t q outcome psi =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) psi := by
  have h : BranchCoherentOn (applyGate (.CCX a b t)) (fun s => s q = false)
      ⟨[], toffoliBranch a b t q outcome⟩ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) :=
    fun s hs => toffoliBranch_ket a b t q outcome hab haq hbq hat hbt hqt s hs
  exact h.on_supported hpsi

/-- Every rotation, including S, is charged. -/
theorem andCompute_tCount (a b q : Wire) : ShorECDLP.tCount (andCompute a b q) = 5 := by
  rfl

theorem andCompute_wellFormed (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q) :
    CircuitWellFormed (andCompute a b q) := by
  simp [andCompute, parityPhase, xorPhase, CircuitWellFormed, Gate.WellFormed, ha, hb]

end
end ShorECDLP.Entrant.AndGadget
end

section

/-! A static record-preserving compiler for measurement-assisted Toffoli gates. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The compiler records the location of every original measurement. -/
structure Lowered (n oldFinish start : Nat) where
  finish : Nat
  program : Straight n start finish
  records : Fin oldFinish → Fin finish

/-- Execute a fixed literal prefix. -/
def literals {n s e : Nat} (gs : Circuit) (next : Straight n s e) : Straight n s e :=
  gs.foldr (fun g tail => .gate (.literal g) tail) next

/-- The selected phase correction uses Clifford gates only. -/
def toffoliPrefix {n s e : Nat} (a b target scratch : Wire)
    (next : Straight n (s+1) e) : Straight n s e :=
  literals (andCompute a b scratch ++ [.CX scratch target])
    (.measure scratch
      (.recordGate (Fin.last s) true (.H b)
        (.recordGate (Fin.last s) true (.CX a b)
          (.recordGate (Fin.last s) true (.H b) next))))

/-- Only unconditional literal Toffolis are replaced. Original conditional gates
and their record references remain exactly represented. -/
def lower {n oldStart oldFinish : Nat} (scratch : Wire)
    (p : Straight n oldStart oldFinish) (start : Nat)
    (records : Fin oldStart → Fin start) : Lowered n oldFinish start :=
  match p with
  | .done => ⟨start, .done, records⟩
  | .gate (.literal (.CCX a b t)) next =>
      let r := lower scratch next (start+1) (fun i => (records i).castSucc)
      ⟨r.finish, toffoliPrefix a b t scratch r.program, r.records⟩
  | .gate g next =>
      let r := lower scratch next start records
      ⟨r.finish, .gate g r.program, r.records⟩
  | .recordGate i v g next =>
      let r := lower scratch next start records
      ⟨r.finish, .recordGate (records i) v g r.program, r.records⟩
  | .measure w next =>
      let r := lower scratch next (start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      ⟨r.finish, .measure w r.program, r.records⟩

/-- Number of new records, independent of all constant values and outcomes. -/
def added {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal (.CCX _ _ _)) next => 1 + added next
  | .gate _ next => added next
  | .recordGate _ _ _ next => added next
  | .measure _ next => added next

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Backward evaluation against a predicate on the complete record. -/
def expectation {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) : ℝ :=
  match p with
  | .done => if accept history then normSq psi else 0
  | .gate g next => expectation read next history (Quantum.run (g.instantiate read) psi) accept
  | .recordGate i v g next => expectation read next history
      (Quantum.run (if history i = v then [g] else []) psi) accept
  | .measure w next =>
      expectation read next (Fin.lastCases false history) (xResetKraus w false psi) accept +
      expectation read next (Fin.lastCases true history) (xResetKraus w true psi) accept

/-- The static record cost of an appended program is additive. -/
theorem added_append {n s m e : Nat} (p : Straight n s m) (q : Straight n m e) :
    added (p.append q) = added p + added q := by
  induction p with
  | done => simp [Straight.append, added]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;> simp [Straight.append, added, ih, Nat.add_assoc]
      | whenBit r v g => simp [Straight.append, added, ih]
  | recordGate i v g p ih => exact ih q
  | measure w p ih => exact ih q

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The new cursor is the old remaining record count plus one per lowered gate. -/
theorem lower_finish {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower scratch p start records).finish + s = start + e + added p := by
  induction p generalizing start with
  | done => simp [lower, added, Nat.add_comm]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower, added]
          all_goals have h := ih (start := start) records
          all_goals try omega
          exact (by have h := ih (start := start+1) (fun i => (records i).castSucc); omega)
      | whenBit r v g => exact ih start records
  | recordGate i v g p ih => exact ih start records
  | measure w p ih =>
      simp only [lower, added]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      omega

/-- Old references into the initial prefix keep their values. -/
theorem lower_initial {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (i : Fin s) :
    ((lower scratch p start records).records (i.castLE p.cursor_mono)).val = (records i).val := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower]
          all_goals apply ih
      | whenBit r v g => exact ih start records i
  | recordGate j v g p ih => exact ih start records i
  | measure w p ih =>
      simp only [lower]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) i.castSucc
      simpa only [Fin.castLE, Fin.val_castSucc, Fin.lastCases_castSucc] using h

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem state_normSq_smul (c : ℂ) (psi : State) :
    normSq (c • psi) = Complex.normSq c * normSq psi := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

theorem expectation_smul {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (c : ℂ) :
    expectation read p history (c • psi) accept =
      Complex.normSq c * expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp only [expectation]; split <;> simp [state_normSq_smul]
  | gate g p ih => simp only [expectation, map_smul, ih]
  | recordGate i v g p ih => simp only [expectation, map_smul, ih]
  | measure w p ih => simp only [expectation, map_smul, ih, mul_add]

theorem expectation_literals {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read (literals gs p) history psi accept =
      expectation read p history (Quantum.run gs psi) accept := by
  induction gs generalizing psi with
  | nil => simp [literals, Quantum.run_nil]
  | cons g gs ih =>
      simp only [literals, List.foldr_cons, expectation, TemplateGate.instantiate,
        Quantum.run_nil, Quantum.run_cons]
      exact ih (applyGate g psi)

theorem expectation_toffoliPrefix {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool)
    (psi : State) (accept : (Fin e → Bool) → Bool) :
    expectation read (toffoliPrefix a b t q p) history psi accept =
      expectation read p (Fin.lastCases false history) (toffoliBranch a b t q false psi) accept +
      expectation read p (Fin.lastCases true history) (toffoliBranch a b t q true psi) accept := by
  simp only [toffoliPrefix, expectation_literals, expectation, Fin.lastCases_last,
    Bool.false_eq_true, if_false, if_true, Quantum.run_nil,
    toffoliBranch, LinearMap.comp_apply, controlledZ,
    Quantum.run_cons, Quantum.run_nil]

/-- The source never accesses the new ancillary wire. -/
def Fresh {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => q ∉ gateWires g ∧ Fresh q p
  | .gate (.whenBit _ _ g) p => q ∉ gateWires g ∧ Fresh q p
  | .recordGate _ _ g p => q ∉ gateWires g ∧ Fresh q p
  | .measure w p => q ≠ w ∧ Fresh q p

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem half_amplitude :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℝ) := by
  simp only [Complex.normSq_ofReal]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- Compilation preserves every predicate on the original measurement record. -/
theorem lower_expectation {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (newHistory : Fin start → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool)
    (hmap : newHistory ∘ records = history) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    expectation read (lower q p start records).program newHistory psi
        (fun h => accept (h ∘ (lower q p start records).records)) =
      expectation read p history psi accept := by
  induction p generalizing start psi with
  | done => simp only [lower, expectation, hmap]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              obtain ⟨hf, htail⟩ := hf
              have hqs : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hwf.1
              have hp : SupportedOn (fun s => s q = false) (applyGate (.CCX a b t) psi) := by
                simpa only [Quantum.run_singleton] using gate_frame q ([.CCX a b t] : Circuit)
                  (by simpa [circuitWires] using hf) psi hpsi
              simp only [lower, expectation_toffoliPrefix]
              rw [toffoliBranch_supported a b t q false hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  toffoliBranch_supported a b t q true hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  expectation_smul, expectation_smul]
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              rw [ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases false newHistory) _ accept (hm false) htail hwf.2 hp,
                  ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases true newHistory) _ accept (hm true) htail hwf.2 hp]
              simp only [expectation, TemplateGate.instantiate, Quantum.run_singleton, half_amplitude]
              ring
          | X t | H t | CX a t | P dir k t =>
              simp only [lower, expectation]
              apply ih start records history newHistory _ accept hmap hf.2 hwf.2
              apply gate_frame q _ ?_ psi hpsi
              simpa [TemplateGate.instantiate, circuitWires] using hf.1
      | whenBit r v g =>
          simp only [lower, expectation]
          apply ih start records history newHistory _ accept hmap hf.2 hwf.2
          apply gate_frame q _ ?_ psi hpsi
          simp only [TemplateGate.instantiate]
          split
          · simpa [circuitWires] using hf.1
          · simp [circuitWires]
  | recordGate i v g p ih =>
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, expectation, hm]
      apply ih start records history newHistory _ accept hmap hf.2 hwf.2
      apply gate_frame q _ ?_ psi hpsi
      split
      · simpa [circuitWires] using hf.1
      · simp [circuitWires]
  | measure w p ih =>
      simp only [lower, expectation]
      congr 1
      all_goals
        apply ih (start+1)
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) _ _ _ accept ?_ hf.2 hwf
          (reset_frame q w hf.1 _ psi hpsi)
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
set_option linter.unusedSimpArgs false

theorem literals_slots {n s e : Nat} (gs : Circuit) (p : Straight n s e) :
    (literals gs p).gateSlots = gs.length + p.gateSlots := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
      change 1 + (literals gs p).gateSlots = (gs.length+1) + p.gateSlots
      rw [ih]
      omega

theorem toffoliPrefix_slots {n s e : Nat} (a b t q : Wire) (p : Straight n (s+1) e) :
    (toffoliPrefix a b t q p).gateSlots = 19 + p.gateSlots := by
  simp [toffoliPrefix, literals_slots, andCompute, parityPhase, xorPhase, Straight.gateSlots]
  omega

theorem lower_slots {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower q p start records).program.gateSlots = p.gateSlots + 18 * added p := by
  induction p generalizing start with
  | done => simp [lower, added, Straight.gateSlots]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;>
          simp [lower, added, Straight.gateSlots, toffoliPrefix_slots, ih] <;> omega
      | whenBit r v g => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | measure w p ih => exact ih _ _

theorem literals_wellFormed {n s e : Nat} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp), ih (fun k hk => hg k (by simp [hk]))⟩

theorem lower_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (hf : Fresh q p) (hp : p.WellFormed) :
    (lower q p start records).program.WellFormed := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hq : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf.1
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hp.1
              apply literals_wellFormed
              · exact (circuitWellFormed_append _ _).mpr
                  ⟨andCompute_wellFormed a b q hq.1.symm hq.2.1.symm,
                    by simpa [CircuitWellFormed, Gate.WellFormed] using hq.2.2⟩
              · exact ⟨trivial, hw.1, trivial, ih _ _ hf.2 hp.2⟩
          | X t | H t | CX a t | P dir k t => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
      | whenBit r v g => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | measure w p ih => exact ih _ _ hf.2 hp

theorem literals_t {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := by
  induction gs with
  | nil => simp [literals, ShorECDLP.tCount]
  | cons g gs ih =>
      change ShorECDLP.tCount [g] + ((literals gs p).instantiate read history).tCount = _
      rw [ih]
      simp [ShorECDLP.tCount, Nat.add_assoc]

theorem toffoliPrefix_t {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool) :
    ((toffoliPrefix a b t q p).instantiate read history).tCount =
      5 + max (p.instantiate read (Fin.lastCases false history)).tCount
        (p.instantiate read (Fin.lastCases true history)).tCount := by
  simp [toffoliPrefix, literals_t, andCompute, parityPhase, xorPhase,
    Straight.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost]

/-- Exact T reduction, including arbitrary original record-controlled gates. -/
theorem lower_t {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (newHistory : Fin start → Bool)
    (hmap : newHistory ∘ records = history) :
    ((lower q p start records).program.instantiate read newHistory).tCount + 2 * added p =
      (p.instantiate read history).tCount := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              have h0 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases false newHistory) (hm false)
              have h1 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases true newHistory) (hm true)
              simp only [lower, toffoliPrefix_t, added, Straight.instantiate,
                TemplateGate.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost] at *
              omega
          | X t | H t | CX a t | P dir k t =>
              have h := ih start records history newHistory hmap
              simp only [lower, added, Straight.instantiate, TemplateGate.instantiate,
                AdaptiveCircuit.tCount] at *
              omega
      | whenBit r v g =>
          have h := ih start records history newHistory hmap
          simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
          omega
  | recordGate i v g p ih =>
      have h := ih start records history newHistory hmap
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount, hm] at *
      omega
  | measure w p ih =>
      have hm (outcome : Bool) : (Fin.lastCases outcome newHistory) ∘
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) =
          Fin.lastCases outcome history := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]
      have h0 := ih (start+1) _ (Fin.lastCases false history) (Fin.lastCases false newHistory) (hm false)
      have h1 := ih (start+1) _ (Fin.lastCases true history) (Fin.lastCases true newHistory) (hm true)
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
      omega

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private def prependBranch (outcome : Option Bool) (before : State →ₗ[ℂ] State)
    (branch : InstrumentBranch) : InstrumentBranch :=
  ⟨outcome.toList ++ branch.history, branch.kraus.comp before⟩
private theorem run_unitary (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (prependBranch none (Quantum.run gs)) := rfl
private theorem run_measure (q : Wire) (a b : AdaptiveCircuit) :
    (AdaptiveCircuit.xMeasureReset q a b).run =
      a.run.map (prependBranch (some false) (xResetKraus q false)) ++
      b.run.map (prependBranch (some true) (xResetKraus q true)) := rfl

/-- Sum probability mass selected by an arbitrary transcript predicate. -/
def selectedMass (I : Instrument) (psi : State) (accept : List Bool → Bool) : ℝ :=
  (I.map (fun b => if accept b.history then normSq (b.kraus psi) else 0)).sum

theorem selectedMass_filter (I : Instrument) (psi : State) (accept : List Bool → Bool) :
    selectedMass I psi accept = Instrument.bornMass (I.filter (fun b => accept b.history)) psi := by
  induction I with
  | nil => rfl
  | cons b I ih =>
      cases hb : accept b.history <;> simp [selectedMass, Instrument.bornMass, hb] at * <;> exact ih

private theorem selectedMass_prefix (I : Instrument) (outcome : Option Bool)
    (before : State →ₗ[ℂ] State) (psi : State) (accept : List Bool → Bool) :
    selectedMass (I.map (prependBranch outcome before)) psi accept =
      selectedMass I (before psi) (fun xs => accept (outcome.toList ++ xs)) := by
  simp [selectedMass, prependBranch, List.map_map, Function.comp_def, LinearMap.comp_apply]

/-- Read the initial prefix followed by the newly emitted record. -/
def fullHistory {s : Nat} (e : Nat) (history : Fin s → Bool) (tail : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ tail).getD i.val false

private theorem fullHistory_nil {s : Nat} (history : Fin s → Bool) :
    fullHistory s history List.nil = history := by
  funext i
  simp [fullHistory, i.isLt]

private theorem fullHistory_cons {s e : Nat} (history : Fin s → Bool) (b : Bool) (tail : List Bool) :
    fullHistory e history (b :: tail) = fullHistory e (Fin.lastCases b history) tail := by
  unfold fullHistory
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append,
    List.append_assoc, List.singleton_append]

/-- The recursive expectation is precisely the protected instrument Born mass. -/
theorem expectation_selectedMass {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read p history psi accept =
      selectedMass (p.instantiate read history).run psi (fun xs => accept (fullHistory e history xs)) := by
  induction p generalizing psi with
  | done => simp [expectation, Straight.instantiate, AdaptiveCircuit.run,
      selectedMass, fullHistory_nil]
  | gate g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | recordGate i v g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | measure w p ih =>
      simp only [expectation, Straight.instantiate, run_measure]
      rw [show ∀ a b : Instrument, selectedMass (a ++ b) psi
          (fun xs => accept (fullHistory _ history xs)) =
          selectedMass a psi (fun xs => accept (fullHistory _ history xs)) +
          selectedMass b psi (fun xs => accept (fullHistory _ history xs)) by
        intros; simp [selectedMass]]
      simp only [selectedMass_prefix, Option.toList_some, List.singleton_append, fullHistory_cons]
      rw [ih, ih]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

/-- Invalid old positions remain invalid after record remapping. -/
def redirect {e f : Nat} (records : Fin e → Fin f) (i : Nat) : Nat :=
  if h : i < e then (records ⟨i,h⟩).val else f

def redirectedLayout {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout) : DecodeLayout where
  kind := layout.kind
  params := layout.params
  trials := layout.trials.map (fun t => ⟨t.left.map (redirect records), t.right.map (redirect records)⟩)
  trials_le := by simpa using layout.trials_le

private theorem redirect_get {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (i : Nat) :
    xs[redirect records i]? =
      (List.ofFn (fun j : Fin e => xs.getD (records j).val false))[i]? := by
  by_cases hi : i < e
  · have hr : (records ⟨i,hi⟩).val < xs.length := by simp [hlen]
    simp [redirect, hi, List.getElem?_eq_getElem hr]
  · have he : e ≤ i := by omega
    simp [redirect, hi, List.getElem?_eq_none (by omega : xs.length ≤ f)]

theorem readWord_redirect {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (positions : List Nat) :
    readWord xs (positions.map (redirect records)) =
      readWord (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) positions := by
  induction positions with
  | nil => rfl
  | cons i positions ih => simp only [List.map_cons, readWord, redirect_get records xs hlen, ih]

theorem candidates_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (xs : List Bool) (hlen : xs.length = f) :
    candidates (redirectedLayout records layout) xs =
      candidates layout (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  simp only [candidates, redirectedLayout, List.flatMap_map]
  apply List.flatMap_congr
  intro t ht
  cases layout.kind <;>
    simp [decodeTrial, trialCandidates, Vector.toList_map, readWord_redirect records xs hlen]

theorem verified_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (Q : Secp256k1.Point) (xs : List Bool) (hlen : xs.length = f) :
    verifiedCandidate (redirectedLayout records layout) Q xs =
      verifiedCandidate layout Q (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  unfold verifiedCandidate
  rw [candidates_redirect records layout xs hlen]

private theorem ofFn_fullHistory {e : Nat} (xs : List Bool) (hlen : xs.length = e) :
    List.ofFn (fullHistory e Fin.elim0 xs) = xs := by
  subst e
  change List.ofFn (fun i : Fin xs.length => xs.getD i.val false) = xs
  simpa only [List.getD_eq_getElem xs false (Fin.isLt _)] using List.ofFn_getElem xs

/-- Bridge the finite-record predicate to the protected decoder and Born sum. -/
theorem expectation_verified {n e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n 0 e) (layout : DecodeLayout) (Q : Secp256k1.Point) (psi : State) :
    expectation read p Fin.elim0 psi
      (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome) =
      Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [expectation_selectedMass, ← selectedMass_filter (p.instantiate read Fin.elim0).run psi
    (fun xs => (verifiedCandidate layout Q xs).isSome)]
  unfold selectedMass
  congr 1
  apply List.map_congr_left
  intro b hb
  have hl : b.history.length = e := by
    simpa using straight_history_length p read Fin.elim0 b hb
  change (if (verifiedCandidate layout Q (List.ofFn (fullHistory e Fin.elim0 b.history))).isSome then _ else _) = _
  rw [ofFn_fullHistory b.history hl]

/-- The remapped protected decoder has exactly the original success probability. -/
theorem lower_verified {n e : Nat} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass
      (((lower q p 0 Fin.elim0).program.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
          Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified]
  have he : (fun h => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
        Q (List.ofFn h)).isSome) =
      (fun h => (verifiedCandidate layout Q (List.ofFn (h ∘ (lower q p 0 Fin.elim0).records))).isSome) := by
    funext h
    rw [verified_redirect _ _ _ _ List.length_ofFn]
    simp [Function.comp_def]
  rw [he]
  exact lower_expectation q p 0 Fin.elim0 read Fin.elim0 Fin.elim0 psi (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome)
    (by funext i; exact Fin.elim0 i) hf hwf hpsi

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- Static support, including every optional gate slot. -/
def Within {n s e : Nat} (ws : List Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => gateWires g ⊆ ws ∧ Within ws p
  | .gate (.whenBit _ _ g) p => gateWires g ⊆ ws ∧ Within ws p
  | .recordGate _ _ g p => gateWires g ⊆ ws ∧ Within ws p
  | .measure w p => w ∈ ws ∧ Within ws p

theorem Within.fresh {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (q : Wire) (hq : q ∉ ws) : Fresh q p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g <;> exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | recordGate i v g p ih => exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | measure w p ih => exact ⟨fun he => hq (he ▸ h.1), ih h.2⟩

theorem Within.mono {n s e : Nat} {ws vs : List Wire} {p : Straight n s e}
    (h : Within ws p) (hs : ws ⊆ vs) : Within vs p := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨h.1.trans hs, ih h.2⟩
  | recordGate i v g p ih => exact ⟨h.1.trans hs, ih h.2⟩
  | measure w p ih => exact ⟨hs h.1, ih h.2⟩

theorem Within.instantiate {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ ws := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.wires]
  | gate g p ih =>
      cases g with
      | literal g => simpa [Straight.instantiate, TemplateGate.instantiate,
          AdaptiveCircuit.wires, circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      | whenBit r v g =>
          simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires]
          split
          · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
          · simpa [circuitWires] using ih h.2 history
  | recordGate i v g p ih =>
      simp only [Straight.instantiate, AdaptiveCircuit.wires]
      split
      · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      · simpa [circuitWires] using ih h.2 history
  | measure w p ih =>
      exact List.cons_subset.mpr ⟨h.1, List.append_subset.mpr ⟨ih h.2 _, ih h.2 _⟩⟩

theorem within_of_instantiate {n s e : Nat} (p : Straight n s e) (ws : List Wire)
    (h : ∀ read history, (p.instantiate read history).wires ⊆ ws) : Within ws p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          constructor
          · intro w hw
            exact h (fun _ => false) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
      | whenBit r v g =>
          constructor
          · intro w hw
            exact h (fun _ => v) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
  | recordGate i v g p ih =>
      constructor
      · intro w hw
        exact h (fun _ => false) (fun _ => v)
          (by simp [Straight.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
      · apply ih
        intro read history w hw
        exact h read history (List.mem_append_right _ hw)
  | @measure s e w p ih =>
      constructor
      · exact h (fun _ => false) (fun _ => false) (List.mem_cons_self)
      · apply ih
        intro read history v hv
        let before : Fin s → Bool := fun i => history i.castSucc
        have he : Fin.lastCases (history (Fin.last s)) before = history := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [before]
        rw [← he] at hv
        apply h read before
        cases hb : history (Fin.last s) <;>
          simp only [hb] at hv <;>
          simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append]
        · exact Or.inr (Or.inl hv)
        · exact Or.inr (Or.inr hv)

theorem within_literals {n s e : Nat} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
      have hh : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by
        simpa only [circuitWires, List.flatMap_cons, List.append_subset] using hg
      exact ⟨hh.1, ih hh.2⟩

theorem lower_within {n s e : Nat} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) (start : Nat) (records : Fin s → Fin start) :
    Within (q :: ws) (lower q p start records).program := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hs : a ∈ ws ∧ b ∈ ws ∧ t ∈ ws := by simpa [gateWires] using hp.1
              apply within_literals
              · simp [andCompute, parityPhase, xorPhase, circuitWires, gateWires,
                  List.cons_subset, hs.1, hs.2.1, hs.2.2]
              · exact ⟨by simp, by simp [gateWires, hs.2.1],
                  by simp [gateWires, hs.1, hs.2.1], by simp [gateWires, hs.2.1], ih hp.2 _ _⟩
          | X t | H t | CX a t | P dir k t =>
              exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
      | whenBit r v g => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | recordGate i v g p ih => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | measure w p ih => exact ⟨List.mem_cons_of_mem _ hp.1, ih hp.2 _ _⟩

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Package the transformed straight program with unchanged public coefficients. -/
def lowerEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := (lower q entry.program 0 Fin.elim0).finish
  program := (lower q entry.program 0 Fin.elim0).program

def lowerLayout (q : Wire) (entry : StraightEntry) (layout : DecodeLayout) : DecodeLayout :=
  redirectedLayout (lower q entry.program 0 Fin.elim0).records layout

/-- Certificate transport uses only a proved count of eligible literal Toffolis. -/
theorem lower_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 18 * added entry.program ≤ limits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ limits.measurements)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel ≤ newBounds.tModel + 2 * added entry.program)
    (hm : entry.finalCursor + added entry.program ≤ newBounds.measurements) :
    Certificate limits (lowerLayout q entry layout) (lowerEntry q entry) newBounds where
  gateBudget := by simpa only [lowerEntry, lower_slots] using hslots
  recordBudget := by
    have h := lower_finish q entry.program 0 Fin.elim0
    simp only [Nat.add_zero, Nat.zero_add] at h
    simpa only [lowerEntry] using h.le.trans hrecords
  tableBudget := cert.tableBudget
  candidateBudget := by simpa [lowerLayout, redirectedLayout] using cert.candidateBudget
  wellFormed := lower_wellFormed q entry.program 0 Fin.elim0 (hs.fresh q hq) cert.wellFormed
  resources := by
    intro Q
    have hsup := (lower_within q entry.program ws hs 0 Fin.elim0).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((lowerEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((lowerEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := lower_t q entry.program 0 Fin.elim0 (readConstant entry.coefficients.get Q)
      Fin.elim0 Fin.elim0 (by funext i; exact Fin.elim0 i)
    have hto := (cert.resources Q).2.1
    have hmc := (lower q entry.program 0 Fin.elim0).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hfinish := lower_finish q entry.program 0 Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      omega
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q entry.program 0 Fin.elim0).records layout)
          Q b.history).isSome)) (ket zeroBasisState)
    rw [lower_verified q entry.program _ layout Q _ (hs.fresh q hq) cert.wellFormed
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem added_cast {n s e f} (p : Straight n s e) (h : e=f) :
    added (ChallengeMigration.castFinish h p) = added p := by subst f; rfl

theorem added_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) :
    added (relabelStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight, relabelTemplateGate, Gate.relabel, added]
    | whenBit r v g => simp_all [relabelStraight, relabelTemplateGate, added]
  | recordGate => simp_all [relabelStraight, added]
  | measure => simp_all [relabelStraight, added]

theorem added_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    added (reindexStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, added]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, added]
  | recordGate => simp_all [reindexStraight, added]
  | measure => simp_all [reindexStraight, added]

theorem added_shift {n s e} (p : Straight n s e) (offset : Nat) :
    added (shiftStraight offset p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [shiftStraight, added]
    | whenBit r v g => simp_all [shiftStraight, added]
  | recordGate => simp_all [shiftStraight, added]
  | measure => simp_all [shiftStraight, added, added_cast]

def ccxCount : Circuit → Nat
  | [] => 0
  | .CCX _ _ _ :: gs => Nat.succ (ccxCount gs)
  | _ :: gs => ccxCount gs

theorem added_literal {n s} (gs : Circuit) :
    added (literalProgram gs : Straight n s s) = ccxCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [literalProgram, gateProgram, added, ccxCount, Nat.add_comm]

def AtLeast {n s e} (p : Straight n s e) (count : Nat) : Prop := count ≤ added p
namespace AtLeast
 theorem zero {n s e} (p : Straight n s e) : AtLeast p 0 := Nat.zero_le _
 theorem castCount {n s e d f} {p : Straight n s e} (hp : AtLeast p d) (h : d=f) : AtLeast p f := h ▸ hp
 theorem castFinish {n s e f d} {p : Straight n s e} (hp : AtLeast p d) (h : e=f) :
     AtLeast (ChallengeMigration.castFinish h p) d := by simpa only [AtLeast, added_cast] using hp
 theorem append {n s m e d f} {p : Straight n s m} {q : Straight n m e}
     (hp : AtLeast p d) (hq : AtLeast q f) : AtLeast (p.append q) (d+f) := by
   unfold AtLeast at *; rw [added_append]; omega
 theorem appendCompiled {n start d f}
     (p : (count : Nat) × Straight n start (start+count))
     (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
     (hp : AtLeast p.2 d) (hq : AtLeast q.2 f) :
     AtLeast (ChallengeMigration.appendCompiled p q).2 (d+f) := by
   unfold ChallengeMigration.appendCompiled
   exact (hp.append hq).castFinish _
 theorem sequenceCons {n start d f} (p : FixedSegment n) (ps : List (FixedSegment n))
     (hp : AtLeast (p start).2 d)
     (hq : AtLeast (sequenceProgram n ps (start+(p start).1)).2 f) :
     AtLeast (sequenceProgram n (p::ps) start).2 (d+f) := appendCompiled (p start) (sequenceProgram n ps (start+(p start).1)) hp hq
 theorem surroundCompiled {n start d} (before after : Circuit)
     (p : (count : Nat) × Straight n start (start+count)) (hp : AtLeast p.2 d) :
     AtLeast (ChallengeMigration.surroundCompiled before after p).2 d := by
   unfold ChallengeMigration.surroundCompiled ChallengeMigration.prependCompiled
   exact ((zero (literalProgram before)).append
     ((appendCompiled p ⟨0,literalProgram after⟩ hp (zero _)).castCount (Nat.add_zero d))).castCount (Nat.zero_add d)
 theorem relabel {n s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Wire ≃ Wire) :
     AtLeast (relabelStraight f p) d := by simpa [AtLeast, added_relabel] using hp
 theorem reindex {n m s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Fin n → Fin m) :
     AtLeast (reindexStraight f p) d := by simpa [AtLeast, added_reindex] using hp
 theorem shift {n s e d} {p : Straight n s e} (hp : AtLeast p d) (offset : Nat) :
     AtLeast (shiftStraight offset p) d := by simpa [AtLeast, added_shift] using hp
end AtLeast

attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
 preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
 measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
 divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
 zeroMultiplicationProgram xNegateProgram coordinateProgram


theorem ccxCount_primitive (gs : Circuit) :
    ccxCount gs = (primitiveResources (.unitary gs .done)).toffoli := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [ccxCount, primitiveResources, gidneyToffoliCount, gidneyGateCount, Nat.add_comm]

theorem aCount (n s : Nat) : AtLeast (literalProgram (blockAForward indexedStepProductionRegisters) : Straight n s s) 906 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  rw [blockAForward259_primitive _ indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift indexedStepProduction_layout.work2_length
    (by decide) (by decide) (by decide)]

theorem fCount (n s : Nat) : AtLeast (literalProgram (blockFForward indexedStepProductionRegisters) : Straight n s s) 566 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  unfold blockFForward
  rw [postShiftUnitary259_primitive _ indexedStepProduction_layout.postShift
    indexedStepProduction_layout.work2_length (by decide)]

theorem stepCount (n start T : Nat) :
    AtLeast (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 1472 := by
  unfold measuredStepProgram measuredStepSegments
  refine (AtLeast.sequenceCons (d := 906) (f := 566) _ _ (aCount n _) ?_)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 566) (f := 0) _ _ (fCount n _) (AtLeast.zero _)).castCount (by omega)

theorem scheduleCount (n : Nat) (count first start : Nat) :
    AtLeast (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*1472) := by
  induction count generalizing first start with
  | zero => exact AtLeast.zero _
  | succ count ih =>
    simp only [measuredScheduleProgram]
    exact (AtLeast.appendCompiled _ _ (stepCount n start first) (ih (first+1) _)).castCount (by omega)

theorem wrapperCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 2384640 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 2384640) (f := 0) _ _ (show AtLeast (measuredEEAForwardProgram n _ indexedStepProductionRegisters).2 2384640 from by unfold measuredEEAForwardProgram; exact scheduleCount n 1620 1 _) (AtLeast.zero _)).castCount (by omega)

theorem divisionCount (n start : Nat) : AtLeast (divisionProgram n start).2 2384640 := by
  unfold divisionProgram
  refine (AtLeast.appendCompiled (d := 2384640) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (wrapperCount n start) (AtLeast.zero _)).castCount (by omega)

theorem zeroDivisionCount (n start : Nat) : AtLeast (zeroDivisionProgram n start).2 2384640 := by
  unfold zeroDivisionProgram
  exact AtLeast.surroundCompiled _ _ _ (divisionCount n start)

theorem coordinateCount (start : Nat) : AtLeast (coordinateProgram start).2 2384640 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons _ _ (zeroDivisionCount 32768 _) (AtLeast.zero _)).castCount (by omega)
end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def residue {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => primitivePhaseCost g + residue p
  | .gate (.whenBit _ _ g) p => tCost g + residue p
  | .recordGate _ _ g p => tCost g + residue p
  | .measure _ p => residue p

@[simp] theorem residue_done {n s : Nat} : residue (Straight.done : Straight n s s) = 0 := rfl

theorem residue_t {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    (p.instantiate read history).tCount ≤ 7 * added p + residue p := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
  | gate g p ih =>
    have h := ih history
    cases g with
    | literal g => cases g <;>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
          tCount, tCost, primitivePhaseCost, added, residue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at * <;> omega
    | whenBit r v g =>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount, added, residue]
        split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | recordGate i v g p ih =>
      have h := ih history
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | measure w p ih =>
      have hf := ih (Fin.lastCases false history)
      have ht := ih (Fin.lastCases true history)
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      omega

theorem residue_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    residue (p.append q) = residue p + residue q := by
  induction p with
  | done => simp [Straight.append, residue]
  | gate g p ih => cases g <;> simp [Straight.append, residue, ih, Nat.add_assoc]
  | recordGate => simp_all [Straight.append, residue, Nat.add_assoc]
  | measure => simp_all [Straight.append, residue]

theorem residue_cast {n s e f} (p : Straight n s e) (h : e=f) :
    residue (castFinish h p) = residue p := by subst f; rfl

theorem residue_literal {n s} (gs : Circuit) :
    residue (literalProgram gs : Straight n s s) = (gs.map primitivePhaseCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp_all [literalProgram, gateProgram, residue]

theorem residue_literal_HPFree {n s} (gs : Circuit) (h : Classical.HPFree gs) :
    residue (literalProgram gs : Straight n s s) = 0 := by
  rw [residue_literal, primitivePhaseCost_of_HPFree gs h]

theorem residue_recordGates {n s e} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    residue (recordGates i gs p) = tCount gs + residue p := by
  induction gs with
  | nil => simp [recordGates, tCount]
  | cons g gs ih => simp [recordGates, residue, tCount, ih, Nat.add_assoc]

@[simp] theorem residue_andErase (n s a b t : Nat) :
    residue (andEraseProgram n s a b t) = 0 := by
  simp [andEraseProgram, residue, residue_recordGates, controlledZ, tCount, tCost]

@[simp] theorem residue_compiled {n start}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    residue (appendCompiled p q).2 = residue p.2 + residue q.2 := by
  simp only [appendCompiled, residue_cast, residue_append]

@[simp] theorem residue_prepend {n start} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (prependCompiled gs p).2 = (gs.map primitivePhaseCost).sum + residue p.2 := by
  simp only [prependCompiled, residue_append, residue_literal]

@[simp] theorem residue_surround {n start} (gs hs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (surroundCompiled gs hs p).2 =
      (gs.map primitivePhaseCost).sum + residue p.2 + (hs.map primitivePhaseCost).sum := by
  simp [surroundCompiled, residue_literal, Nat.add_assoc]

@[simp] theorem residue_vchainTail (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    residue (vchainTailProgram n controls acc target scratch start).2 = 0 := by
  induction controls generalizing acc scratch start with
  | nil => rfl
  | cons control controls ih =>
    cases controls with
    | nil => simp [vchainTailProgram, residue_literal, primitivePhaseCost]
    | cons next controls =>
      cases scratch with
      | nil => rfl
      | cons work scratch => simp only [vchainTailProgram, residue_prepend, residue_compiled,
          ih, residue_andErase]; rfl

@[simp] theorem residue_vchain (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    residue (vchainProgram n start controls target scratch).2 = 0 := by
  unfold vchainProgram
  split <;> simp_all [residue, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMaj (n start control target addend carry scratch : Nat) :
    residue (rippleMajProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUma (n start control target addend carry scratch : Nat) :
    residue (rippleUmaProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMajInv (n start control target addend carry scratch : Nat) :
    residue (rippleMajInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUmaInv (n start control target addend carry scratch : Nat) :
    residue (rippleUmaInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleFirst (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleFirstProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleFirstProgram]

@[simp] theorem residue_rippleSecond (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleSecondProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleSecondProgram]

@[simp] theorem residue_zeroErase (n start a b w : Nat) :
    residue (zeroEraseProgram n start a b w).2 = 0 := by
  simp [zeroEraseProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_dualErase (n start a i x b j y : Nat) :
    residue (dualEraseProgram n start a i x b j y).2 = 0 := by
  simp [dualEraseProgram]

def compiledResidue {n start} (p : (count : Nat) × Straight n start (start+count)) : Nat := residue p.2

@[simp] theorem residue_ite {n start} (c : Prop) [Decidable c]
    (p q : (count : Nat) × Straight n start (start+count)) :
    residue (if c then p else q).2 = if c then residue p.2 else residue q.2 := by
  change compiledResidue (if c then p else q) = _
  split <;> rfl


theorem residue_unary (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (start : Nat) :
    residue (unaryProgram n order leaf tree q path start).2 = 0 := by
  change compiledResidue (unaryProgram n order leaf tree q path start) = 0
  induction tree generalizing q path start with
  | leaf label => rw [unaryProgram.eq_1]; exact hl label q start
  | node bit zero one ihz iho =>
    cases path with
    | nil => rw [unaryProgram.eq_3]; rfl
    | cons p ps =>
      rw [unaryProgram.eq_2]
      simp only [compiledResidue] at ihz iho
      cases order <;>
        simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

theorem residue_dual (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label a b start, residue (leaf label a b start).2 = 0)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    residue (dualProgram n order leaf tree a b xs ys start).2 = 0 := by
  change compiledResidue (dualProgram n order leaf tree a b xs ys start) = 0
  induction tree generalizing a b xs ys start with
  | leaf label => rw [dualProgram.eq_1]; exact hl label a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
    | cons x xs => cases ys with
      | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
      | cons y ys =>
        rw [dualProgram.eq_2]
        simp only [compiledResidue] at ihz iho
        cases order <;>
          simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

@[simp] theorem phaseCost_zeroMask (ws : List Wire) (v : Nat) :
    ((zeroMask ws v).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (zeroMask_HPFree ws v)

@[simp] theorem phaseCost_endpointLeafToggle (top : Bool) (label : Nat) (a b c : Wire) :
    ((endpointLeafToggle top label a b c).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (endpointLeafToggle_HPFree top label a b c)

@[simp] theorem residue_equality (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) : residue (equalityProgram n start register value flag scratch).2 = 0 := by
  simp [equalityProgram, residue_literal]

@[simp] theorem residue_toggleEquality (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    residue (toggleEqualityProgram n start root register value acc flag scratch).2 = 0 := by
  simp [toggleEqualityProgram, primitivePhaseCost]

@[simp] theorem residue_intervalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalFirstProgram, residue_literal]

@[simp] theorem residue_topFirst (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topFirstProgram]

@[simp] theorem residue_traversalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalFirstProgram
  apply residue_dual
  intros
  apply residue_intervalFirst

@[simp] theorem residue_coefficientFirst (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientFirstProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_intervalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalSecondProgram, residue_literal]

@[simp] theorem residue_topSecond (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topSecondProgram]

@[simp] theorem residue_traversalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalSecondProgram
  apply residue_dual
  intros
  apply residue_intervalSecond

@[simp] theorem residue_coefficientSecond (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientSecondProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_coefficient (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientProgram n start r k K mode signUpdate target).2 = 0 := by
  have hl : ∀ label control start, residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by simp
  have hr : ∀ label control start, residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by simp
  cases signUpdate <;> simp [coefficientProgram, residue_unary _ _ _ hl, residue_unary _ _ _ hr,
    residue_literal, coefficientPrefixSignCircuit, primitivePhaseCost]

@[simp] theorem residue_coefficientInverse (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientInverseProgram n start r k K mode signUpdate target).2 = 0 := by
  simp [coefficientInverseProgram]

attribute [local simp] primitivePhaseCost_of_HPFree

@[simp] theorem residue_intervalTopFirst (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopFirstProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopFirstProgram n start r k K mode target) = 0
  unfold intervalTopFirstProgram
  split <;> simp [compiledResidue, residue_literal]
@[simp] theorem residue_intervalTopSecond (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopSecondProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopSecondProgram n start r k K mode target) = 0
  unfold intervalTopSecondProgram
  split <;> simp [compiledResidue, residue_literal]

@[simp] theorem residue_interval (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalProgram n start r width k K mode signUpdate target).2 = 0 := by
  cases signUpdate <;> simp [intervalProgram, residue_literal, intervalSignUpdate, primitivePhaseCost]

@[simp] theorem residue_intervalInverse (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalInverseProgram n start r width k K mode signUpdate target).2 = 0 := by
  simp [intervalInverseProgram]

theorem residue_sequence (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p ∈ ps, ∀ start, residue (p start).2 = 0) (start : Nat) :
    residue (sequenceProgram n ps start).2 = 0 := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [sequenceProgram, residue_compiled]
    rw [hp p (by simp), ih (by intro q hq; exact hp q (by simp [hq]))]

theorem residue_phaseSegments (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hc : (core.map primitivePhaseCost).sum = 0) :
    residue (sequenceProgram n (phaseSegments n r shift core) start).2 = 0 := by
  apply residue_sequence
  intro p hp s
  simp only [phaseSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h <;>
    subst p <;> simp [residue_literal, primitivePhaseCost, hc]

@[simp] theorem residue_phase (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseProgram n start r shift).2 = 0 := by
  unfold phaseProgram
  apply residue_phaseSegments
  simp [phaseCoreGates, primitivePhaseCost]

@[simp] theorem residue_phaseInverse (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseInverseProgram n start r shift).2 = 0 := by
  unfold phaseInverseProgram
  apply residue_phaseSegments
  simp [phaseInverseCoreGates, primitivePhaseCost]

private theorem blockB2_classical (r : IndexedStepRegisters) : Classical.HPFree (blockB2 r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  have hb : Classical.HPFree (blockBForward r 256 (certifiedActiveWindows 256 1).remainder) := by tauto
  simp only [blockBForward, Classical.hpFree_append] at hb
  tauto

@[simp] theorem residue_remainderBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (remainderBlockProgram n start r width w).2 = 0 := by
  unfold remainderBlockProgram remainderBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_coefficientBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (coefficientBlockProgram n start r width w).2 = 0 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_zeroCell (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    residue (zeroCellProgram n start base r bit guard target temporary).2 = 0 := by
  cases base <;> simp [zeroCellProgram, measuredZeroPrefix, primitivePhaseCost]

@[simp] theorem residue_upperForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = K <;> simp [upperForwardLeafProgram, h, he]
  · simp [upperForwardLeafProgram, h]

@[simp] theorem residue_upperReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label < K <;> simp [upperReverseLeafProgram, h]

@[simp] theorem residue_lowerForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = k <;> simp [lowerForwardLeafProgram, h, he]
  · simp [lowerForwardLeafProgram, h]

@[simp] theorem residue_lowerReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k < label ∧ label ≤ K <;> simp [lowerReverseLeafProgram, h]

@[simp] theorem residue_rangeLeaf (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    residue (rangeLeafProgram n after r leaf label dynamic start).2 = 0 := by
  cases after <;> simp [rangeLeafProgram, hl, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rangeScan (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0) :
    residue (rangeScanProgram n after order tree control r path leaf start).2 = 0 := by
  have hr (after : Bool) : ∀ label control start,
      residue (rangeLeafProgram n after r leaf label control start).2 = 0 := by simp [hl]
  cases after <;> simp [rangeScanProgram, residue_unary _ _ _ (hr _), residue_literal, primitivePhaseCost]

@[simp] theorem residue_upperMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [upperMapProgram]

@[simp] theorem residue_lowerMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [lowerMapProgram]

@[simp] theorem phaseCost_highestWrites (k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((highestPositionDirtyWrites k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [highestPositionDirtyWrites])
@[simp] theorem phaseCost_rightWrites (width k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((rightLengthDirtyWrites width k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [rightLengthDirtyWrites])

@[simp] theorem residue_upperWriter (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [upperWriterProgram]

@[simp] theorem residue_lowerWriter (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [lowerWriterProgram]

@[simp] theorem residue_ltUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [ltUpdateProgram]
@[simp] theorem residue_lrpUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [lrpUpdateProgram]

@[simp] theorem residue_upperEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (upperEndProgram n start r width w).2 = 0 := by
  simp [upperEndProgram, residue_literal]

@[simp] theorem residue_lowerEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (lowerEndProgram n start r width w).2 = 0 := by
  simp [lowerEndProgram, residue_literal]

@[simp] theorem residue_end (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endProgram n start r width w).2 = 0 := by
  simp [endProgram, residue_literal]

@[simp] theorem residue_endInverse (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endInverseProgram n start r width w).2 = 0 := by
  simp [endInverseProgram, residue_literal]

@[simp] private theorem blockHPrefix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHPrefix r) := by
  simp [blockHPrefix]
@[simp] private theorem blockHSuffix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHSuffix r) := by
  simp [blockHSuffix]

@[simp] theorem residue_h (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hProgram n start r width T).2 = 0 := by
  simp [hProgram, residue_literal, primitivePhaseCost]
@[simp] theorem residue_hInverse (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hInverseProgram n start r width T).2 = 0 := by
  simp [hInverseProgram, residue_literal, primitivePhaseCost]

@[simp] private theorem blockAForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockFForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockFForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockAInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDForward_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDForward r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepUnitary_HPFree r width T
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDInverse_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDInverse r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepInverseUnitary_HPFree r width T
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_measuredStep (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (measuredStepProgram n start r width T).2 = 0 := by
  simp [measuredStepProgram, measuredStepSegments, sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem phaseCost_adjoint (gs : Circuit) :
    ((gs.adjoint).map primitivePhaseCost).sum = (gs.map primitivePhaseCost).sum := by
  have h := congrArg PrimitiveResources.phase (primitiveResources_unitary_adjoint gs .done)
  simpa [primitiveResources, gidneyGateCount] using h

@[simp] theorem residue_measuredInverseStep (n start : Nat) (r : IndexedStepRegisters) (T : Nat) :
    residue (measuredInverseStepProgram n start r T).2 = 0 := by
  simp [measuredInverseStepProgram, measuredInverseStepSegments, sequenceProgram,
    residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_measuredSchedule (n : Nat) (r : IndexedStepRegisters)
    (width count first start : Nat) :
    residue (measuredScheduleProgram n r width count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredScheduleProgram, residue_compiled, residue_measuredStep, ih, Nat.zero_add]

@[simp] theorem residue_measuredInverseSchedule (n : Nat) (r : IndexedStepRegisters)
    (count first start : Nat) :
    residue (measuredInverseScheduleProgram n r count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredInverseScheduleProgram, residue_compiled, residue_measuredInverseStep, ih, Nat.zero_add]

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem ccx_cost_le (gs : Circuit) : 7 * ccxCount gs ≤ tCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;>
      simp only [ccxCount, tCount, List.map_cons, List.sum_cons, tCost] at * <;> omega

theorem adaptive_ccx_cost_le (p : AdaptiveCircuit) : 7 * (primitiveResources p).toffoli ≤ p.tCount := by
  induction p with
  | done => rfl
  | unitary gs p ih =>
      have hg := ccx_cost_le gs
      rw [ccxCount_primitive] at hg
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega
  | xMeasureReset w f t ihf iht =>
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega

attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram
 secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse added residue
 primitiveResources AdaptiveCircuit.tCount

theorem forwardCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAForward_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAForwardPrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
  have ht := measuredEEAForwardProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAForwardProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAForwardProgram
    exact residue_measuredSchedule _ _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega

theorem reverseCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAReverse_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAReversePrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)
  have ht := measuredEEAReverseProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAReverseProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAReverseProgram
    exact residue_measuredInverseSchedule _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 measuredForwardWrapperProgram measuredReverseWrapperProgram

theorem forwardWrapperFullCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 15772489 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (forwardCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem reverseWrapperFullCount (n start : Nat) :
    AtLeast (measuredReverseWrapperProgram n start).2 15772489 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (reverseCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem AtLeast.relabelCompiled {n start d} (p : (count : Nat) × Straight n start (start+count))
    (hp : AtLeast p.2 d) (f : Wire ≃ Wire) : AtLeast (ChallengeMigration.relabelCompiled f p).2 d := hp.relabel f
def CompiledAtLeast {n start} (p : (count : Nat) × Straight n start (start+count)) (d : Nat) : Prop := AtLeast p.2 d

theorem AtLeast.measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : AtLeast p d) :
    AtLeast (.measure w p) d := by simpa only [AtLeast, added] using hp

theorem AtLeast.collect {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, AtLeast (next cursor prior).2 d)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    AtLeast (collectProgram n next ws start prior).2 d := by
  change CompiledAtLeast (collectProgram n next ws start prior) d
  induction ws generalizing start with
  | nil => exact hn start prior
  | cons w ws ih =>
    rw [collectProgram]
    dsimp only [CompiledAtLeast]
    apply AtLeast.castFinish
    apply AtLeast.measure
    exact ih (start+1) _

theorem forwardBankCount (n start : Nat) :
    AtLeast (measuredForwardDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (forwardWrapperFullCount n start) eeaWorkspaceExchange

theorem reverseBankCount (n start : Nat) :
    AtLeast (measuredReverseDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (reverseWrapperFullCount n start) eeaWorkspaceExchange

attribute [local irreducible] measuredForwardDataBankProgram measuredReverseDataBankProgram
 multiplyDataProgram multiplyWorkProgram unmultiplyDataProgram divisionAfterResetProgram divisionProgram
 multiplicationAfterResetProgram multiplicationCleanupProgram multiplicationCorrectionProgram
 multiplicationProgram coordinateProgram zeroDivisionProgram zeroMultiplicationProgram

theorem divisionAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionAfterResetProgram n start prior).2 15772489 := by
  unfold divisionAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 15772489) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem divisionBothCount (n start : Nat) : AtLeast (divisionProgram n start).2 31544978 := by
  unfold divisionProgram
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ ?_
  · exact (AtLeast.appendCompiled _ _ (forwardWrapperFullCount n start) (AtLeast.zero _)).castCount (by omega)
  · exact AtLeast.collect (divisionAfterResetProgram n) (divisionAfterCount n) _ _ _

theorem multiplicationCleanupCount (n start : Nat) :
    AtLeast (multiplicationCleanupProgram n start).2 15772489 := by
  unfold multiplicationCleanupProgram appendLiteral
  refine (AtLeast.appendCompiled (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n _) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationCorrectionCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationCorrectionProgram n start prior).2 15772489 := by
  unfold multiplicationCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (multiplicationCleanupCount n _)).castCount (by omega)

theorem multiplicationAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationAfterResetProgram n start prior).2 31544978 := by
  unfold multiplicationAfterResetProgram appendRetaining
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ (multiplicationCorrectionCount n _ _)
  exact (AtLeast.appendCompiled _ _ (forwardBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationBothCount (n start : Nat) : AtLeast (multiplicationProgram n start).2 31544978 := by
  unfold multiplicationProgram
  refine (AtLeast.appendCompiled (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact AtLeast.collect (multiplicationAfterResetProgram n) (multiplicationAfterCount n) _ _ _

theorem coordinateAllCount (start : Nat) : AtLeast (coordinateProgram start).2 63089956 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine AtLeast.sequenceCons (d := 31544978) (f := 31544978) _ _ ?_ ?_
  · unfold zeroDivisionProgram
    exact AtLeast.surroundCompiled _ _ _ (divisionBothCount _ _)
  · refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 31544978) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
    unfold zeroMultiplicationProgram
    exact AtLeast.surroundCompiled _ _ _ (multiplicationBothCount _ _)

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram coordinateProgram zeroDivisionProgram
 Single.axis Rounded.entry

theorem AtLeast.gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (.gate g p) d := by
  cases g with
  | literal g => cases g <;> simp_all [AtLeast, added] <;> omega
  | whenBit => exact hp

theorem coreCount (start : Nat) : AtLeast (Single.Physical.core start).2 63089956 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (AtLeast.sequenceCons (d := 63089956) (f := 0) _ _ (coordinateAllCount start) (AtLeast.zero _)).castCount (by omega)

theorem preparedCount (start : Nat) : AtLeast (Single.Physical.prepared start).2 63089956 := by
  unfold Single.Physical.prepared
  exact AtLeast.surroundCompiled _ _ _ (coreCount start)

theorem actualCount (start : Nat) : AtLeast (Single.Physical.actual.program start) 63089956 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedCount 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

theorem signedCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 63089956 := by
  unfold Single.signedWindow
  exact (actualCount start).reindex (Single.signedRow w)

theorem prepareCount {n s e d} (ws : List Wire) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact AtLeast.gate (.literal (.H w)) ih

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  countProof : ∀ start, AtLeast (source.program start) saving

def leftCountes : List (CountedWindow 901120) :=
  ⟨Single.firstWindow,0,fun _ => AtLeast.zero _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,63089956,signedCount w⟩)
def rightCountes : List (CountedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,63089956,signedCount w⟩)
private theorem leftCountes_source : leftCountes.map CountedWindow.source = Single.leftWindows := by
  simp [leftCountes, Single.leftWindows]
private theorem rightCountes_source : rightCountes.map CountedWindow.source = Single.rightWindows := by
  simp [rightCountes, Single.rightWindows]
private theorem leftCountes_saving : (leftCountes.map CountedWindow.saving).sum = 1009439296 := by
  simp [leftCountes, Single.leftSigned]
private theorem rightCountes_saving : (rightCountes.map CountedWindow.saving).sum = 883259384 := by
  simp [rightCountes, Single.rightSigned]

theorem axisCountProof {n} : (ps : List (CountedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    AtLeast (Single.axis (ps.map CountedWindow.source) start prior) ((ps.map CountedWindow.saving).sum)
  | [], _, _ => AtLeast.zero _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine AtLeast.castFinish ?_ _
    refine AtLeast.castCount (AtLeast.append (f := (ps.map CountedWindow.saving).sum) (prepareCount _ (p.countProof start)) ?_) (by omega)
    exact (AtLeast.append (AtLeast.zero _) (axisCountProof ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castCount (by omega)

theorem axisCountFor {n} (ps : List (CountedWindow n)) (ws : List (Single.Window n))
    (he : ps.map CountedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    AtLeast (Single.axis ws start prior) ((ps.map CountedWindow.saving).sum) := by
  subst ws
  exact axisCountProof ps start prior

theorem AtLeast.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : AtLeast p dl) (hq : AtLeast q dr) :
    AtLeast (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact AtLeast.gate _ ((AtLeast.append hp ((AtLeast.append hq (AtLeast.gate _ (AtLeast.zero _))).castCount (Nat.add_zero dr))).castFinish h)

theorem trialCount (start : Nat) : AtLeast (Single.trial start) 1892698680 := by
  have hl := (axisCountFor leftCountes Single.leftWindows leftCountes_source start List.nil).castCount leftCountes_saving
  have hr := (axisCountFor rightCountes Single.rightWindows rightCountes_source
    (start+Single.axisCount Single.leftWindows) List.nil).castCount rightCountes_saving
  unfold Single.trial
  exact (AtLeast.framed _ _ _ _ hl hr).castCount (by decide)

theorem singleProgramCount : AtLeast Single.program 1892698680 := by
  unfold Single.program
  exact (trialCount 0).castFinish _

theorem programCount : AtLeast Rounded.program 1892698680 := by
  unfold Rounded.program
  exact (AtLeast.append singleProgramCount (AtLeast.zero Rounded.readout)).castCount (by omega)

theorem AtLeast.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : AtLeast p d) :
    AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

theorem entryCount : AtLeast Rounded.entry.program 1892698680 := by
  unfold Rounded.entry
  exact AtLeast.fixedEntry Single.mixedCoefficientAt _ programCount

theorem dropped_added {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | record => assumption
  | measure => assumption

attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch


theorem parent_added_lower : 1872869880 ≤ added Parent.entry.program := by
  have h := dropped_added Optimization.entryPatch.drops
  have hc := entryCount
  change 1892698680 ≤ added Rounded.entry.program at hc
  unfold Parent.entry Optimization.replaceEntry
  change 1872869880 ≤ added Optimization.entryPatch.program
  omega


theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ⟨hp.1, ih hp.2⟩


theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program :=
  within_reindex p _ ws hp


attribute [local irreducible] Within

theorem parent_within : Within completeBatchedSupport Parent.entry.program := by
  unfold Parent.entry Optimization.replaceEntry
  apply within_drops Optimization.entryPatch.drops
  unfold Rounded.entry
  apply fixedEntry_within
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact Rounded.program_support read


set_option maxRecDepth 2000

theorem parent_added_upper : added Parent.entry.program ≤ 7629819592 := by
  have h := lower_t 1024 Parent.entry.program 0 Fin.elim0
    (readConstant Parent.entry.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (Parent.certificate.resources 0).2.1
  change (Parent.entry.program.instantiate (readConstant Parent.entry.coefficients.get 0) Fin.elim0).tCount ≤ 15259639184 at ht
  omega


theorem parent_slots : Parent.entry.program.gateSlots ≤ 93000061339 := by
  have hs := Optimization.entryPatch.drops.slots
  have ho : Rounded.entry.program.gateSlots ≤ 93000061339 := by
    rw [Rounded.entry, Single.fixedEntry_slots]
    exact Rounded.program_slots
  unfold Parent.entry Optimization.replaceEntry
  exact hs.trans ho

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant
open Challenge AndGadget Paper2607_13816.ChallengeMigration
attribute [local irreducible] Within
set_option maxRecDepth 10000
attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch
noncomputable def entry : StraightEntry := lowerEntry 1024 Parent.entry
noncomputable def layout : DecodeLayout := lowerLayout 1024 Parent.entry Parent.layout
def bounds : Bounds := ⟨856, 11513899424, 8551122464⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 7629819592) (hl : 1872869880 ≤ a) (hs : slots ≤ 93000061339)
    (hc : cursor ≤ 921302872) (ho : oldT ≤ 15259639184) (hn : 11513899424 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 8551122464 ≤ newRecords) :
    slots + 18*a ≤ maxSlots ∧ cursor+a ≤ maxRecords ∧ oldT ≤ newT + 2*a ∧
    cursor+a ≤ newRecords := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic (added Parent.entry.program) Parent.entry.program.gateSlots
    Parent.entry.finalCursor Parent.bounds.tModel bounds.tModel officialLimits.gateSlots
    officialLimits.measurements bounds.measurements
    parent_added_upper parent_added_lower parent_slots (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply lower_certificate officialLimits Parent.layout Parent.entry Parent.bounds bounds
    1024 completeBatchedSupport Parent.certificate parent_within
  · simp [completeBatchedSupport, resetWires]
  · exact h.1
  · exact h.2.1
  · change completeBatchedSupport.length + 1 ≤ 856
    rw [completeBatchedSupport_length]
  · exact h.2.2.1
  · exact h.2.2.2
end ShorECDLP.Entrant
end

