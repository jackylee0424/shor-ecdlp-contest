import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Model
import ShorECDLP.Submission.«2607_13816».Challenge.BatchState

namespace ShorECDLP.FlagCorrection

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

abbrev FlagWord := Fin 513 → Bool

def flagWordXor (a b : FlagWord) : FlagWord := fun i => xor (a i) (b i)

def zeroWord : FlagWord := fun _ => false

def wordIsZero (a : FlagWord) : Bool := decide (a = zeroWord)

structure FlagModel where
  data : FlagWord
  flags : Fin 4 → Bool

@[ext] theorem FlagModel.ext (a b : FlagModel) (hd : a.data = b.data)
    (hf : a.flags = b.flags) : a = b := by
  cases a
  cases b
  simp_all

def flagModelStep (words : Fin 8 → FlagWord) (m : FlagModel) : FlagOp → FlagModel
  | .query column control =>
      { m with data := if control = 836 then flagWordXor m.data (words column)
        else if h : control < 4 then
          if m.flags ⟨control, h⟩ then flagWordXor m.data (words column) else m.data
        else m.data }
  | .test flag =>
      { m with flags := (fun j => if j = flag then
          xor (m.flags flag) (wordIsZero m.data) else m.flags j) }

def runFlagModel (words : Fin 8 → FlagWord) (m : FlagModel) : FlagModel :=
  flagSchedule.foldl (flagModelStep words) m

theorem runFlagModel_split (words : Fin 8 → FlagWord) (m : FlagModel) :
    runFlagModel words m = flagClearSchedule.foldl (flagModelStep words)
      (flagUpdateSchedule.foldl (flagModelStep words)
        (flagDetectSchedule.foldl (flagModelStep words) m)) := by
  rfl

def initialFlagModel (data : FlagWord) : FlagModel :=
  ⟨data, fun _ => false⟩

theorem flagWordXor_assoc (a b c : FlagWord) :
    flagWordXor (flagWordXor a b) c = flagWordXor a (flagWordXor b c) := by
  funext i
  exact Bool.xor_assoc _ _ _

theorem flagWordXor_comm (a b : FlagWord) : flagWordXor a b = flagWordXor b a := by
  funext i
  exact Bool.xor_comm _ _

@[simp] theorem flagWordXor_self (a : FlagWord) : flagWordXor a a = zeroWord := by
  funext i
  exact Bool.xor_self _

@[simp] theorem flagWordXor_zero (a : FlagWord) : flagWordXor a zeroWord = a := by
  funext i
  exact Bool.xor_false _

@[simp] theorem flagWordXor_zero_left (a : FlagWord) : flagWordXor zeroWord a = a := by
  funext i
  exact Bool.false_xor _

@[simp] theorem flagWordXor_left_cancel (a b : FlagWord) :
    flagWordXor a (flagWordXor a b) = b := by
  rw [← flagWordXor_assoc, flagWordXor_self, flagWordXor_zero_left]

@[simp] theorem flagWordXor_right_cancel (a b : FlagWord) :
    flagWordXor a (flagWordXor b a) = b := by
  rw [flagWordXor_comm b a, flagWordXor_left_cancel]

@[simp] theorem wordIsZero_zero : wordIsZero zeroWord = true := by
  simp [wordIsZero]

theorem wordIsZero_xor_eq (a b : FlagWord) :
    wordIsZero (flagWordXor a b) = decide (a = b) := by
  unfold wordIsZero
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg (flagWordXor a) h
    exact (by simpa [flagWordXor_left_cancel] using this.symm)
  · rintro rfl
    exact flagWordXor_self a

def modelWords (F T : Fin 4 → FlagWord) : Fin 8 → FlagWord := fun j =>
  if h : j.val < 4 then F ⟨j.val, h⟩ else T ⟨j.val - 4, by omega⟩

def oneHot (k : Fin 4) : Fin 4 → Bool := fun j => decide (j = k)

def detectedModel (F : Fin 4 → FlagWord) (k : Fin 4) : FlagModel :=
  ⟨flagWordXor (F k) (F 3), oneHot k⟩

def updatedModel (F T : Fin 4 → FlagWord) (k : Fin 4) : FlagModel :=
  ⟨flagWordXor (F 3) (T k), oneHot k⟩

theorem flagDetectSchedule_source {F T : Fin 4 → FlagWord}
    (hF : Function.Injective F) (k : Fin 4) :
    flagDetectSchedule.foldl (flagModelStep (modelWords F T)) (initialFlagModel (F k)) =
      detectedModel F k := by
  classical
  have hFne : ∀ i j : Fin 4, i ≠ j → F i ≠ F j := fun i j h => fun he => h (hF he)
  fin_cases k <;> apply FlagModel.ext
  all_goals simp [flagDetectSchedule, flagModelStep, initialFlagModel, modelWords,
    detectedModel, q, wordIsZero_xor_eq, hFne, flagWordXor_comm]
  all_goals funext j
  all_goals fin_cases j <;> simp [oneHot]

theorem flagUpdateSchedule_source {F T : Fin 4 → FlagWord} (k : Fin 4) :
    flagUpdateSchedule.foldl (flagModelStep (modelWords F T)) (detectedModel F k) =
      updatedModel F T k := by
  classical
  fin_cases k <;> apply FlagModel.ext
  all_goals simp [flagUpdateSchedule, flagModelStep, modelWords, detectedModel,
    updatedModel, oneHot, q, flagWordXor_comm]

theorem flagClearSchedule_source {F T : Fin 4 → FlagWord}
    (hT : Function.Injective T) (k : Fin 4) :
    flagClearSchedule.foldl (flagModelStep (modelWords F T)) (updatedModel F T k) =
      ⟨T k, fun _ => false⟩ := by
  classical
  have hTne : ∀ i j : Fin 4, i ≠ j → T i ≠ T j := fun i j h => fun he => h (hT he)
  fin_cases k <;> apply FlagModel.ext
  all_goals simp [flagClearSchedule, flagModelStep, modelWords, updatedModel,
    oneHot, q, wordIsZero_xor_eq, hTne, flagWordXor_comm]
  all_goals funext j
  all_goals fin_cases j <;> simp

theorem runFlagModel_source {F T : Fin 4 → FlagWord}
    (hF : Function.Injective F) (hT : Function.Injective T) (k : Fin 4) :
    (runFlagModel (modelWords F T) (initialFlagModel (F k))).data = T k ∧
      (runFlagModel (modelWords F T) (initialFlagModel (F k))).flags = fun _ => false := by
  rw [runFlagModel_split, flagDetectSchedule_source hF k,
    flagUpdateSchedule_source k, flagClearSchedule_source hT k]
  exact ⟨rfl, rfl⟩

def unmatchedDetectedModel (F : Fin 4 → FlagWord) (data : FlagWord) : FlagModel :=
  ⟨flagWordXor data (F 3), fun _ => false⟩

theorem flagDetectSchedule_unmatched {F T : Fin 4 → FlagWord} (data : FlagWord)
    (hF : ∀ k, data ≠ F k) :
    flagDetectSchedule.foldl (flagModelStep (modelWords F T)) (initialFlagModel data) =
      unmatchedDetectedModel F data := by
  classical
  apply FlagModel.ext
  · simp [flagDetectSchedule, flagModelStep, initialFlagModel, modelWords,
      unmatchedDetectedModel, q, wordIsZero_xor_eq, hF, flagWordXor_comm]
  · funext j
    fin_cases j <;>
      simp [flagDetectSchedule, flagModelStep, initialFlagModel, modelWords,
        unmatchedDetectedModel, q, wordIsZero_xor_eq, hF, flagWordXor_comm]

theorem flagUpdateSchedule_unmatched {F T : Fin 4 → FlagWord} (data : FlagWord) :
    flagUpdateSchedule.foldl (flagModelStep (modelWords F T))
      (unmatchedDetectedModel F data) = unmatchedDetectedModel F data := by
  classical
  apply FlagModel.ext
  · simp [flagUpdateSchedule, flagModelStep, unmatchedDetectedModel, q]
  · funext j
    fin_cases j <;> simp [flagUpdateSchedule, flagModelStep,
      unmatchedDetectedModel, q]

theorem flagClearSchedule_unmatched {F T : Fin 4 → FlagWord} (data : FlagWord)
    (hT : ∀ k, data ≠ T k) :
    flagClearSchedule.foldl (flagModelStep (modelWords F T))
      (unmatchedDetectedModel F data) = initialFlagModel data := by
  classical
  apply FlagModel.ext
  · simp [flagClearSchedule, flagModelStep, modelWords, unmatchedDetectedModel,
      initialFlagModel, q, flagWordXor_comm]
  · funext j
    fin_cases j <;>
      simp [flagClearSchedule, flagModelStep, modelWords, unmatchedDetectedModel,
        initialFlagModel, q, wordIsZero_xor_eq, hT, flagWordXor_comm]

theorem runFlagModel_unmatched {F T : Fin 4 → FlagWord} (data : FlagWord)
    (hF : ∀ k, data ≠ F k) (hT : ∀ k, data ≠ T k) :
    runFlagModel (modelWords F T) (initialFlagModel data) = initialFlagModel data := by
  rw [runFlagModel_split, flagDetectSchedule_unmatched data hF,
    flagUpdateSchedule_unmatched data, flagClearSchedule_unmatched data hT]

end ShorECDLP.FlagCorrection
