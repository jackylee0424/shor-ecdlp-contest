import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def NegativeFirstAndComputed (a b target : Wire) (s : BasisState) : Prop :=
  s target = (!s a && s b)

def NegativeSecondAndComputed (a b target : Wire) (s : BasisState) : Prop :=
  s target = (s a && !s b)

def eraseNegativeFirstAnd (a b target : Wire) : AdaptiveCircuit :=
  .unitary [.X a]
    ((measuredAndErase a b target).seq (.unitary [.X a] .done))

def eraseNegativeSecondAnd (a b target : Wire) : AdaptiveCircuit :=
  .unitary [.X b]
    ((measuredAndErase a b target).seq (.unitary [.X b] .done))

private theorem x_seq
    {a b : AdaptiveCircuit} {u v : Circuit} {P Q : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) Q)
    (hu : HPFree u) (hp : ∀ s, P s → Q (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket Q _ (hp s hs))
  apply h.congrIdeal
  intro s _
  rw [Quantum.run_append]
  rfl

private theorem optimized_tCount_seq (a b : AdaptiveCircuit) :
    (a.seq b).tCount = a.tCount + b.tCount := by
  simpa only [gidneyGateCount_tCount] using
    modularGateCount_seq tCost a b

theorem eraseNegativeFirstAnd_coherent (a b target : Wire)
    (hab : a ≠ b) (hat : a ≠ target) (hbt : b ≠ target) :
    CoherentlyImplementsOn (eraseNegativeFirstAnd a b target)
      (Quantum.run [.X a, .CCX a b target, .X a])
      (NegativeFirstAndComputed a b target) := by
  have hmask := CoherentlyImplementsOn.unitary ([.X a] : Circuit)
    (NegativeFirstAndComputed a b target)
  have herase := measuredAndErase_coherent_uncompute a b target hab hat hbt
  have hfirst := x_seq hmask herase (by simp) (by
    intro s hs
    unfold NegativeFirstAndComputed at hs
    unfold PathAndComputed
    simp [Classical.run, Classical.applyGate, upd, hs,
      Ne.symm hab, Ne.symm hat])
  have hunmask := CoherentlyImplementsOn.unitary ([.X a] : Circuit) (fun _ => True)
  have hall := x_seq hfirst hunmask (by simp) (by intros; trivial)
  simpa [eraseNegativeFirstAnd, List.append_assoc] using hall

theorem eraseNegativeSecondAnd_coherent (a b target : Wire)
    (hab : a ≠ b) (hat : a ≠ target) (hbt : b ≠ target) :
    CoherentlyImplementsOn (eraseNegativeSecondAnd a b target)
      (Quantum.run [.X b, .CCX a b target, .X b])
      (NegativeSecondAndComputed a b target) := by
  have hmask := CoherentlyImplementsOn.unitary ([.X b] : Circuit)
    (NegativeSecondAndComputed a b target)
  have herase := measuredAndErase_coherent_uncompute a b target hab hat hbt
  have hfirst := x_seq hmask herase (by simp) (by
    intro s hs
    unfold NegativeSecondAndComputed at hs
    unfold PathAndComputed
    simp [Classical.run, Classical.applyGate, upd, hs,
      hab, Ne.symm hbt])
  have hunmask := CoherentlyImplementsOn.unitary ([.X b] : Circuit) (fun _ => True)
  have hall := x_seq hfirst hunmask (by simp) (by intros; trivial)
  simpa [eraseNegativeSecondAnd, List.append_assoc] using hall

@[simp] theorem eraseNegativeFirstAnd_tCount (a b target : Wire) :
    (eraseNegativeFirstAnd a b target).tCount = 0 := by rfl

@[simp] theorem eraseNegativeSecondAnd_tCount (a b target : Wire) :
    (eraseNegativeSecondAnd a b target).tCount = 0 := by rfl

def BlockEMiddleReady (phase1 phase2 sign terminal control : Wire)
    (s : BasisState) : Prop :=
  s terminal = false ∧
    s control = (s phase1 && !(!s phase2 && s sign))

def blockETemporaryCircuit (phase2 sign terminal : Wire) : Circuit :=
  [.X phase2, .CCX phase2 sign terminal, .X phase2]

def blockESubCircuit (phase1 terminal control : Wire) : Circuit :=
  [.X terminal, .CCX phase1 terminal control, .X terminal]

def optimizedBlockEMiddle (phase1 phase2 sign terminal control : Wire) :
    AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (blockETemporaryCircuit phase2 sign terminal) .done).seq
    ((eraseNegativeSecondAnd phase1 terminal control).seq
      ((eraseNegativeFirstAnd phase2 sign terminal).seq
        (.unitary [.CX phase1 sign, .CX phase1 control] .done)))

def sourceBlockEMiddle (phase1 phase2 sign terminal control : Wire) : Circuit :=
  blockETemporaryCircuit phase2 sign terminal ++
    blockESubCircuit phase1 terminal control ++
    blockETemporaryCircuit phase2 sign terminal ++
    [.CX phase1 sign, .CX phase1 control]

theorem optimizedBlockEMiddle_coherent
    (phase1 phase2 sign terminal control : Wire)
    (hphysical : [phase1, phase2, sign, terminal, control].Nodup) :
    CoherentlyImplementsOn
      (optimizedBlockEMiddle phase1 phase2 sign terminal control)
      (Quantum.run (sourceBlockEMiddle phase1 phase2 sign terminal control))
      (BlockEMiddleReady phase1 phase2 sign terminal control) := by
  have hp1p2 : phase1 ≠ phase2 := by simp_all
  have hp1s : phase1 ≠ sign := by simp_all
  have hp1t : phase1 ≠ terminal := by simp_all
  have hp1c : phase1 ≠ control := by simp_all
  have hp2s : phase2 ≠ sign := by simp_all
  have hp2t : phase2 ≠ terminal := by simp_all
  have hp2c : phase2 ≠ control := by simp_all
  have hst : sign ≠ terminal := by simp_all
  have hsc : sign ≠ control := by simp_all
  have htc : terminal ≠ control := by simp_all
  let temp := blockETemporaryCircuit phase2 sign terminal
  let sub := blockESubCircuit phase1 terminal control
  have htemp := CoherentlyImplementsOn.unitary temp
    (BlockEMiddleReady phase1 phase2 sign terminal control)
  have hsub := eraseNegativeSecondAnd_coherent phase1 terminal control
    hp1t hp1c htc
  have htempSub := x_seq htemp hsub (by simp [temp, blockETemporaryCircuit]) (by
    intro s hs
    unfold BlockEMiddleReady at hs
    unfold NegativeSecondAndComputed
    dsimp only [temp]
    cases h1 : s phase1 <;> cases h2 : s phase2 <;> cases h3 : s sign <;>
      simp [blockETemporaryCircuit, Classical.run, Classical.applyGate, upd,
        hs.1, hs.2, h1, h2, h3, hp1p2, hp1s, hp1t, hp1c,
        hp2s, hp2t, hp2c, hst, hsc, htc,
        Ne.symm hp1p2, Ne.symm hp1s, Ne.symm hp1t, Ne.symm hp1c,
        Ne.symm hp2s, Ne.symm hp2t, Ne.symm hp2c, Ne.symm hst,
        Ne.symm hsc, Ne.symm htc])
  have heraseTemp := eraseNegativeFirstAnd_coherent phase2 sign terminal
    hp2s hp2t hst
  have hcleared := x_seq htempSub heraseTemp (by
      simp [temp, sub, blockETemporaryCircuit, blockESubCircuit]) (by
    intro s hs
    unfold BlockEMiddleReady at hs
    unfold NegativeFirstAndComputed
    dsimp only [temp, sub]
    cases h1 : s phase1 <;> cases h2 : s phase2 <;> cases h3 : s sign <;>
      simp [blockETemporaryCircuit, blockESubCircuit, Classical.run,
        Classical.applyGate, upd, hs.1, hs.2, h1, h2, h3,
        hp1p2, hp1s, hp1t, hp1c, hp2s, hp2t, hp2c, hst, hsc, htc,
        Ne.symm hp1p2, Ne.symm hp1s, Ne.symm hp1t, Ne.symm hp1c,
        Ne.symm hp2s, Ne.symm hp2t, Ne.symm hp2c, Ne.symm hst,
        Ne.symm hsc, Ne.symm htc])
  let suffix : Circuit := [.CX phase1 sign, .CX phase1 control]
  have hsuffix := CoherentlyImplementsOn.unitary suffix (fun _ => True)
  have hall := x_seq hcleared hsuffix (by
    simp [temp, sub, blockETemporaryCircuit, blockESubCircuit]) (by intros; trivial)
  simpa [optimizedBlockEMiddle, sourceBlockEMiddle, temp, sub, suffix,
    List.append_assoc] using hall

@[simp] theorem optimizedBlockEMiddle_tCount
    (phase1 phase2 sign terminal control : Wire) :
    (optimizedBlockEMiddle phase1 phase2 sign terminal control).tCount = 7 := by
  rw [optimizedBlockEMiddle, optimized_tCount_seq, optimized_tCount_seq,
    optimized_tCount_seq, eraseNegativeFirstAnd_tCount,
    eraseNegativeSecondAnd_tCount]
  rfl

theorem sourceBlockEMiddle_tCount
    (phase1 phase2 sign terminal control : Wire) :
    ShorECDLP.tCount (sourceBlockEMiddle phase1 phase2 sign terminal control) = 21 := by
  rfl

end
end ShorECDLP.Paper2607_13816
