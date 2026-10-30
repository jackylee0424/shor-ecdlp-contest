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

def carryUnwindOps {n : Nat} (source target carry : Wire)
    (previous : Option Wire) : List (LookupOp n) :=
  [ordinaryOp (carryIsolate carry previous), .erase source target carry,
    ordinaryOp (carryFinishSum source target previous)]

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

def tightChunks : List Nat :=
  [23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 8]

theorem tightChunks_sum : tightChunks.sum = 256 := by decide +kernel
theorem tightChunks_prefix : (tightChunks.dropLast).sum = 248 := by decide +kernel
theorem tightChunks_count : tightChunks.length = 17 := by decide +kernel

def previousBit (previous : Option Wire) (state : BasisState) : Bool :=
  previous.elim false state

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

def carryFinishCompare (source target : Wire) : Option Wire -> Circuit
  | none => []
  | some previous => [.CX previous target, .CX previous source]

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
      let erase := boundaryEraseProgram n (start + first.1 + tail.1)
        chunkSources chunkTargets work incoming boundary
      appendCompiled first (appendCompiled tail erase)

def wordAddCCX (chunks : List Nat) : Nat :=
  match chunks with
  | [] => 0
  | _ => chunks.sum - 1 + (chunks.dropLast.map (fun width => width - 1)).sum

theorem tightWordAddCCX : wordAddCCX tightChunks = 487 := by decide +kernel

end ShorECDLP.Entrant.FastMul
