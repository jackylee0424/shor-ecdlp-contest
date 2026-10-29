import ShorECDLP.Submission.Entrant.Success
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport
import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
import ShorECDLP.Submission.«2607_13816».Window.ScalarWindows
import ShorECDLP.Submission.«2607_13816».Window.StreamKernel

/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
Our contribution: a uniform per-round acceptance bound of 0.546,
using finite Fourier moments; the entry uses 6 rounds.
The entry and decoder share streamingRounds.
Packaged into existing tracked files for the official source policy;
workspace/port_upstream.py and workspace/package_streaming.py reproduce it.
-/

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ControlSupport -/
section Port_ControlSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def templateControlSafe {n : Nat} (q : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => constantControlSafe q g

def straightControlSafe {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => templateControlSafe q g ∧ straightControlSafe q p
  | .recordGate _ _ g p => constantControlSafe q g ∧ straightControlSafe q p
  | .measure w p => w ≠ q ∧ straightControlSafe q p

theorem constantStraight_support_erase {n s e : Nat} (q : Wire) (p : Straight n s e)
    (safe : straightControlSafe q p) (support : List Wire) (hp : straightWires p ⊆ q::support) :
    straightWires (constantStraight q p) ⊆ support := by
  have hg (g : Gate) (hs : constantControlSafe q g) (h : gateWires g ⊆ q::support) :
      gateWires (constantControlGate q g) ⊆ support := by
    intro w hw
    have hh := (constantControlGate_wires q g hs w).mp hw
    exact (List.mem_cons.mp (h hh.1)).resolve_left hh.2
  induction p with
  | done => exact List.nil_subset _
  | gate g p ih =>
    obtain ⟨hs,sp⟩ := safe
    have hh := List.append_subset.mp hp
    simp only [constantStraight,straightWires,List.append_subset]
    refine ⟨?_,ih sp hh.2⟩
    cases g <;> exact hg _ hs hh.1
  | recordGate i b g p ih =>
    have hh := List.append_subset.mp hp
    exact List.append_subset.mpr ⟨hg g safe.1 hh.1,ih safe.2 hh.2⟩
  | measure w p ih =>
    have hh := List.cons_subset.mp hp
    exact List.cons_subset.mpr ⟨(List.mem_cons.mp hh.1).resolve_left safe.1,ih safe.2 hh.2⟩

theorem straightControlSafe_append {n s m e : Nat} (q : Wire) (p : Straight n s m) (r : Straight n m e) :
    straightControlSafe q (p.append r) ↔ straightControlSafe q p ∧ straightControlSafe q r := by
  induction p <;> simp_all only [Straight.append,straightControlSafe,true_and,and_assoc]

theorem straightControlSafe_castFinish {n s e f : Nat} (q : Wire) (h : e=f) (p : Straight n s e) :
    straightControlSafe q (castFinish h p) ↔ straightControlSafe q p := by subst f; rfl

theorem literalProgram_controlSafe (n start : Nat) (q : Wire) (gs : Circuit)
    (h : ∀ g ∈ gs, constantControlSafe q g) :
    straightControlSafe q (literalProgram (n:=n) (s:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_controlSafe {n s e : Nat} (q : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : ∀ g ∈ gs, constantControlSafe q g) (hp : straightControlSafe q p) :
    straightControlSafe q (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

theorem registerCorrectionProgram_controlSafe {n s e : Nat} (q : Wire) (ws : List Wire)
    (indices : List (Fin s)) (p : Straight n s e) (hw : q ∉ ws) (hp : straightControlSafe q p) :
    straightControlSafe q (registerCorrectionProgram ws indices p) := by
  induction ws generalizing indices with
  | nil => exact hp
  | cons w ws ih =>
    cases indices with
    | nil => exact hp
    | cons i indices =>
      apply recordGates_controlSafe
      · have hne : w ≠ q := by intro he; subst w; exact hw List.mem_cons_self
        simp [pauliZ,constantControlSafe,hne]
      · exact ih indices (fun h => hw (List.mem_cons_of_mem _ h))

theorem deferredCorrectionProgram_controlSafe (n : Nat) (q : Wire) (targets : List Wire)
    (cleanup : Circuit) (cells : List (Circuit × Wire))
    (ht : q ∉ targets) (hc : ∀ g ∈ cleanup, constantControlSafe q g)
    (hcell : ∀ c ∈ cells, (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q)
    (start : Nat) (prior : List (Fin start)) :
    straightControlSafe q (deferredCorrectionProgram n targets cleanup cells start prior) := by
  induction cells generalizing start with
  | nil =>
    apply registerCorrectionProgram_controlSafe _ _ _ _ ht
    apply (straightControlSafe_append _ _ _).mpr
    exact ⟨literalProgram_controlSafe _ _ _ _ hc,
      registerCorrectionProgram_controlSafe _ _ _ _ ht trivial⟩
  | cons c cells ih =>
    simp only [deferredCorrectionProgram,straightControlSafe_castFinish,straightControlSafe_append,straightControlSafe]
    exact ⟨literalProgram_controlSafe _ _ _ _ (hcell c (by simp)).1,
      (hcell c (by simp)).2,ih (fun d hd => hcell d (by simp [hd])) _ _⟩



theorem compareCarryCell_controlSafe (q c r t a d f : Wire) (k last : Bool)
    (h : q ∉ [c,r,t,a,d,f]) :
    ∀ g ∈ gidneyCompareCarryCell q c r t a d f k last, constantControlSafe q g := by
  cases k <;> cases last <;> simp_all [gidneyCompareCarryCell,constantControlSafe,eq_comm]

theorem compareCarryCells_controlSafe (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire) (hq : q ∉ support)
    (hc : current ∈ support) (hs : spare ∈ support) (ha : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ compareCarryCells q current spare ancilla flag input dirty constant,
      (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  induction input generalizing current spare dirty constant with
  | nil => cases dirty <;> cases constant <;> simp [compareCarryCells,hneq current hc]
  | cons a input ih =>
    cases dirty with
    | nil => simp [compareCarryCells]
    | cons d ds =>
      cases constant with
      | nil => simp [compareCarryCells]
      | cons k ks =>
        simp only [compareCarryCells,List.forall_mem_cons]
        refine ⟨⟨compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_,hneq current hc⟩,
          ih spare current ds ks hs hc (fun _ h => hi (List.mem_cons_of_mem _ h))
            (fun _ h => hd (List.mem_cons_of_mem _ h))⟩
        intro h
        have hsupp : [current,spare,ancilla,a,d,flag] ⊆ support := by
          simp only [List.cons_subset,List.nil_subset,and_true]
          exact ⟨hc,hs,ha,hi List.mem_cons_self,hd List.mem_cons_self,hf⟩
        exact hq (hsupp h)

theorem compareCarryProgram_controlSafe (n start : Nat) (a d q c r t f : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (hq : q ∉ support) (ha : a ∈ support) (hd : d ∈ support) (hc : c ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightControlSafe q (compareCarryProgram n start a d q c r t f input dirty k constant) := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  simp only [compareCarryProgram,straightControlSafe_append]
  refine ⟨literalProgram_controlSafe _ _ _ _ (compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_),?_⟩
  · intro h
    have hsupp : [c,r,t,a,d,f] ⊆ support := by
      simp only [List.cons_subset,List.nil_subset,and_true]
      exact ⟨hc,hr,ht,ha,hd,hf⟩
    exact hq (hsupp h)
  · apply deferredCorrectionProgram_controlSafe
    · intro h
      rcases List.mem_cons.mp h with he | h
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · apply controlledConstCarryXor_controlSafe
      intro h
      simp only [List.mem_append,List.mem_cons] at h
      rcases h with (he | he | h) | he | h
      · exact hneq c hc he.symm
      · exact hneq a ha he.symm
      · exact hq (hi h)
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · exact compareCarryCells_controlSafe q r c t f input dirty constant support hq hr hc ht hf hi hds

theorem compareGEProgram_controlSafe (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (support : List Wire) (hq : q ∉ support)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightControlSafe q (compareGEProgram n start input dirty threshold q c r t f).2 := by
  by_cases hz : threshold = 0
  · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,literalProgram [.CX q f]⟩ by simp only [compareGEProgram,hz,ite_true]]
    apply literalProgram_controlSafe
    simp only [List.forall_mem_singleton,constantControlSafe]
    exact fun he => hq (he ▸ hf)
  · by_cases hb : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,.done⟩ by simp only [compareGEProgram,hz,hb,ite_false,ite_true]]
      trivial
    · rw [show compareGEProgram n start input dirty threshold q c r t f = _ by exact (if_neg hz).trans (if_neg hb)]
      cases input with
      | nil => trivial
      | cons a input =>
        cases dirty with
        | nil => trivial
        | cons d ds =>
          generalize (List.map (2 ^ (a :: input).length - threshold).testBit (List.range (a :: input).length)) = bits
          cases bits with
          | nil => trivial
          | cons k ks =>
            exact compareCarryProgram_controlSafe n start a d q c r t f input ds k ks support hq
              (hi List.mem_cons_self) (hd List.mem_cons_self) hc hr ht hf
              (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))

theorem uncontrolledCompareProgram_support (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) :
    straightWires (uncontrolledCompareProgram n start input dirty threshold c r t f).2 ⊆
      [c,r,t,f] ++ input ++ dirty := by
  let support := [c,r,t,f] ++ input ++ dirty
  let q := gidneyCompareVirtualControl input dirty c r t f
  have hq : q ∉ support := by
    intro h
    have hh := List.le_sum_of_mem h
    change support.sum+1 ≤ support.sum at hh
    exact (Nat.not_succ_le_self _) hh
  have hc : c ∈ support := by simp [support]
  have hr : r ∈ support := by simp [support]
  have ht : t ∈ support := by simp [support]
  have hf : f ∈ support := by simp [support]
  have hi : input ⊆ support := fun _ h => by simp [support,h]
  have hd : dirty ⊆ support := fun _ h => by simp [support,h]
  apply constantStraight_support_erase
  · exact compareGEProgram_controlSafe n start input dirty threshold q c r t f support hq hc hr ht hf hi hd
  · exact compareGEProgram_support n start input dirty threshold q c r t f (q::support)
      List.mem_cons_self (List.mem_cons_of_mem _ hc) (List.mem_cons_of_mem _ hr)
      (List.mem_cons_of_mem _ ht) (List.mem_cons_of_mem _ hf)
      (fun _ h => List.mem_cons_of_mem _ (hi h)) (fun _ h => List.mem_cons_of_mem _ (hd h))



theorem modularAddProgram_support (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : correction.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularAddProgram n start input acc correction modulus q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hfirst := (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f)).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input modulus c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) correction f c r t
    support htake hk hf hc hr ht ha (fun _ h => hi (List.mem_of_mem_take h))
  have hlast : circuitWires (controlledCompareLT acc input q c f) ⊆ support := by
    cases acc with
    | nil => simp at hpos
    | cons a acc =>
      intro w hw
      have h := (controlledCompareLT_wires a acc input q c f w hl.symm).mp hw
      have hsub : q::c::f::(a::acc)++input ⊆ support := by
        simp only [List.append_subset,List.cons_subset]
        exact ⟨⟨hq,hc,hf,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hi⟩
      exact hsub h
  simp only [modularAddProgram,straightWires_append,literalProgram_support,appendCompiled_support,List.append_subset]
  exact ⟨hfirst,hcompare _,hadd _,hlast⟩



theorem fieldLoadProgram_support_static (field : PointField) (start : Nat) :
    straightWires (fieldLoadProgram field start) ⊆ windowBaseSupport := by
  have hl : ∀ op ∈ fieldLoadOps field, lookupOpWires op ⊆ windowBaseSupport := by
    apply unaryLookupOps_support
    · simp [windowBaseSupport]
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro z hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro p hp
      have h := (List.of_mem_zip hp).2
      simp only [List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLoadProgram,straightWires_castFinish,lookupProgram_support]
  intro z hz
  obtain ⟨op,hop,hz⟩ := List.mem_flatMap.mp hz
  exact hl op hop hz

theorem fieldLookupAddProgram_support_static (field : PointField) (acc : List Wire)
    (ha : acc ⊆ windowBaseSupport) (hlen : acc.length = 256) (start : Nat) :
    straightWires (fieldLookupAddProgram field acc start).2 ⊆ windowBaseSupport := by
  have had cursor : straightWires (modularAddProgram 32768 cursor (List.range' 7 256) acc
      secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558).2 ⊆ windowBaseSupport := by
    apply modularAddProgram_support
    all_goals try exact ha
    all_goals try simp [hlen,secp256k1ReductionConstantBits,windowBaseSupport]
    · intro w hw
      simp only [List.mem_range'_1] at hw
      simp only [List.mem_append,List.mem_range,List.mem_cons,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLookupAddProgram,appendCompiled_support,List.append_subset]
  exact ⟨fieldLoadProgram_support_static _ _,had _,fieldLoadProgram_support_static _ _⟩

theorem signedFieldProgram_support_static (field : PointField) (start : Nat) :
    straightWires (signedFieldProgram field start).2 ⊆ windowBaseSupport := by
  have hy : List.range' 580 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  simp only [signedFieldProgram,appendCompiled_support,List.append_subset]
  exact ⟨yNegateProgram_support_static _,fieldLookupAddProgram_support_static _ _ hy (by simp) _,yNegateProgram_support_static _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ControlSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEACoreSupport -/
section Port_EEACoreSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_support (n start : Nat) (a b t : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (ht : t ∈ support) :
    straightWires (andEraseProgram n start a b t) ⊆ support := by
  simp only [andEraseProgram,straightWires,recordGates_support,List.append_nil,List.cons_subset]
  refine ⟨ht,?_⟩
  by_cases h : a = b
  · simp [controlledZ,h,circuitWires,gateWires,hb]
  · simp [controlledZ,circuitWires,gateWires,ha,hb]

theorem vchainTailProgram_support (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) (support : List Wire)
    (hc : controls ⊆ support) (ha : acc ∈ support) (ht : target ∈ support)
    (hs : scratch ⊆ support) :
    straightWires (vchainTailProgram n controls acc target scratch start).2 ⊆ support := by
  induction controls generalizing acc scratch start with
  | nil => exact List.nil_subset _
  | cons control controls ih =>
    have hcontrol := hc List.mem_cons_self
    cases controls with
    | nil => simp [vchainTailProgram,literalProgram_support,circuitWires,gateWires,hcontrol,ha,ht]
    | cons next controls =>
      cases scratch with
      | nil => exact List.nil_subset _
      | cons work scratch =>
        have hw := hs List.mem_cons_self
        have hi := ih work scratch start (fun _ h => hc (List.mem_cons_of_mem _ h)) hw (fun _ h => hs (List.mem_cons_of_mem _ h))
        have he cursor := andEraseProgram_support n cursor control acc work support hcontrol ha hw
        simp only [vchainTailProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
        refine ⟨?_,hi,he _⟩
        simp [circuitWires,gateWires,hcontrol,ha,hw]

theorem vchainProgram_support (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (support : List Wire)
    (hc : controls ⊆ support) (ht : target ∈ support) (hs : scratch ⊆ support) :
    straightWires (vchainProgram n start controls target scratch).2 ⊆ support := by
  cases controls with
  | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,ht]
  | cons first rest =>
    have hf := hc List.mem_cons_self
    cases rest with
    | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,hf,ht]
    | cons second rest =>
      apply vchainTailProgram_support n (first::rest) second target scratch start support
      · intro w hw
        exact hc (by simp only [List.mem_cons] at hw ⊢; tauto)
      · exact hc (by simp)
      · exact ht
      · exact hs

theorem rippleMajProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleMajInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajInvProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaInvProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleFirstProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleFirstProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleMajProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleUmaInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs

theorem rippleSecondProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleSecondProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleUmaProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleMajInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs


theorem equalityProgram_support (n start : Nat) (register : List Wire) (value : Nat)
    (flag : Wire) (scratch support : List Wire)
    (hr : register ⊆ support) (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (equalityProgram n start register value flag scratch).2 ⊆ support := by
  have hx := (circuitWires_subset_of_usesOnly (zeroMask_usesOnly register value)).trans hr
  have hb := vchainProgram_support n start register flag scratch support hr hf hs
  simp only [equalityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem toggleEqualityProgram_support (n start : Nat) (root : Wire) (register : List Wire)
    (value : Nat) (acc flag : Wire) (scratch support : List Wire)
    (hroot : root ∈ support) (hr : register ⊆ support) (ha : acc ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (toggleEqualityProgram n start root register value acc flag scratch).2 ⊆ support := by
  have hb cursor := equalityProgram_support n cursor register value flag scratch support hr hf hs
  simp only [toggleEqualityProgram,appendCompiled_support,prependCompiled_support,List.append_subset]
  refine ⟨hb _,?_,hb _⟩
  simp [circuitWires,gateWires,hroot,ha,hf]

theorem intervalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleFirstProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalFirstProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hr,hb,hl⟩

theorem intervalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleSecondProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalSecondProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hl,hb,hr⟩


theorem zeroEraseProgram_support (n start : Nat) (a b w : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (hw : w ∈ support) :
    straightWires (zeroEraseProgram n start a b w).2 ⊆ support := by
  have he := andEraseProgram_support n start a b w support ha hb hw
  have hx : circuitWires [.X b] ⊆ support := by simp [circuitWires,gateWires,hb]
  simp only [zeroEraseProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,he,hx⟩

theorem dualEraseProgram_support (n start : Nat) (a i x b j y : Wire) (support : List Wire)
    (ha : a ∈ support) (hi : i ∈ support) (hx : x ∈ support)
    (hb : b ∈ support) (hj : j ∈ support) (hy : y ∈ support) :
    straightWires (dualEraseProgram n start a i x b j y).2 ⊆ support := by
  simp only [dualEraseProgram,appendCompiled_support,List.append_subset]
  exact ⟨zeroEraseProgram_support n _ b j y support hb hj hy,
    zeroEraseProgram_support n _ a i x support ha hi hx⟩

private theorem port_EEACoreSupport_compiledSupportIf {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

theorem dualProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ a b start, a ∈ support → b ∈ support →
      straightWires (leaf label a b start).2 ⊆ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (ha : a ∈ support) (hb : b ∈ support) (hx : xs ⊆ support) (hy : ys ⊆ support) :
    straightWires (dualProgram n order leaf tree a b xs ys start).2 ⊆ support := by
  induction tree generalizing a b xs ys start with
  | leaf label =>
    rw [dualProgram]
    exact hleaf label (by simp [DualUnaryActionTree.labels]) a b start ha hb
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram] <;> simp [straightWires]
    | cons x xs =>
      cases ys with
      | nil => rw [dualProgram] <;> simp [straightWires]
      | cons y ys =>
        have hix : i ∈ support := hi List.mem_cons_self
        have hjy : j ∈ support := hj List.mem_cons_self
        have hxx : x ∈ support := hx List.mem_cons_self
        have hyy : y ∈ support := hy List.mem_cons_self
        have hz cursor := ihz x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_left _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have ho cursor := iho x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_right _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have he cursor := dualEraseProgram_support n cursor a i x b j y support ha hix hxx hb hjy hyy
        have hca : circuitWires (computeZeroAnd a i x) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,ha,hix,hxx]
        have hcb : circuitWires (computeZeroAnd b j y) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hb,hjy,hyy]
        have hab : circuitWires [.CX a x,.CX b y] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        have hba : circuitWires [.CX b y,.CX a x] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        rw [dualProgram]
        rw [port_EEACoreSupport_compiledSupportIf]
        cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
        · exact ⟨hca,hcb,hz _,hab,ho _,hba,he _⟩
        · exact ⟨hca,hcb,hab,ho _,hba,hz _,he _⟩


theorem topFirstProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleFirstProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topFirstProgram,appendCompiled_support,List.append_subset]
  exact ⟨hright _,hb _,hleft _⟩

theorem topSecondProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleSecondProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topSecondProgram,appendCompiled_support,List.append_subset]
  exact ⟨hleft _,hb _,hright _⟩

theorem traversalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalFirstProgram
  apply dualProgram_support n .dec _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalFirstProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp

theorem traversalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalSecondProgram
  apply dualProgram_support n .inc _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalSecondProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp


theorem unaryProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ control start, control ∈ support →
      straightWires (leaf label control start).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hp : paths ⊆ support) :
    straightWires (unaryProgram n order leaf tree control paths start).2 ⊆ support := by
  induction tree generalizing control paths start with
  | leaf label =>
    rw [unaryProgram]
    exact hleaf label (by simp [UnaryActionTree.labels]) control start hc
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact List.nil_subset _
    | cons path rest =>
      have hib : bit ∈ support := hi List.mem_cons_self
      have hpath : path ∈ support := hp List.mem_cons_self
      have hz cursor := ihz path rest cursor
        (fun l hl => hleaf l (List.mem_append_left _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have ho cursor := iho path rest cursor
        (fun l hl => hleaf l (List.mem_append_right _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have he cursor := zeroEraseProgram_support n cursor control bit path support hc hib hpath
      have hca : circuitWires (computeZeroAnd control bit path) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hc,hib,hpath]
      have hcx : circuitWires [.CX control path] ⊆ support := by simp [circuitWires,gateWires,hc,hpath]
      rw [unaryProgram,port_EEACoreSupport_compiledSupportIf]
      cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
      · exact ⟨hca,hz _,hcx,ho _,hcx,he _⟩
      · exact ⟨hca,hcx,ho _,hcx,hz _,he _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEACoreSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CoefficientSupport -/
section Port_CoefficientSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem coefficientFirstProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientFirstProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleFirstProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientFirstProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientSecondProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientSecondProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleSecondProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientSecondProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (support : List Wire)
    (hc : r.control ∈ support) (ha : r.accumulator k K ∈ support)
    (hcarry : r.carry k K ∈ support) (hs : r.cellScratch k K ∈ support)
    (hindex : (coefficientPrefixTree r k K).indexWires ⊆ support)
    (hpath : r.path k K ⊆ support)
    (ht : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.targetAt target k l ∈ support)
    (had : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.addendAt target k l ∈ support)
    (hsgn : circuitWires (coefficientPrefixSignCircuit r k K signUpdate) ⊆ support) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ support := by
  have hfirst cursor := unaryProgram_support n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientFirstProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hsecond cursor := unaryProgram_support n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientSecondProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hx : circuitWires [.CX r.control (r.accumulator k K)] ⊆ support := by simp [circuitWires,gateWires,hc,ha]
  simp only [coefficientProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hfirst _,hsgn,hsecond _,hx⟩

private theorem port_CoefficientSupport_getD_support {xs support : List Wire} (i : Nat) (fallback : Wire)
    (hxs : xs ⊆ support) (hf : fallback ∈ support) : xs.getD i fallback ∈ support := by
  by_cases h : i < xs.length
  · rw [List.getD_eq_getElem xs fallback h]
    exact hxs (List.getElem_mem h)
  · rw [List.getD_eq_default xs fallback (by omega)]
    exact hf

theorem coefficientProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  have hscratch : r.scratch ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hsget (i : Nat) (hi : i < r.scratch.length) : r.scratch.getD i 0 ∈ r.allWires := by
    rw [List.getD_eq_getElem r.scratch 0 hi]
    exact hscratch (List.getElem_mem hi)
  have hcarry : r.carry k K ∈ r.allWires := hsget _ (by rw [hl.scratch_length]; omega)
  have hw1 : r.work1 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hw2 : r.work2 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hfirst1 : r.work1.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work1.length := by rw [hl.work1_length]; omega
    rw [List.getD_eq_getElem r.work1 0 hp]
    exact hw1 (List.getElem_mem hp)
  have hfirst2 : r.work2.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work2.length := by rw [hl.work2_length]; omega
    rw [List.getD_eq_getElem r.work2 0 hp]
    exact hw2 (List.getElem_mem hp)
  have hwork1 l : r.work1At k l ∈ r.allWires := port_CoefficientSupport_getD_support _ _ hw1 hfirst1
  have hwork2 l : r.work2At k l ∈ r.allWires := port_CoefficientSupport_getD_support _ _ hw2 hfirst2
  apply coefficientProgram_support
  · simp [CoefficientPrefixRegisters.allWires]
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · exact hcarry
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · intro w hw
    have hmem := quotientSwapTree_indexWires_mem_lengthQ (r.routing k K) hl.k_le_K
      (by simpa [CoefficientPrefixRegisters.routing] using hl.index_width) w hw
    have hb : w ∈ r.boundary := hmem
    simp [CoefficientPrefixRegisters.allWires,hb]
  · intro w hw
    exact hscratch (List.mem_of_mem_take hw)
  · intro l _
    cases target
    · exact hwork1 l
    · exact hwork2 l
  · intro l _
    cases target
    · exact hwork2 l
    · exact hwork1 l
  · have hsign : r.sign ∈ r.allWires := by simp [CoefficientPrefixRegisters.allWires]
    cases signUpdate <;> simp [coefficientPrefixSignCircuit,circuitWires,gateWires,hcarry,hsign]

theorem coefficientInverseProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientInverseProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  exact coefficientProgram_support_layout n start r k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CoefficientSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.MultiplicationSupport -/
section Port_MultiplicationSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem modularSubProgram_support (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularSubProgram n start input acc modulus p q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hsub : circuitWires (controlledSubCarry input acc q c f) ⊆ support :=
    (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f).adjoint).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input p c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) modulus f c r t
    support htake hk hf hc hr ht ha (fun _ h => hi (List.mem_of_mem_take h))
  have hlast : circuitWires (controlledCompareLT acc input q c f) ⊆ support := by
    cases acc with
    | nil => simp at hpos
    | cons a acc =>
      intro w hw
      have h := (controlledCompareLT_wires a acc input q c f w hl.symm).mp hw
      have hsub : q::c::f::(a::acc)++input ⊆ support := by
        simp only [List.append_subset,List.cons_subset]
        exact ⟨⟨hq,hc,hf,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hi⟩
      exact hsub h
  simp only [modularSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hlast,hadd _,hcompare _,hsub⟩

theorem modularDoubleProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularDoubleProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc)).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hlast : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularDoubleProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hshift,hcompare _,hadd _,hlast⟩

theorem modularHalveProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularHalveProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc).adjoint).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hfirst : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularHalveProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hfirst,hadd _,hcompare _,hshift⟩



theorem compiledIf_support {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := modularAddProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem hornerInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerInverseProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := modularSubProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩

theorem squareAddProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareAddProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularAddProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareAddProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem squareSubProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareSubProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularSubProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := squareAddProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem squareInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareInverseProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := squareSubProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩



attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_support (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hx : x.length = acc.length) (hy : y.length = acc.length)
    (hk : correction.length = acc.length) (hm : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support)
    (hsx : x ⊆ support) (hsy : y ⊆ support) (hsa : acc ⊆ support) :
    straightWires (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 ⊆ support := by
  have hs cursor := squareProgram_support n cursor y y acc correction p copied c r t f support hy hk hpos hcopy hc hr ht hf hsy hsy hsa
  have hu cursor := squareInverseProgram_support n cursor y y acc modulus p copied c r t f support hy hm hpos hcopy hc hr ht hf hsy hsy hsa
  have hsub cursor := modularSubProgram_support n cursor acc x modulus p q copied f r c support hx.symm
    (hm.trans hx.symm) (hx.symm ▸ hpos) hq hcopy hf hr hc hsa hsx
  simp only [squareSubtractProgram,appendCompiled_support,List.append_subset]
  exact ⟨hs _,hsub _,hu _⟩

theorem pointSquareProgram_support_static (n start : Nat) :
    straightWires (pointSquareProgram n start).2 ⊆ windowBaseSupport := by
  apply squareSubtractProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega


theorem multiplyWorkProgram_support_static (n start : Nat) :
    straightWires (multiplyWorkProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem multiplyDataProgram_support_static (n start : Nat) :
    straightWires (multiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem unmultiplyDataProgram_support_static (n start : Nat) :
    straightWires (unmultiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerInverseProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem xNegateProgram_support_static (n start : Nat) :
    straightWires (xNegateProgram n start).2 ⊆ windowBaseSupport := by
  apply modularNegateProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_MultiplicationSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.LengthSupport -/
section Port_LengthSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem zeroCellProgram_support (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (support : List Wire) (hr : r ∈ support) (hb : bit ∈ support)
    (hg : guard ∈ support) (ht : target ∈ support) (hm : temporary ∈ support) :
    straightWires (zeroCellProgram n start base r bit guard target temporary).2 ⊆ support := by
  simp only [zeroCellProgram,prependCompiled_support,List.append_subset]
  constructor
  · cases base <;> simp [measuredZeroPrefix,circuitWires,gateWires,hr,hb,hg,ht,hm]
  · exact andEraseProgram_support n start r bit temporary support hr hb hm

attribute [local irreducible] zeroCellProgram

theorem upperForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem upperReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem lowerForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem lowerReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem rangeLeafProgram_support (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (label : Nat) (dynamic : Wire) (start : Nat)
    (support : List Wire) (hr : r ∈ support) (hd : dynamic ∈ support)
    (hl : straightWires (leaf label r start).2 ⊆ support) :
    straightWires (rangeLeafProgram n after r leaf label dynamic start).2 ⊆ support := by
  unfold rangeLeafProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨by simp [circuitWires,gateWires,hr,hd],hl⟩
  · exact ⟨hl,by simp [circuitWires,gateWires,hr,hd]⟩

theorem rangeScanProgram_support (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat) (support : List Wire)
    (hl : ∀ label ∈ tree.labels, ∀ cursor,
      straightWires (leaf label r cursor).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (hp : path ⊆ support) :
    straightWires (rangeScanProgram n after order tree control r path leaf start).2 ⊆ support := by
  have hu (a : Bool) := unaryProgram_support n order (rangeLeafProgram n a r leaf)
    tree control path start support
    (fun label hlabel dynamic cursor hd => rangeLeafProgram_support n a r leaf label dynamic cursor support hr hd (hl label hlabel cursor)) hi hc hp
  unfold rangeScanProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨hu false,by simp [circuitWires,gateWires,hc,hr]⟩
  · exact ⟨by simp [circuitWires,gateWires,hc,hr],hu true⟩


theorem upperMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold upperMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp

theorem lowerMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold lowerMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp


theorem upperWriterProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (truthMinusOneValue targets.length K)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (highestPositionDirtyWrites k K targets dirtyAt) ⊆ support := by
    unfold highestPositionDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := upperMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold upperWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩

theorem lowerWriterProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (rightLengthValue width targets.length k)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (rightLengthDirtyWrites width k K targets dirtyAt) ⊆ support := by
    unfold rightLengthDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := lowerMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold lowerWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩


theorem ltUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthRP ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hy⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  have hb := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  unfold ltUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply upperWriterProgram_support <;> assumption

theorem lrpUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthT ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hx⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (addConstant_usesOnly lengthT constants carry 3)).trans hs
  have hb := (circuitWires_subset_of_usesOnly (subConstant_usesOnly lengthT constants carry 3)).trans hs
  unfold lrpUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply lowerWriterProgram_support <;> assumption
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_LengthSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.IntervalSupport -/
section Port_IntervalSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_IntervalSupport_list_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex


private theorem port_IntervalSupport_intervalTopRelative_lt_laneCount
    (k K : Nat) (hkK : k ≤ K) :
    intervalTopRelative k K < intervalLaneCount k K := by
  simp only [intervalTopRelative, intervalLaneCount]
  omega


private theorem port_IntervalSupport_intervalTargetAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := port_IntervalSupport_list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)
  | work2 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := port_IntervalSupport_list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))


private theorem port_IntervalSupport_intervalAddendAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.addendAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := port_IntervalSupport_list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))
  | work2 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := port_IntervalSupport_list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)


private theorem port_IntervalSupport_intervalScratch_mem_allWires
    (registers : IntervalRegisters) {wire : Wire}
    (hwire : wire ∈ registers.scratch) :
    wire ∈ registers.allWires := by
  rw [IntervalRegisters.allWires]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hwire)))))


private theorem port_IntervalSupport_intervalRightTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.rightTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := port_IntervalSupport_list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
    rw [IntervalRegisters.rightTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · have hbound : 0 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := port_IntervalSupport_list_getD_mem registers.lengthT 0 0 hbound
    rw [IntervalRegisters.rightTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem port_IntervalSupport_intervalLeftTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.leftTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := port_IntervalSupport_list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
    rw [IntervalRegisters.leftTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hbound : 1 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := port_IntervalSupport_list_getD_mem registers.lengthT 1 0 hbound
    rw [IntervalRegisters.leftTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem port_IntervalSupport_intervalEndpointSupport_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ intervalEndpointSupport registers.lengthT registers.lengthQ
          registers.lengthS registers.endpointScratch (registers.carry k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [intervalEndpointSupport, List.mem_append, List.mem_singleton] at hwire
  rcases hwire with ((((hscratch | hcarry) | ht) | hq) | hs)
  · exact port_IntervalSupport_intervalScratch_mem_allWires registers
      (List.mem_of_mem_take hscratch)
  · subst wire
    exact port_IntervalSupport_intervalScratch_mem_allWires registers
      (intervalCarry_mem_scratch registers k K target hlayout)
  · simp [IntervalRegisters.allWires, ht]
  · simp [IntervalRegisters.allWires, hq]
  · simp [IntervalRegisters.allWires, hs]


private theorem port_IntervalSupport_intervalDecoder_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ (intervalTree registers k K).decoderWires registers.control
          registers.control (registers.rightPaths k K) (registers.leftPaths k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hrightPath | hleftPath
  · rcases hcontrol with rfl | rfl <;> simp [IntervalRegisters.allWires]
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexA)
    have hbound : bit < registers.lengthS.length :=
      lt_of_lt_of_le hbit hlayout.right_index_capacity
    have hmem := port_IntervalSupport_list_getD_mem registers.lengthS bit 0 hbound
    change registers.lengthS.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexBWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexB)
    have hbound : bit < registers.lengthQ.length :=
      lt_of_lt_of_le hbit hlayout.left_index_capacity
    have hmem := port_IntervalSupport_list_getD_mem registers.lengthQ bit 0 hbound
    change registers.lengthQ.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_take hrightPath
    simp [IntervalRegisters.allWires, hscratch]
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_drop (List.mem_of_mem_take hleftPath)
    simp [IntervalRegisters.allWires, hscratch]



theorem intervalTopFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopFirstProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopFirstProgram
  rw [compiledIf_support]
  split
  · apply topFirstProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalTargetAt_mem_allWires r k K _ target hl (port_IntervalSupport_intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact port_IntervalSupport_intervalAddendAt_mem_allWires r k K _ target hl (port_IntervalSupport_intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact port_IntervalSupport_intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTopSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopSecondProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopSecondProgram
  rw [compiledIf_support]
  split
  · apply topSecondProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalTargetAt_mem_allWires r k K _ target hl (port_IntervalSupport_intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact port_IntervalSupport_intervalAddendAt_mem_allWires r k K _ target hl (port_IntervalSupport_intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact port_IntervalSupport_intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTraversalFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalFirstProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := port_IntervalSupport_intervalDecoder_mem_allWires r k K target hl
  apply traversalFirstProgram_support
  · exact port_IntervalSupport_intervalRightTop_mem_allWires r k K target hl
  · exact port_IntervalSupport_intervalLeftTop_mem_allWires r k K target hl
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact port_IntervalSupport_intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact port_IntervalSupport_intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])

theorem intervalTraversalSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalSecondProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := port_IntervalSupport_intervalDecoder_mem_allWires r k K target hl
  apply traversalSecondProgram_support
  · exact port_IntervalSupport_intervalRightTop_mem_allWires r k K target hl
  · exact port_IntervalSupport_intervalLeftTop_mem_allWires r k K target hl
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact port_IntervalSupport_intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact port_IntervalSupport_intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact port_IntervalSupport_intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])


theorem intervalProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  have he := port_IntervalSupport_intervalEndpointSupport_mem_allWires r k K target hl
  have hprep := (circuitWires_subset_of_usesOnly (prepareIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have hrest := (circuitWires_subset_of_usesOnly (restoreIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have ht1 cursor := intervalTopFirstProgram_support n cursor r k K mode target hl
  have ht2 cursor := intervalTopSecondProgram_support n cursor r k K mode target hl
  have hp1 cursor := intervalTraversalFirstProgram_support n cursor r k K mode target hl
  have hp2 cursor := intervalTraversalSecondProgram_support n cursor r k K mode target hl
  have hcarry := port_IntervalSupport_intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  have hsign : r.sign ∈ r.allWires := by simp [IntervalRegisters.allWires]
  have hsgn : circuitWires (intervalSignUpdate r k K signUpdate) ⊆ r.allWires := by
    cases signUpdate <;> simp [intervalSignUpdate,circuitWires,gateWires,hcarry,hsign]
  simp only [intervalProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hprep,ht1 _,hp1 _,hsgn,hp2 _,ht2 _,hrest⟩

theorem intervalInverseProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalInverseProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  exact intervalProgram_support_layout n start r width k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_IntervalSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.PhaseSupport -/
section Port_PhaseSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem phaseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseInverseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseInverseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseInverseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseSegments_support (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hcore : circuitWires core ⊆ r.epochWires shift) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start,
      straightWires (seg start).2 ⊆ r.epochWires shift := by
  have hq cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthQ
    (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hr cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthRPrime
    (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hs cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthS
    (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hx : circuitWires [.X shift] ⊆ r.epochWires shift := by
    simp [circuitWires,gateWires,PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.withShiftEpoch,PhaseUpdateRegisters.allWires]
  intro seg hseg start
  simp only [phaseSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hq _ | exact hr _ | exact hs _ | simpa only [literalProgram_support] using hx | simpa only [literalProgram_support] using hcore

theorem phaseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseCoreGates_support _)) start

theorem phaseInverseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseInverseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseInverseCoreGates_support _)) start
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_PhaseSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.StepSupport -/
section Port_StepSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_StepSupport_support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))


private theorem port_StepSupport_range580_of_closed (ws : List Wire) (h : ws.all (fun w => decide (w < 580)) = true)
    (w : Wire) (hw : w ∈ ws) : w ∈ List.range 580 := port_StepSupport_support_to_580 ws h w hw


private theorem port_StepSupport_window_mem {work : List Wire} {window : ActiveWindow} {w : Wire}
    (hw : w ∈ IndexedStepRegisters.windowSlice work window) : w ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hw)


private theorem port_StepSupport_production_remainder_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.remainder window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ (r.lengthQ ++ (r.lengthS ++
    (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch)).take (r.remainderScratchSize window)))))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact port_StepSupport_range580_of_closed r.work1 (by decide +kernel) w (port_StepSupport_window_mem hw)
  · exact port_StepSupport_range580_of_closed r.work2 (by decide +kernel) w (port_StepSupport_window_mem hw)
  · exact port_StepSupport_range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact port_StepSupport_range580_of_closed r.lengthQ (by decide +kernel) w hw
  · exact port_StepSupport_range580_of_closed r.lengthS (by decide +kernel) w hw
  · exact port_StepSupport_range580_of_closed (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch))
      (by decide +kernel) w (List.mem_of_mem_take hw)


private theorem port_StepSupport_gate_support_580 (g : Gate)
    (h : (gateWires g).all (fun w => decide (w < 580)) = true) :
    PaperCircuitUsesOnly (List.range 580) ([g] : Circuit) := by
  intro g' hg
  simp only [List.mem_singleton] at hg
  subst g'
  exact port_StepSupport_support_to_580 _ h


private theorem port_StepSupport_production_coefficient_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.coefficient window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ r.blockScratch.take (max (quotientSwapUnaryDepth window.start window.stop) r.lengthT.length+3)))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact port_StepSupport_range580_of_closed r.work1 (by decide +kernel) w (port_StepSupport_window_mem hw)
  · exact port_StepSupport_range580_of_closed r.work2 (by decide +kernel) w (port_StepSupport_window_mem hw)
  · exact port_StepSupport_range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact port_StepSupport_range580_of_closed r.blockScratch (by decide +kernel) w (List.mem_of_mem_take hw)


attribute [local irreducible] intervalProgram rControlNonterminal coefficientProgram

theorem remainderBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : IntervalLayout (indexedStepProductionRegisters.remainder w) w.start w.stop .work1) :
    straightWires (remainderBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := (rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hp := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hr := (rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime
    (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hc := port_StepSupport_gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel)
  have hx := port_StepSupport_gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hrestore := circuitWires_subset_of_usesOnly ((hc.append hr).append hc)
  have h2 : circuitWires (blockB2 r) ⊆ List.range 580 := by
    exact circuitWires_subset_of_usesOnly ((hp.append hx).append hp)
  have hiSub cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .sub true .work1 hl).trans
    (fun _ h => port_StepSupport_production_remainder_support w _ h)
  have hiAdd cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .add false .work1 hl).trans
    (fun _ h => port_StepSupport_production_remainder_support w _ h)
  unfold remainderBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [remainderBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using circuitWires_subset_of_usesOnly hs | simpa only [literalProgram_support] using h2 | simpa only [literalProgram_support] using hrestore

theorem coefficientBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : CoefficientPrefixLayout (indexedStepProductionRegisters.coefficient w) w.start w.stop) :
    straightWires (coefficientBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have ht := (computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hs := (computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have ha := (computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hp := (prepareLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hr := (restoreLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  have hx := port_StepSupport_gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel)
  have hfirst := circuitWires_subset_of_usesOnly (((ht.append hs).append ht).append hp)
  have hmiddle := circuitWires_subset_of_usesOnly ((((ht.append hs).append ht).append hx).append ha)
  have hlast := circuitWires_subset_of_usesOnly (ha.append hr)
  have hiSub cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .sub false .work2 hl).trans
    (fun _ h => port_StepSupport_production_coefficient_support w _ h)
  have hiAdd cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .add true .work2 hl).trans
    (fun _ h => port_StepSupport_production_coefficient_support w _ h)
  unfold coefficientBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coefficientBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using hfirst | simpa only [literalProgram_support] using hmiddle | simpa only [literalProgram_support] using hlast

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem indexedStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (indexedStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hs := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩,hG⟩,hH⟩ := hs
  have hCD : circuitWires (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters (certifiedActiveWindows 256 T).quotientSwap) ⊆ List.range 580 := by
    simp only [circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hC,hD⟩
  have hrem cursor := remainderBlockProgram_support_production n cursor 256 _ hl.remainder
  have hcoef cursor := coefficientBlockProgram_support_production n cursor 256 _ hl.coefficient
  have hphase cursor := (phaseProgram_support n cursor indexedStepProductionRegisters.phaseUpdate indexedStepProductionRegisters.shiftEpoch).trans
    (port_StepSupport_support_to_580 _ (by decide +kernel))
  unfold indexedStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [indexedStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · simpa only [literalProgram_support,circuitWires] using hH
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_StepSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EndpointSupport -/
section Port_EndpointSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_EndpointSupport_getD_support (ws : List Wire) (i : Nat)
    (hws : ∀ w ∈ ws, w ∈ List.range 580) : ws.getD i 0 ∈ List.range 580 := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hws _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_range.mpr (by decide)

private theorem port_EndpointSupport_endpoint_width {k K : Nat} (hK : K ≤ 259) :
    DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hmem : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'_1] at hmem
  norm_num
  omega

private theorem port_EndpointSupport_support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))
theorem endPrograms_support_production (n start T : Nat)
    (hlayout : EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (endProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 ∧
    straightWires (endInverseProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters.endIteration 256 T
  let windows := endIterationWindowsAt 256 T
  have hc : r.control ∈ List.range 580 := List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  have h1 : ∀ w ∈ r.work1, w ∈ List.range 580 := port_EndpointSupport_support_to_580 indexedStepProductionRegisters.work1 (by decide +kernel)
  have h2 : ∀ w ∈ r.work2, w ∈ List.range 580 := port_EndpointSupport_support_to_580 indexedStepProductionRegisters.work2 (by decide +kernel)
  have hT : ∀ w ∈ r.lengthT, w ∈ List.range 580 := port_EndpointSupport_support_to_580 indexedStepProductionRegisters.lengthT (by decide +kernel)
  have hRP : ∀ w ∈ r.lengthRP, w ∈ List.range 580 := port_EndpointSupport_support_to_580 indexedStepProductionRegisters.lengthRPrime (by decide +kernel)
  have hs : ∀ w ∈ r.scratch, w ∈ List.range 580 := by
    intro w hw
    exact port_EndpointSupport_support_to_580 (indexedStepProductionRegisters.sourceScratch.drop 2)
      (by decide +kernel) w (List.mem_of_mem_take hw)
  have hpath : ∀ k K w, w ∈ r.path k K → w ∈ List.range 580 := by
    intro k K w hw; exact hs w (List.mem_of_mem_take hw)
  have hconst : ∀ w ∈ r.constants, w ∈ List.range 580 := by
    intro w hw; exact hs w (List.mem_of_mem_take hw)
  have huIndex : ∀ w ∈ (r.upperTree windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthRP,[]⟩
    intro w hw
    exact hRP w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k4_le_K4
      (port_EndpointSupport_endpoint_width hlayout.K4_le_work) w hw)
  have hlIndex : ∀ w ∈ (r.lowerTree 256 windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthT,[]⟩
    intro w hw
    exact hT w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k5_le_decode
      (port_EndpointSupport_endpoint_width (Nat.min_le_right _ _)) w hw)
  have hu cursor := ltUpdateProgram_support n 256 windows.k4 windows.K4 (r.upperTree windows) r.control
    (r.rangeAccumulator windows.k4 windows.K4) (r.temporary windows.k4 windows.K4) r.carry
    (r.path windows.k4 windows.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => huIndex _ h) hc (port_EndpointSupport_getD_support _ _ hs) (port_EndpointSupport_getD_support _ _ hs) (port_EndpointSupport_getD_support _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => port_EndpointSupport_getD_support _ _ h1) (fun _ => port_EndpointSupport_getD_support _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hl cursor := lrpUpdateProgram_support n 256 windows.k5 (windows.K5Decode 256) (r.lowerTree 256 windows) r.control
    (r.rangeAccumulator windows.k5 (windows.K5Decode 256)) (r.temporary windows.k5 (windows.K5Decode 256)) r.carry
    (r.path windows.k5 (windows.K5Decode 256)) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => hlIndex _ h) hc (port_EndpointSupport_getD_support _ _ hs) (port_EndpointSupport_getD_support _ _ hs) (port_EndpointSupport_getD_support _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => port_EndpointSupport_getD_support _ _ h1) (fun _ => port_EndpointSupport_getD_support _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hws : r.control :: r.work1 ++ r.work2 ⊆ List.range 580 := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hc,fun _ h => h1 _ h⟩,fun _ h => h2 _ h⟩
  have hf := (circuitWires_subset_of_usesOnly (controlledWorkSwap_usesOnly r.control r.work1 r.work2)).trans hws
  have hb := (circuitWires_subset_of_usesOnly (controlledWorkSwapInverse_usesOnly r.control r.work1 r.work2)).trans hws
  constructor
  · simp only [endProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
    exact ⟨hf,hu _,hl _⟩
  · simp only [endInverseProgram,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hl _,hu _,hb⟩


private theorem port_EndpointSupport_production_h_literals :
    circuitWires (blockHPrefix indexedStepProductionRegisters) ⊆ List.range 580 ∧
    circuitWires (blockHSuffix indexedStepProductionRegisters) ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hq := (mcxVChain_usesOnly r.lengthQ (r.sourceScratch.getD 0 0)
    (r.sourceScratch.drop 2)).mono (port_EndpointSupport_support_to_580 _ (by decide +kernel))
  have hs := (mcxVChain_usesOnly (r.lengthS ++ [r.shiftEpoch]) (r.sourceScratch.getD 1 0)
    (r.sourceScratch.drop 2)).mono (port_EndpointSupport_support_to_580 _ (by decide +kernel))
  have hx : PaperCircuitUsesOnly (List.range 580) ([.X r.shiftEpoch] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact port_EndpointSupport_support_to_580 _ (by decide +kernel) w hw
  have hc : PaperCircuitUsesOnly (List.range 580)
      ([.CCX (r.sourceScratch.getD 0 0) (r.sourceScratch.getD 1 0) r.control] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact port_EndpointSupport_support_to_580 _ (by decide +kernel) w hw
  constructor
  · exact circuitWires_subset_of_usesOnly ((((hq.append hx).append hs).append hx).append hc)
  · exact circuitWires_subset_of_usesOnly ((((hc.append hx).append hs).append hx).append hq)

theorem hPrograms_support_production (n start T : Nat)
    (hl : T%4=0 → EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (hProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 ∧
    straightWires (hInverseProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hx : circuitWires ([.CX indexedStepProductionRegisters.control indexedStepProductionRegisters.iter] : Circuit) ⊆ List.range 580 := by
    intro w hw
    exact port_EndpointSupport_support_to_580 _ (by decide +kernel) w hw
  unfold hProgram hInverseProgram
  rw [compiledIf_support,compiledIf_support]
  by_cases h : T%4=0
  · simp only [h,ite_true,surroundCompiled_support,circuitWires,List.flatMap_append,List.append_subset]
    obtain ⟨hf,hb⟩ := port_EndpointSupport_production_h_literals
    obtain ⟨he,hi⟩ := endPrograms_support_production n start T (hl h)
    exact ⟨⟨⟨hf,he⟩,hx,hb⟩,⟨⟨hf,hx⟩,hi⟩,hb⟩
  · simp [h,straightWires]

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem measuredStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hs := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩,hG⟩,hH⟩ := hs
  have hCD : circuitWires (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters (certifiedActiveWindows 256 T).quotientSwap) ⊆ List.range 580 := by
    simp only [circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hC,hD⟩
  have hrem cursor := remainderBlockProgram_support_production n cursor 256 _ hl.remainder
  have hcoef cursor := coefficientBlockProgram_support_production n cursor 256 _ hl.coefficient
  have hphase cursor := (phaseProgram_support n cursor indexedStepProductionRegisters.phaseUpdate indexedStepProductionRegisters.shiftEpoch).trans
    (port_EndpointSupport_support_to_580 _ (by decide +kernel))
  unfold measuredStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · exact (hPrograms_support_production n _ T hl.endIteration).1
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EndpointSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEACenterSupport -/
section Port_EEACenterSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constMinusProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (constMinusProgram n start input dirty bits q c r t).2 ⊆ support := by
  have hx : circuitWires (controlledComplement input q) ⊆ support := by
    intro w hw
    simp only [controlledComplement,circuitWires,List.mem_flatMap,List.mem_map] at hw
    obtain ⟨g,⟨z,hz,rfl⟩,hw⟩ := hw
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact hq
    · exact hi hz
  have hinc := gidneyProgram_support n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t support hd (by simp) hq hc hr ht hi hy
  have hbody cursor := gidneyProgram_support n cursor input dirty bits q c r t support hd hk hq hc hr ht hi hy
  simp only [constMinusProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
  exact ⟨hx,hinc,hbody _⟩

theorem eeaCenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaCenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb cursor := constMinusProgram_support n cursor input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst := (uncontrolledCompareProgram_support n start input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaCenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨htst,hb _⟩

theorem eeaUncenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaUncenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb := constMinusProgram_support n start input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst cursor := (uncontrolledCompareProgram_support n cursor input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaUncenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨hb,htst _⟩

theorem eeaParityProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaParityProgram n start input dirty bits c r t iter).2 ⊆ support := by
  have hb := constMinusProgram_support n start input dirty bits iter c r t support hd hk he hc hr ht hi hy
  have hx : circuitWires [.X iter] ⊆ support := by simp [circuitWires,gateWires,he]
  simp only [eeaParityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEACenterSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WrapperSupport -/
section Port_WrapperSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_WrapperSupport_support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))


private theorem port_WrapperSupport_range580_of_closed (ws : List Wire) (h : ws.all (fun w => decide (w < 580)) = true)
    (w : Wire) (hw : w ∈ ws) : w ∈ List.range 580 := port_WrapperSupport_support_to_580 ws h w hw


private theorem port_WrapperSupport_window_mem {work : List Wire} {window : ActiveWindow} {w : Wire}
    (hw : w ∈ IndexedStepRegisters.windowSlice work window) : w ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hw)


private theorem port_WrapperSupport_production_remainder_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.remainder window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ (r.lengthQ ++ (r.lengthS ++
    (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch)).take (r.remainderScratchSize window)))))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact port_WrapperSupport_range580_of_closed r.work1 (by decide +kernel) w (port_WrapperSupport_window_mem hw)
  · exact port_WrapperSupport_range580_of_closed r.work2 (by decide +kernel) w (port_WrapperSupport_window_mem hw)
  · exact port_WrapperSupport_range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact port_WrapperSupport_range580_of_closed r.lengthQ (by decide +kernel) w hw
  · exact port_WrapperSupport_range580_of_closed r.lengthS (by decide +kernel) w hw
  · exact port_WrapperSupport_range580_of_closed (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch))
      (by decide +kernel) w (List.mem_of_mem_take hw)


private theorem port_WrapperSupport_gate_support_580 (g : Gate)
    (h : (gateWires g).all (fun w => decide (w < 580)) = true) :
    PaperCircuitUsesOnly (List.range 580) ([g] : Circuit) := by
  intro g' hg
  simp only [List.mem_singleton] at hg
  subst g'
  exact port_WrapperSupport_support_to_580 _ h


private theorem port_WrapperSupport_production_coefficient_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.coefficient window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ r.blockScratch.take (max (quotientSwapUnaryDepth window.start window.stop) r.lengthT.length+3)))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact port_WrapperSupport_range580_of_closed r.work1 (by decide +kernel) w (port_WrapperSupport_window_mem hw)
  · exact port_WrapperSupport_range580_of_closed r.work2 (by decide +kernel) w (port_WrapperSupport_window_mem hw)
  · exact port_WrapperSupport_range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact port_WrapperSupport_range580_of_closed r.blockScratch (by decide +kernel) w (List.mem_of_mem_take hw)



attribute [local irreducible] coefficientInverseProgram intervalInverseProgram phaseInverseProgram hInverseProgram
  blockAInverse blockCInverse blockDInverse blockFForward

theorem measuredInverseStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := circuitWires_subset_of_usesOnly (indexedStepInverseUnitary_production_usesOnly T hl)
  simp only [indexedStepInverseUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hH,hG⟩,hF⟩,hE⟩,hD⟩,hC⟩,hB⟩,hA⟩ := hs
  have hsf := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hsf
  have hforwardF : PaperCircuitUsesOnly (List.range 580) (blockFForward r) := by
    intro g hg w hw
    exact hsf.1.1.2 (List.mem_flatMap.mpr ⟨g,hg,hw⟩)
  have hFadj := circuitWires_subset_of_usesOnly hforwardF.adjoint
  have hcAdd := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hcSub := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hcTmp := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hprep := circuitWires_subset_of_usesOnly ((prepareLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hrest := circuitWires_subset_of_usesOnly ((restoreLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hx := circuitWires_subset_of_usesOnly (port_WrapperSupport_gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel))
  have hterm := circuitWires_subset_of_usesOnly (port_WrapperSupport_gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel))
  have hrst := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hrsub := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel)))
  have hrc := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).mono (port_WrapperSupport_support_to_580 _ (by decide +kernel))
  have hrx := port_WrapperSupport_gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hB2 : circuitWires (blockB2 r) ⊆ List.range 580 := circuitWires_subset_of_usesOnly ((hrc.append hrx).append hrc)
  have hci mode phase cursor := (coefficientInverseProgram_support_layout n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) _ _ mode phase .work2 hl.coefficient).trans (fun _ h => port_WrapperSupport_production_coefficient_support _ _ h)
  have hii mode phase cursor := (intervalInverseProgram_support_layout n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 _ _ mode phase .work1 hl.remainder).trans (fun _ h => port_WrapperSupport_production_remainder_support _ _ h)
  have hphase cursor := (phaseInverseProgram_support n cursor r.phaseUpdate r.shiftEpoch).trans (port_WrapperSupport_support_to_580 _ (by decide +kernel))
  unfold measuredInverseStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredInverseStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (hPrograms_support_production n _ T hl.endIteration).2
  · exact hphase _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨hFadj,hprep⟩,hcAdd⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hcAdd,hx⟩,hcTmp⟩,hcSub⟩,hcTmp⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨⟨⟨hcTmp,hcSub⟩,hcTmp⟩,hrest⟩,hD⟩,hC⟩,⟨hterm,hrst⟩,hterm⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hterm,hrst⟩,hterm⟩,hB2⟩,hrsub⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hrsub,hA⟩


attribute [local irreducible] measuredStepProgram measuredInverseStepProgram

theorem measuredScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨measuredStepProgram_support_production n _ _ head,ih _⟩

theorem measuredInverseScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredInverseScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredInverseScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨ih _,measuredInverseStepProgram_support_production n _ _ head⟩

theorem measuredEEAForwardProgram_support_production (n start : Nat) :
    straightWires (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production

theorem measuredEEAReverseProgram_support_production (n start : Nat) :
    straightWires (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredInverseScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production


theorem preprocessProgram_support (n start : Nat) :
    straightWires (preprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaCenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires workRegistersPrepare ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires eeaLengthSetup ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold preprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem unpreprocessProgram_support (n start : Nat) :
    straightWires (unpreprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaUncenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires eeaLengthUndo ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires workRegistersRestore ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold unpreprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem productionParityProgram_support (n start : Nat) :
    straightWires (productionParityProgram n start).2 ⊆ List.range 580 := by
  exact eeaParityProgram_support n start (List.range' 263 256) (List.range' 4 255)
    secp256k1ModulusBits 560 561 562 2 (List.range 580)
    (by simp) (by simp [secp256k1ModulusBits])
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => port_WrapperSupport_support_to_580 _ (by decide +kernel) _ h)


attribute [local irreducible] preprocessProgram unpreprocessProgram productionParityProgram
  measuredEEAForwardProgram measuredEEAReverseProgram
  eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation canonicalWork2InverseRotation
  terminalEpochCompression terminalWork1Clear

theorem measuredForwardWrapperProgram_support (n start : Nat) :
    straightWires (measuredForwardWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (canonicalWork2Rotation ++ terminalEpochCompression) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredForwardWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredForwardWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · exact preprocessProgram_support n _
  · exact measuredEEAForwardProgram_support_production n _
  · simpa only [literalProgram_support] using hmid
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hclear

theorem measuredReverseWrapperProgram_support (n start : Nat) :
    straightWires (measuredReverseWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (terminalEpochCompression ++ canonicalWork2InverseRotation) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredReverseWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredReverseWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support] using hclear
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hmid
  · exact measuredEEAReverseProgram_support_production n _
  · exact unpreprocessProgram_support n _


private theorem port_WrapperSupport_exchanged_580_in_base (w : Wire) (hw : w ∈ List.range 580) :
    eeaWorkspaceExchange w ∈ windowBaseSupport := by
  have h : (List.range 580).all (fun w => decide (eeaWorkspaceExchange w < 837)) = true := by decide +kernel
  have hlt := of_decide_eq_true ((List.all_eq_true.mp h) w hw)
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl hlt)

theorem measuredForwardDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredForwardDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredForwardDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact port_WrapperSupport_exchanged_580_in_base v (measuredForwardWrapperProgram_support n start hv)

theorem measuredReverseDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredReverseDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredReverseDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact port_WrapperSupport_exchanged_580_in_base v (measuredReverseWrapperProgram_support n start hv)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WrapperSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.InPlaceSupport -/
section Port_InPlaceSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_InPlaceSupport_swap_support : circuitWires fig15SwapOutput ⊆ List.range 836 := by
  intro w hw
  simp only [circuitWires,fig15SwapOutput,List.mem_flatMap] at hw
  obtain ⟨g,⟨i,hi,hg⟩,hw⟩ := hw
  simp only [List.mem_range] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw <;>
    simp only [List.mem_range] <;> dsimp only [Wire] at * <;> omega

private theorem port_InPlaceSupport_range_in_base (k : Nat) (hk : k ≤ 837) : List.range k ⊆ windowBaseSupport := by
  intro w hw
  have := List.mem_range.mp hw
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl (by omega))
private theorem port_InPlaceSupport_data_in_base : List.range' 580 256 ⊆ windowBaseSupport := by
  intro w hw
  apply port_InPlaceSupport_range_in_base 837 (by omega)
  simp only [List.mem_range'_1] at hw
  exact List.mem_range.mpr (by omega)

theorem correctionCompiled_support (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    straightWires (correctionCompiled n start ws prior).2 ⊆ ws := by
  unfold correctionCompiled
  induction ws generalizing prior with
  | nil => simp [registerCorrectionProgram,straightWires]
  | cons w ws ih =>
    cases prior with
    | nil => simp [registerCorrectionProgram,straightWires]
    | cons i rest =>
      simp only [registerCorrectionProgram,recordGates_support]
      intro z hz
      simp only [circuitWires,pauliZ,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        gateWires,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,or_self] at hz
      rcases hz with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem w (ih rest h)

attribute [local irreducible] unmultiplyDataProgram multiplyDataProgram multiplyWorkProgram
  measuredForwardWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_support_static (n start : Nat) :
    straightWires (divisionCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,port_InPlaceSupport_swap_support.trans (port_InPlaceSupport_range_in_base _ (by omega))⟩

theorem multiplicationCleanupProgram_support_static (n start : Nat) :
    straightWires (multiplicationCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,measuredReverseDataBankProgram_support_static n _,port_InPlaceSupport_swap_support.trans (port_InPlaceSupport_range_in_base _ (by omega))⟩

theorem divisionCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans port_InPlaceSupport_data_in_base,divisionCleanupProgram_support_static n start⟩

theorem divisionAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredReverseDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,divisionCorrectionProgram_support_static n _ _⟩

theorem multiplicationCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans port_InPlaceSupport_data_in_base,multiplicationCleanupProgram_support_static n start⟩

theorem multiplicationAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredForwardDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,multiplicationCorrectionProgram_support_static n _ _⟩

theorem divisionProgram_support_static (n start : Nat) :
    straightWires (divisionProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionProgram,appendCompiled_support,List.append_subset]
  refine ⟨⟨(measuredForwardWrapperProgram_support n start).trans (port_InPlaceSupport_range_in_base _ (by omega)),multiplyWorkProgram_support_static n _⟩,?_⟩
  exact collectProgram_support n (divisionAfterResetProgram n) windowBaseSupport
    (divisionAfterResetProgram_support_static n) _ port_InPlaceSupport_data_in_base _ _

theorem multiplicationProgram_support_static (n start : Nat) :
    straightWires (multiplicationProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationProgram,appendCompiled_support,List.append_subset]
  refine ⟨multiplyWorkProgram_support_static n start,?_⟩
  exact collectProgram_support n (multiplicationAfterResetProgram n) windowBaseSupport
    (multiplicationAfterResetProgram_support_static n) _ port_InPlaceSupport_data_in_base _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_InPlaceSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CoordinateSupport -/
section Port_CoordinateSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Complete coordinate candidate allocation, including the zero-divisor flag. -/
def coordinateBaseSupport : List Wire := 837 :: windowBaseSupport
private theorem port_CoordinateSupport_old_in_complete : windowBaseSupport ⊆ coordinateBaseSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)
private theorem port_CoordinateSupport_zero_layout_in_complete : zeroAllowedLayout ⊆ coordinateBaseSupport := by
  intro w hw
  simp only [zeroAllowedLayout,List.mem_append,List.mem_range,List.mem_singleton] at hw
  simp only [coordinateBaseSupport,windowBaseSupport,List.mem_cons,List.mem_append,List.mem_range,List.mem_nil_iff,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega
private theorem port_CoordinateSupport_zero_wrapper_literals :
    circuitWires fig15ZeroPrepare ⊆ coordinateBaseSupport ∧
    circuitWires fig15ZeroRestore ⊆ coordinateBaseSupport := by
  constructor
  · intro w hw
    apply port_CoordinateSupport_zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl (Or.inl hw)
  · intro w hw
    apply port_CoordinateSupport_zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr hw

theorem zeroDivisionProgram_support_static (n start : Nat) :
    straightWires (zeroDivisionProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨port_CoordinateSupport_zero_wrapper_literals.1,(divisionProgram_support_static n start).trans port_CoordinateSupport_old_in_complete⟩,port_CoordinateSupport_zero_wrapper_literals.2⟩

theorem zeroMultiplicationProgram_support_static (n start : Nat) :
    straightWires (zeroMultiplicationProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroMultiplicationProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨port_CoordinateSupport_zero_wrapper_literals.1,(multiplicationProgram_support_static n start).trans port_CoordinateSupport_old_in_complete⟩,port_CoordinateSupport_zero_wrapper_literals.2⟩

attribute [local irreducible] fieldLookupAddProgram signedFieldProgram zeroDivisionProgram
  pointSquareProgram zeroMultiplicationProgram xNegateProgram

theorem coordinateProgram_support_static (start : Nat) :
    straightWires (coordinateProgram start).2 ⊆ coordinateBaseSupport := by
  have ha : List.range' 263 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  have hf field cursor := (fieldLookupAddProgram_support_static field _ ha (by simp) cursor).trans port_CoordinateSupport_old_in_complete
  have hs field cursor := (signedFieldProgram_support_static field cursor).trans port_CoordinateSupport_old_in_complete
  unfold coordinateProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coordinateSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf _ _
  · exact hs _ _
  · exact zeroDivisionProgram_support_static _ _
  · exact (pointSquareProgram_support_static _ _).trans port_CoordinateSupport_old_in_complete
  · exact hf _ _
  · exact zeroMultiplicationProgram_support_static _ _
  · exact (xNegateProgram_support_static _ _).trans port_CoordinateSupport_old_in_complete
  · exact hf _ _
  · exact hs _ _
theorem zeroDivision_touches837 (n start : Nat) :
    837 ∈ straightWires (zeroDivisionProgram n start).2 := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.mem_append]
  left; left
  simp only [fig15ZeroPrepare,nonzeroInputPrepare,circuitWires,List.flatMap_append,List.mem_append]
  right
  simp [gateWires]

theorem coordinateProgram_touches837 (start : Nat) :
    837 ∈ straightWires (coordinateProgram start).2 := by
  simp only [coordinateProgram,coordinateSegments,sequenceProgram,appendCompiled_support,List.mem_append]
  exact Or.inr (Or.inr (Or.inl (zeroDivision_touches837 _ _)))
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CoordinateSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowSupport -/
section Port_WindowSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Mapping a shared allocation through a fixed wire permutation commutes with
sequential compilation, without expanding any window body. -/
theorem sequenceProgram_mapped_support (n : Nat) (ps : List (FixedSegment n))
    (e : Wire → Wire) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, (straightWires (p start).2).map e ⊆ support) (start : Nat) :
    (straightWires (sequenceProgram n ps start).2).map e ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support,List.map_append,List.append_subset]
    exact ⟨h p (by simp) start,ih (fun q hq => h q (by simp [hq])) _⟩

theorem signedAddressCircuit_support_static :
    (circuitWires (signedAddressCircuit 836 854 pointLookupAddress)).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
  have hx (q : Wire) (hq : q ∈ windowBaseSupport) :
      circuitWires (tableXorGates q pointLookupAddress) ⊆ windowBaseSupport := by
    intro z hz
    obtain ⟨g,hg,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    have hw' : w ∈ windowBaseSupport := by simp [windowBaseSupport,pointLookupAddress] at hw ⊢; omega
    rcases (show z = q ∨ z = w by simpa [gateWires] using hz) with rfl | rfl
    · exact hq
    · exact hw'
  have hp : circuitWires (signedAddressCircuit 836 854 pointLookupAddress) ⊆ windowBaseSupport := by
    simpa only [signedAddressCircuit,circuitWires,List.flatMap_append,List.append_subset] using
      And.intro (hx 836 (by simp [windowBaseSupport])) (hx 854 (by simp [windowBaseSupport]))
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact List.mem_append_left _ (List.mem_append_left _ (windowBaseSupport_relocated v (hp hv)))

/-- The remaining arithmetic obligation is explicit. The correction and both
negation segments have unconditional concrete support proofs. -/
theorem actualBatchedWindow_support_of_coordinate (w : OddWindow)
    (hc : ∀ start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires) (start : Nat) :
    straightWires ((actualBatchedWindow w).program start) ⊆ batchedResetWires := by
  have hcore cursor : (straightWires (batchedWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
    apply sequenceProgram_mapped_support
    simp only [batchedWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨hc,sharedYNegateProgram_support_static w,placedBatchProgram_support_static w,
      sharedYNegateProgram_support_static w⟩
  simp only [actualBatchedWindow,closedWindow,straightWires_shift,straightWires_relabel,
    batchedWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static,hcore 0⟩,signedAddressCircuit_support_static⟩



theorem actualWindows_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (window : OuterWindow 983040) (hw : window ∈ actualLeftWindows ++ actualRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ batchedResetWires := by
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact (actualFirstWindow_support_static start).trans
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h))
  · exact actualBatchedWindow_support_of_coordinate _ (hc _) start
  · exact actualBatchedWindow_support_of_coordinate _ (hc _) start

theorem batchedOuter_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires ⊆ batchedResetWires := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))
  · exact List.Subset.refl _
  · simp [batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_of_coordinate hc window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

/-- Conditional assembly only: the concrete coordinate compiler support must
still be supplied. This is not an unconditional Streaming resource certificate. -/
theorem batchedOuter_qubits_le_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 3931 := by
  have hs := batchedOuter_support_of_coordinate hc count start read history
  have hfin : ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      batchedResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq batchedResetWires_length)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CompleteSupport -/
section Port_CompleteSupport

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Static allocation includes the zero-divisor flag even though the reset list omits it. -/
def completeBatchedSupport : List Wire := 837 :: batchedResetWires

theorem completeBatchedSupport_length : completeBatchedSupport.length = 3932 := by
  simp only [completeBatchedSupport,List.length_cons,batchedResetWires_length]

private theorem port_CompleteSupport_old_in_complete : batchedResetWires ⊆ completeBatchedSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)

theorem sharedCoordinateProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have h := coordinateProgram_support_static start hv
  rcases List.mem_cons.mp h with rfl | h
  · have he : windowAddressPerm 855 (by decide) 837 = 837 := by decide +kernel
    rw [he]
    exact List.mem_cons_self
  · exact port_CompleteSupport_old_in_complete (List.mem_append_left _ (List.mem_append_left _ (windowBaseSupport_relocated v h)))

theorem actualBatchedWindow_support_static (w : OddWindow) (start : Nat) :
    straightWires ((actualBatchedWindow w).program start) ⊆ completeBatchedSupport := by
  have hcore cursor : (straightWires (batchedWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
    apply sequenceProgram_mapped_support
    simp only [batchedWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨sharedCoordinateProgram_support_static w,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans port_CompleteSupport_old_in_complete,
      fun cursor => (placedBatchProgram_support_static w cursor).trans port_CompleteSupport_old_in_complete,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans port_CompleteSupport_old_in_complete⟩
  simp only [actualBatchedWindow,closedWindow,straightWires_shift,straightWires_relabel,
    batchedWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static.trans port_CompleteSupport_old_in_complete,hcore 0⟩,
    signedAddressCircuit_support_static.trans port_CompleteSupport_old_in_complete⟩

theorem actualWindows_support_static
    (window : OuterWindow 983040) (hw : window ∈ actualLeftWindows ++ actualRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ completeBatchedSupport := by
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact (actualFirstWindow_support_static start).trans
      (fun _ h => port_CompleteSupport_old_in_complete (List.mem_append_left _ (List.mem_append_left _ h)))
  · exact actualBatchedWindow_support_static _ start
  · exact actualBatchedWindow_support_static _ start

theorem batchedOuter_support_static
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact port_CompleteSupport_old_in_complete (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))
  · exact port_CompleteSupport_old_in_complete
  · simp [completeBatchedSupport,batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem wire837_not_in_old_allocation : 837 ∉ batchedResetWires := by
  simp only [batchedResetWires,resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  norm_num

theorem sharedCoordinateProgram_touches837 (w : OddWindow) (start : Nat) :
    837 ∈ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  exact List.mem_map.mpr ⟨837,coordinateProgram_touches837 start,by decide +kernel⟩

theorem old_coordinate_support_false (w : OddWindow) (start : Nat) :
    ¬ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ batchedResetWires := by
  intro h
  exact wire837_not_in_old_allocation (h (sharedCoordinateProgram_touches837 w start))

/-- An upper bound on the actual program's deduplicated wire set, not an exact usage count. -/
theorem batchedOuter_qubits_le_3932
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 3932 := by
  have hs := batchedOuter_support_static count start read history
  have hfin : ((batchedOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      completeBatchedSupport.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq completeBatchedSupport_length)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CompleteSupport

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CrossWindowWeights -/
section Port_CrossWindowWeights

namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological outputs from later windows have the higher binary weights. -/
theorem fourierWordLSB_append (xs ys : List Bool) :
    fourierWordLSB (xs ++ ys) = fourierWordLSB xs + 2 ^ xs.length * fourierWordLSB ys := by
  induction xs with
  | nil => simp [fourierWordLSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordLSB, List.length_cons, ih, pow_succ]
    ring

/-- Reversing the newest-first feedback history restores chronological output. -/
theorem fourierWordLSB_updated_history (bits prior : List Bool) :
    fourierWordLSB (bits.reverse ++ prior).reverse =
      fourierWordLSB prior.reverse + 2 ^ prior.length * fourierWordLSB bits := by
  rw [List.reverse_append, List.reverse_reverse, fourierWordLSB_append, List.length_reverse]

/-- Input words use the opposite convention: the first window is most significant. -/
theorem fourierWordMSB_append (xs ys : List Bool) :
    fourierWordMSB (xs ++ ys) = fourierWordMSB xs * 2 ^ ys.length + fourierWordMSB ys := by
  induction xs with
  | nil => simp [fourierWordMSB]
  | cons b xs ih =>
    simp only [List.cons_append, fourierWordMSB, List.length_append, ih, pow_add]
    ring

-- Both sides of the signed-address boundary, including both extreme addresses.
example : [0, 32767, 32768, 65535].map (signedTableOdd 32768) =
    [-65535, -1, 1, 65535] := by decide +kernel

-- Two radix-65536 input windows. The fixed offset cancels both centered digits.
example : ([0, 32767, 32768, 65535] : List Nat).all (fun a =>
    [0, 32767, 32768, 65535].all (fun b =>
      65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 +
        signedTableOdd 32768 b == 2 * ((a : Int) * 65536 + b))) = true := by
  decide +kernel

example : fourierWordLSB (List.replicate 16 false ++ true :: List.replicate 15 false) =
    65536 := by decide +kernel

/-- The offset cancellation holds for every pair of input digits, including the
sign boundary. Multiplication by a half-point turns the right side into the
ordinary unsigned two-window scalar. -/
theorem two_window_signed_offset (a b : Nat) :
    65535 * (65536 + 1) + signedTableOdd 32768 a * 65536 + signedTableOdd 32768 b =
      2 * ((a : Int) * 65536 + b) := by
  rw [signedTableOdd_value, signedTableOdd_value]
  ring

/-- Splitting a Fourier word at a window boundary retains all feedback phases. -/
theorem fourierBitAmplitude_append (dir : PhaseDir) (xs ys prior bs cs : List Bool)
    (hl : bs.length = xs.length) :
    fourierBitAmplitude dir (xs ++ ys) prior (bs ++ cs) =
      fourierBitAmplitude dir xs prior bs *
        fourierBitAmplitude dir ys (bs.reverse ++ prior) cs := by
  induction xs generalizing prior bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hl
    subst bs
    simp [fourierBitAmplitude]
  | cons a xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, fourierBitAmplitude]
      rw [ih (b :: prior) bs (by simpa using hl)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      ring

/-- Actual feedback order for any number of complete windows. -/
theorem window_history_fold (windows : List (List Bool)) (prior : List Bool) :
    windows.foldl (fun history bits => bits.reverse ++ history) prior =
      windows.flatten.reverse ++ prior := by
  induction windows generalizing prior with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.foldl_cons, ih, List.flatten_cons, List.reverse_append, List.append_assoc]

/-- Product of the individual window amplitudes, with the actual newest-first
history carried from one window to the next. -/
noncomputable def windowFourierAmplitude (dir : PhaseDir) :
    List (List Bool × List Bool) → List Bool → ℂ
  | [], _ => 1
  | (input, output) :: windows, prior =>
      fourierBitAmplitude dir input prior output *
        windowFourierAmplitude dir windows (output.reverse ++ prior)

theorem windowFourierAmplitude_flatten (dir : PhaseDir)
    (windows : List (List Bool × List Bool)) (prior : List Bool)
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows prior =
      fourierBitAmplitude dir (windows.map Prod.fst).flatten prior
        (windows.map Prod.snd).flatten := by
  induction windows generalizing prior with
  | nil => simp [windowFourierAmplitude, fourierBitAmplitude]
  | cons w windows ih =>
    simp only [windowFourierAmplitude, List.map_cons, List.flatten_cons]
    rw [fourierBitAmplitude_append dir _ _ _ _ _ (hl w (by simp)),
      ih _ (fun v hv => hl v (List.mem_cons_of_mem w hv))]

/-- The entire axis has one Fourier kernel; window feedback introduces no
extra phase when the axis starts with empty history. -/
theorem windowFourierAmplitude_kernel (dir : PhaseDir)
    (windows : List (List Bool × List Bool))
    (hl : ∀ w ∈ windows, w.2.length = w.1.length) :
    windowFourierAmplitude dir windows List.nil =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ (windows.map Prod.fst).flatten.length) *
        dyadicFourierKernel dir (windows.map Prod.fst).flatten.length
          (fourierWordMSB (windows.map Prod.fst).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have he : (windows.map Prod.snd).flatten.length =
      (windows.map Prod.fst).flatten.length := by
    induction windows with
    | nil => rfl
    | cons w windows ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [hl w (by simp), ih (fun v hv => hl v (List.mem_cons_of_mem w hv))]
  rw [windowFourierAmplitude_flatten dir windows List.nil hl,
    fourierBitAmplitude_eq dir _ List.nil _ he]
  simp [fourierHistoryPhase, fourierHistoryAngle]

/-- All centered odd digits, including the first mixed-table digit, reconstruct
an unsigned scalar after its fixed initial offset is added. -/
theorem signed_odd_digits_reconstruct (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) +
      (65535 * radixGeometric digits.length : Nat) =
      2 * (windowValue 65536 digits : Int) := by
  induction digits with
  | nil => simp [signedWindowValue, windowValue, radixGeometric]
  | cons d ds ih =>
    simp only [List.map_cons, List.length_cons, signedWindowValue,
      windowValue, radixGeometric, signedTableOdd_value]
    push_cast at ih ⊢
    linear_combination 65536 * ih

/-- Group-level reconstruction uses only the subgroup order, and imposes no
exceptional-point exclusion on the accumulator. -/
theorem signed_odd_digits_point {A : Type} [AddCommGroup A]
    (P : A) (r : Nat) (hr : Odd r) (hP : r • P = 0) (digits : List Nat) :
    signedWindowValue 65536 (digits.map (signedTableOdd 32768)) •
        signedWindowHalfPoint P r +
      (65535 * radixGeometric digits.length) • signedWindowHalfPoint P r =
        windowValue 65536 digits • P := by
  rw [← natCast_zsmul (signedWindowHalfPoint P r) (65535 * radixGeometric digits.length),
    ← add_zsmul, signed_odd_digits_reconstruct]
  rw [show 2 * (windowValue 65536 digits : Int) =
    (windowValue 65536 digits : Int) + (windowValue 65536 digits : Int) by ring,
    add_zsmul, natCast_zsmul, ← nsmul_add,
    signedWindowHalfPoint_double P r hr hP]

/-- A fixed-width list of windows retains leading zero windows. -/
theorem fixed_windows_flatten_length (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    windows.flatten.length = w * windows.length := by
  induction windows with
  | nil => simp
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]
    ring

/-- Chronological window outputs are the little-endian radix digits of the
integer accepted by the decoder. -/
theorem output_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordLSB windows.flatten = windowValue (2 ^ w) (windows.map fourierWordLSB) := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    simp only [List.flatten_cons, List.map_cons, windowValue, fourierWordLSB_append]
    rw [hw bits (by simp), ih (fun bs hb => hw bs (List.mem_cons_of_mem bits hb))]

private theorem port_CrossWindowWeights_windowValue_append (base : Nat) (xs ys : List Nat) :
    windowValue base (xs ++ ys) = windowValue base xs + base ^ xs.length * windowValue base ys := by
  induction xs with
  | nil => simp [windowValue]
  | cons x xs ih =>
    simp only [List.cons_append, windowValue, List.length_cons, ih, pow_succ]
    ring

/-- Input windows run in descending significance, opposite to emitted output
weights. This is the unsigned scalar reconstructed by the signed point tables. -/
theorem input_windows_value (w : Nat) (windows : List (List Bool))
    (hw : ∀ bits ∈ windows, bits.length = w) :
    fourierWordMSB windows.flatten =
      windowValue (2 ^ w) (windows.map fourierWordMSB).reverse := by
  induction windows with
  | nil => rfl
  | cons bits windows ih =>
    have ht := fun bs hb => hw bs (List.mem_cons_of_mem bits hb)
    simp only [List.flatten_cons, List.map_cons, List.reverse_cons,
      fourierWordMSB_append, port_CrossWindowWeights_windowValue_append, List.length_reverse, List.length_map,
      windowValue]
    rw [ih ht, fixed_windows_flatten_length w windows ht, pow_mul]
    ring

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CrossWindowWeights

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CrossWindowPoint -/
section Port_CrossWindowPoint

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1

/-- The sign bit and the unsigned value agree even at the two central digits. -/
theorem reused_window_digit_low (s : BasisState) :
    windowRawDigit 0 s < 32768 ↔ s 870 = false := by
  have hb := boolWordToNat_lt_pow_two (wireValues (windowAddressBits 0) s)
  simp only [wireValues, List.length_map, windowAddressBits, List.length_range'] at hb
  change boolWordToNat (wireValues (windowAddressBits 0) s) < 32768 at hb
  cases hh : s 870 <;> simp_all [windowRawDigit, windowBankStart]

/-- Actual signed table selection gives a centered odd scalar at its fixed
power-of-two weight. No accumulator point is excluded. -/
theorem reused_window_selected_odd (P : Point) (j : Nat) (s : BasisState) :
    (if s 870 then oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))
      else -oddWindowPoint P j (signedTableAddress 32768 (windowRawDigit 0 s))) =
    signedTableOdd 32768 (windowRawDigit 0 s) •
      ((2 ^ (16 * j)) • signedWindowHalfPoint P order) := by
  have ha := signedTableAddress_bound 32768 (windowRawDigit 0 s) (windowRawDigit_bound 0 s)
  simp only [oddWindowPoint, Nat.mod_eq_of_lt ha, signedTableOdd]
  cases hs : s 870
  · rw [if_neg (by decide), if_pos ((reused_window_digit_low s).mpr hs)]
    simp only [neg_zsmul, natCast_zsmul]
  · rw [if_pos rfl, if_neg (by intro h; have hh := (reused_window_digit_low s).mp h; simp [hs] at hh)]
    simp only [natCast_zsmul]

/-- The corrected actual left window has precisely its scalar digit action. -/
theorem actual_left_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 15) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q (.left j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.left j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]

/-- The corrected actual right window has precisely its scalar digit action. -/
theorem actual_right_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (j : Fin 13) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q (.right j) s =
      pointWrite (P + signedTableOdd 32768 (windowRawDigit 0 s) •
        ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)) s := by
  rw [actualBatchedWindowState_selected Q hQ hn (.right j) s hs P hP]
  simp only [windowPoint, reused_window_selected_odd]
/-- The mixed first table obeys the same centered odd-digit formula as the
later tables, including any row whose resulting point is infinity. -/
theorem actual_first_window_digit (Q : Point) (s : BasisState) :
    actualFirstWindowState Q s =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (windowRawDigit 0 s) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  have ha : tableAddressValue (List.range' 855 16) s = windowRawDigit 0 s := by
    simp [tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  have hd : (2 ^ (16 * 15)) • signedWindowHalfPoint G order +
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order = (2 ^ (16 * 15)) • G := by
    rw [← nsmul_add, signedWindowHalfPoint_double G order (by decide +kernel)
      generator_nsmul_eq_zero]
  have he := signedTable_point ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)
    32768 (windowRawDigit 0 s)
  rw [hd] at he
  have hh : signedWindowHalfPoint ((2 ^ (16 * 15)) • G) order =
      (2 ^ (16 * 15)) • signedWindowHalfPoint G order := by
    exact smul_comm ((order + 1) / 2) (2 ^ (16 * 15)) G
  simp only [actualFirstWindowState, firstWindowTable, ha, hh]
  rw [sub_eq_iff_eq_add.mp he]
  rfl

/-- Once the actual signed digits have been accumulated, the two initial
 offsets cancel exactly. This is an exact group identity, without a loss term. -/
theorem two_axis_signed_digits (Q : Point) (hQ : order • Q = 0)
    (left right : List Nat) (hl : left.length = 16) (hr : right.length = 13) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 (left.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 (right.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      windowValue 65536 left • G + windowValue 65536 right • Q := by
  have hleft := signed_odd_digits_point G order (by decide +kernel)
    generator_nsmul_eq_zero left
  have hright := signed_odd_digits_point Q order (by decide +kernel) hQ right
  rw [hl] at hleft
  rw [hr] at hright
  change _ + axisWindowOffset G 16 = _ at hleft
  change _ + axisWindowOffset Q 13 = _ at hright
  rw [← hleft, ← hright]
  abel

/-- In bit-word form, the signed tables reconstruct exactly the two integers
used as input exponents by the 256/208 Fourier kernels. -/
theorem two_axis_input_words (Q : Point) (hQ : order • Q = 0)
    (left right : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hlw : ∀ bits ∈ left, bits.length = 16) (hrw : ∀ bits ∈ right, bits.length = 16) :
    axisWindowOffset G 16 + axisWindowOffset Q 13 +
      signedWindowValue 65536 ((left.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint G order +
      signedWindowValue 65536 ((right.map fourierWordMSB).reverse.map (signedTableOdd 32768)) •
        signedWindowHalfPoint Q order =
      fourierWordMSB left.flatten • G + fourierWordMSB right.flatten • Q := by
  rw [input_windows_value 16 left hlw, input_windows_value 16 right hrw]
  exact two_axis_signed_digits Q hQ _ _ (by simpa using hl) (by simpa using hr)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CrossWindowPoint

/-! Our contribution module: ShorECDLP.Submission.Entrant.Streaming.Contributions.UniformAcceptance -/
section Port_UniformAcceptance

open scoped BigOperators
open ShorECDLP.Quantum.PhaseEstimation
namespace ShorECDLP.Acceptance
noncomputable section

lemma sum_range_first (N : ℕ) :
    ∑ x ∈ Finset.range N, (x:ℝ) = (N:ℝ)*((N:ℝ)-1)/2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_second (N : ℕ) :
    ∑ x ∈ Finset.range N, (x:ℝ)^2 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_quadratic (N : ℕ) (a b c : ℝ) :
    ∑ x ∈ Finset.range N, (a*(x:ℝ)^2+b*(x:ℝ)+c) =
      a*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6) + b*((N:ℝ)*((N:ℝ)-1)/2) + (N:ℝ)*c := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_first, sum_range_second,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sum_range_difference_sq (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^2 =
      (N:ℝ)^2*((N:ℝ)^2-1)/6 := by
  simp_rw [show ∀ x y : ℕ, ((x:ℝ)-(y:ℝ))^2 =
      1*(y:ℝ)^2+(-2*(x:ℝ))*(y:ℝ)+(x:ℝ)^2 by intros; ring,
    sum_quadratic]
  trans ∑ x ∈ Finset.range N,
      ((N:ℝ)*(x:ℝ)^2 + (-((N:ℝ)*((N:ℝ)-1)))*(x:ℝ) +
        ((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_quadratic]; ring

lemma eigen_mul_conj (t : ℝ) (x y : ℕ) :
    (eigenvalue t ^ x * star (eigenvalue t ^ y)).re =
      Real.cos (2*Real.pi*t*((x:ℝ)-(y:ℝ))) := by
  rw [eigenvalue_pow_eq_eigenvalue_mul, eigenvalue_pow_eq_eigenvalue_mul]
  simp only [eigenvalue, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [Complex.exp_re]
  simp
  congr 1
  ring

lemma geometric_normSq (N : ℕ) (t : ℝ) :
    Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) =
      (N:ℝ)⁻¹^2 * ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
        Real.cos (2*Real.pi*t*((x:ℝ)-(y:ℝ))) := by
  rw [Complex.normSq_mul]
  have hs (z : ℂ) : Complex.normSq z = (z * star z).re := by
    simp [Complex.mul_conj]
  rw [hs (∑ x ∈ Finset.range N, eigenvalue t ^ x)]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum,
    eigen_mul_conj]
  simp only [Complex.normSq_inv, Complex.normSq_natCast]
  rw [Finset.sum_comm]
  simp only [pow_two]
  ring

/-- A quadratic lower bound for the exact finite Fourier peak. -/
theorem geometric_quadratic (N : ℕ) (hN : 0 < N) (t : ℝ) :
    1 - Real.pi^2 * ((N:ℝ)*t)^2 / 3 ≤
      Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [geometric_normSq]
  have hb := Finset.sum_le_sum (s := Finset.range N) (fun x hx =>
    Finset.sum_le_sum (s := Finset.range N) (fun y hy =>
      Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*t*((x:ℝ)-(y:ℝ)))))
  have hid : (∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
      (1 - (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2)) =
      (N:ℝ)^2 - 2*Real.pi^2*t^2*((N:ℝ)^2*((N:ℝ)^2-1)/6) := by
    simp_rw [show ∀ x y : ℕ, (1 - (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2) =
        1 - (2*Real.pi^2*t^2)*((x:ℝ)-(y:ℝ))^2 by intros; ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_difference_sq]
    simp
    ring
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (N:ℝ)⁻¹)
  have he : (N:ℝ)⁻¹^2 * ((N:ℝ)^2 - 2*Real.pi^2*t^2*((N:ℝ)^2*((N:ℝ)^2-1)/6)) =
      1 - Real.pi^2*((N:ℝ)*t)^2/3 + Real.pi^2*t^2/3 := by
    field_simp
    ; ring
  rw [he] at hb'
  nlinarith [sq_nonneg (Real.pi*t)]
end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
noncomputable section

lemma primitive_nonneg (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun y hy => (hf y).continuousAt.continuousWithinAt
    · exact fun y hy => (hf y).hasDerivWithinAt
    · exact fun y hy => hd y ((interior_subset hy) : y ∈ Set.Ici 0)
  exact h0.trans (hm (by simp) hx hx)

lemma sin_lower_three (x : ℝ) (hx : 0 ≤ x) : x-x^3/6 ≤ Real.sin x := by
  have h := primitive_nonneg (fun x => Real.sin x-x+x^3/6)
    (fun x => Real.cos x-1+x^2/2)
    (by intro y; convert (((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 6)) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; nlinarith [Real.one_sub_sq_div_two_le_cos (x := y)]) x hx
  linarith

lemma cos_upper_four (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have h := primitive_nonneg (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (fun x => Real.sin x-x+x^3/6)
    (by intro y; convert (((hasDerivAt_const y (1:ℝ)).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 4).div_const 24)).sub (Real.hasDerivAt_cos y) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [sin_lower_three y hy]) x hx
  linarith

lemma sin_upper_five (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x-x^3/6+x^5/120 := by
  have h := primitive_nonneg (fun x => x-x^3/6+x^5/120-Real.sin x)
    (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (by intro y; convert (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 6)).add
      (((hasDerivAt_id y).pow 5).div_const 120)).sub (Real.hasDerivAt_sin y) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [cos_upper_four y hy]) x hx
  linarith

lemma cos_lower_six_nonneg (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have h := primitive_nonneg (fun x => Real.cos x-1+x^2/2-x^4/24+x^6/720)
    (fun x => x-x^3/6+x^5/120-Real.sin x)
    (by intro y; convert ((((Real.hasDerivAt_cos y).sub (hasDerivAt_const y (1:ℝ))).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).pow 4).div_const 24)).add (((hasDerivAt_id y).pow 6).div_const 720) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [sin_upper_five y hy]) x hx
  linarith

lemma cos_lower_six (x : ℝ) : 1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact cos_lower_six_nonneg x hx
  · simpa only [neg_sq, Even.neg_pow (by decide : Even 4), Even.neg_pow (by decide : Even 6), Real.cos_neg] using cos_lower_six_nonneg (-x) (by linarith)
end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open scoped BigOperators
noncomputable section

lemma power_sum_0 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^0 = (N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_1 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^1 = (N:ℝ)*((N:ℝ)-1)/2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_2 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^2 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_3 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^3 = (N:ℝ)^2*((N:ℝ)-1)^2/4 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_4 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^4 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_5 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^5 = (N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_6 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^6 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_poly_six (N : ℕ) (a0 : ℝ) (a1 : ℝ) (a2 : ℝ) (a3 : ℝ) (a4 : ℝ) (a5 : ℝ) (a6 : ℝ) :
    ∑ x ∈ Finset.range N, ((a6)*(x:ℝ)^6 + (a5)*(x:ℝ)^5 + (a4)*(x:ℝ)^4 + (a3)*(x:ℝ)^3 + (a2)*(x:ℝ)^2 + (a1)*(x:ℝ)^1 + (a0)) =
      a6*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42) + a5*((N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12) + a4*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30) + a3*((N:ℝ)^2*((N:ℝ)-1)^2/4) + a2*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6) + a1*((N:ℝ)*((N:ℝ)-1)/2) + a0*((N:ℝ)) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, power_sum_1, power_sum_2, power_sum_3, power_sum_4, power_sum_5, power_sum_6,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma difference_sum_4 (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^4 = (N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30 := by
  have hi (x : ℕ) : (∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^4) = (0)*(x:ℝ)^6 + (0)*(x:ℝ)^5 + (1*((N:ℝ)))*(x:ℝ)^4 + (-4*((N:ℝ)*((N:ℝ)-1)/2))*(x:ℝ)^3 + (6*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))*(x:ℝ)^2 + (-4*((N:ℝ)^2*((N:ℝ)-1)^2/4))*(x:ℝ)^1 + (1*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30)) := by
    calc
      _ = ∑ y ∈ Finset.range N, ((0)*(y:ℝ)^6 + (0)*(y:ℝ)^5 + (1*(x:ℝ)^0)*(y:ℝ)^4 + (-4*(x:ℝ)^1)*(y:ℝ)^3 + (6*(x:ℝ)^2)*(y:ℝ)^2 + (-4*(x:ℝ)^3)*(y:ℝ)^1 + (1*(x:ℝ)^4)) := by
        apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [sum_poly_six]; ring
  simp_rw [hi]
  rw [sum_poly_six]
  ring

lemma difference_sum_6 (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^6 = (N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84 := by
  have hi (x : ℕ) : (∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^6) = (1*((N:ℝ)))*(x:ℝ)^6 + (-6*((N:ℝ)*((N:ℝ)-1)/2))*(x:ℝ)^5 + (15*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))*(x:ℝ)^4 + (-20*((N:ℝ)^2*((N:ℝ)-1)^2/4))*(x:ℝ)^3 + (15*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30))*(x:ℝ)^2 + (-6*((N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12))*(x:ℝ)^1 + (1*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42)) := by
    calc
      _ = ∑ y ∈ Finset.range N, ((1*(x:ℝ)^0)*(y:ℝ)^6 + (-6*(x:ℝ)^1)*(y:ℝ)^5 + (15*(x:ℝ)^2)*(y:ℝ)^4 + (-20*(x:ℝ)^3)*(y:ℝ)^3 + (15*(x:ℝ)^4)*(y:ℝ)^2 + (-6*(x:ℝ)^5)*(y:ℝ)^1 + (1*(x:ℝ)^6)) := by
        apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [sum_poly_six]; ring
  simp_rw [hi]
  rw [sum_poly_six]
  ring

lemma centered_4 (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^4 = (r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240 := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^4) r]
  trans ∑ x ∈ Finset.range r, ((0)*(x:ℝ)^6 + (0)*(x:ℝ)^5 + (1*(-(r/2:ℕ):ℝ)^0)*(x:ℝ)^4 + (4*(-(r/2:ℕ):ℝ)^1)*(x:ℝ)^3 + (6*(-(r/2:ℕ):ℝ)^2)*(x:ℝ)^2 + (4*(-(r/2:ℕ):ℝ)^3)*(x:ℝ)^1 + (1*(-(r/2:ℕ):ℝ)^4))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_poly_six]
    have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
      exact_mod_cast (by omega : r = 2*(r/2)+1)
    rw [he]
    ring

lemma centered_6 (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^6 = (r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344 := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^6) r]
  trans ∑ x ∈ Finset.range r, ((1*(-(r/2:ℕ):ℝ)^0)*(x:ℝ)^6 + (6*(-(r/2:ℕ):ℝ)^1)*(x:ℝ)^5 + (15*(-(r/2:ℕ):ℝ)^2)*(x:ℝ)^4 + (20*(-(r/2:ℕ):ℝ)^3)*(x:ℝ)^3 + (15*(-(r/2:ℕ):ℝ)^4)*(x:ℝ)^2 + (6*(-(r/2:ℕ):ℝ)^5)*(x:ℝ)^1 + (1*(-(r/2:ℕ):ℝ)^6))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_poly_six]
    have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
      exact_mod_cast (by omega : r = 2*(r/2)+1)
    rw [he]
    ring

end
end ShorECDLP.Acceptance

open scoped BigOperators
namespace ShorECDLP.Acceptance
noncomputable section
open ShorECDLP.Paper2607_13816

/-- Index the centered residues without an integer interval. -/
def residualIndex (r N : ℕ) (k : Fin r) : Fin r :=
  ⟨(N*k.val+r/2)%r, Nat.mod_lt _ (by have := k.isLt; omega)⟩

lemma residualIndex_bijective (r N : ℕ) [Fact (Nat.Prime r)]
    (hN : (N : ZMod r) ≠ 0) : Function.Bijective (residualIndex r N) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hi : Function.Injective (residualIndex r N) := by
    intro a b hab
    apply Fin.ext
    have he : (N:ZMod r) * (a.val:ZMod r) + (r/2:ℕ) =
        (N:ZMod r) * (b.val:ZMod r) + (r/2:ℕ) := by
      have := congrArg (fun j : Fin r => (j.val:ZMod r)) hab
      simpa [residualIndex, Nat.cast_add, Nat.cast_mul] using this
    have he' := mul_left_cancel₀ hN (add_right_cancel he)
    have := congrArg ZMod.val he'
    simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, rfl⟩

lemma raw_round_eq (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    reducedPeakRaw r n k = (2^n*k.val+r/2)/r := by
  have hr : 0 < r := by have := k.isLt; omega
  have he := Nat.mod_add_div r 2
  have h1 := Nat.div_mul_le_self (2^n*k.val+r/2) r
  have h2 := Nat.lt_mul_div_succ (2^n*k.val+r/2) hr
  apply (Nat.div_eq_of_lt_le ?_ ?_)
  · nlinarith
  · nlinarith

lemma raw_residual (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    (2^n:ℕ)*(k.val:ℝ)/(r:ℝ) - (reducedPeakRaw r n k:ℝ) =
      ((residualIndex r (2^n) k).val-(r/2:ℕ):ℝ)/(r:ℝ) := by
  have hr : (r:ℝ) ≠ 0 := by have := k.isLt; exact_mod_cast (by omega : r ≠ 0)
  rw [raw_round_eq r n k hodd]
  have he := Nat.mod_add_div (2^n*k.val+r/2) r
  have heR : (((2^n*k.val+r/2)%r:ℕ):ℝ) + (r:ℝ)*(((2^n*k.val+r/2)/r:ℕ):ℝ) =
      (2^n:ℕ)*(k.val:ℝ)+(r/2:ℕ) := by exact_mod_cast he
  dsimp [residualIndex]
  field_simp
  nlinarith

lemma centered_second (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^2 = (r:ℝ)*((r:ℝ)^2-1)/12 := by
  change (∑ k : Fin r, (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^2) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^2) r]
  have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
    have := Nat.mod_add_div r 2
    exact_mod_cast (by omega : r = 2*(r/2)+1)
  trans ∑ x ∈ Finset.range r, (1*(x:ℝ)^2+(-2*(r/2:ℕ))*(x:ℝ)+(r/2:ℕ)^2)
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_quadratic, he]; ring

end
end ShorECDLP.Acceptance

-- Combined by workspace/acceptance_check.py after AcceptanceAnalytic/Residues.
namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

lemma raw_peak_quadratic (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    1 - Real.pi^2 * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 / (3*(r:ℝ)^2) ≤
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) := by
  have h := geometric_quadratic (2^n) (by positivity)
    ((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ))
  change _ ≤ Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) at h
  have hN : ((2^n:ℕ):ℝ) ≠ 0 := by positivity
  have he : ((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) =
      (2^n:ℕ)*(k.val:ℝ)/r - (reducedPeakRaw r n k:ℝ) := by field_simp
  rw [he, raw_residual r n k hodd] at h
  convert h using 1 ; ring

lemma raw_reduced_mass_eq (r n : ℕ) (k : Fin r) :
    Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) =
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hle := reducedPeakRaw_le r n k
  by_cases heq : reducedPeakRaw r n k = 2^n
  · have hp (t : ℝ) : eigenvalue (t-1)=eigenvalue t := by
      unfold eigenvalue
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-1, ?_⟩
      push_cast
      ring
    simp [reducedPeak, heq, paperPhaseAmplitude, hp]
  · simp [reducedPeak, Nat.mod_eq_of_lt (by omega : reducedPeakRaw r n k < 2^n)]

lemma paper_reduced_eq (r n : ℕ) (hn : r < 2^n) (k : Fin r) :
    paperPeak r n hn k = reducedPeak r n k := by
  apply Fin.ext
  dsimp [paperPeak, reducedPeak, reducedPeakRaw]
  exact (Nat.mod_eq_of_lt (paperPeak r n hn k).isLt).symm

lemma peak_mass_le_one (n : ℕ) (t : ℝ) (v : Fin (2^n)) :
    Complex.normSq (paperPhaseAmplitude n t v.val) ≤ 1 := by
  rw [← paperPhaseAmplitude_totalMass t n]
  exact Finset.single_le_sum (fun (i : Fin (2^n)) _ => Complex.normSq_nonneg (paperPhaseAmplitude n t i.val)) (Finset.mem_univ v)

lemma average_peak_quadratic (r n : ℕ) [Fact (Nat.Prime r)]
    (hodd : r%2=1) (_hN : (2^n:ℕ) ≠ 0) (hNz : ((2^n:ℕ):ZMod r) ≠ 0) :
    (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun k hk =>
    (raw_peak_quadratic r n k hodd).trans_eq (raw_reduced_mass_eq r n k))
  have he : ∑ k : Fin r, (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 =
      (r:ℝ)*((r:ℝ)^2-1)/12 := by
    calc
      _ = ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^2 := by
        exact (residualIndex_bijective r (2^n) hNz).sum_comp (fun k => ((k.val:ℝ)-(r/2:ℕ))^2)
      _ = _ := centered_second r hodd
  simp_rw [show ∀ k : Fin r,
    1 - Real.pi^2 * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 / (3*(r:ℝ)^2) =
    1 - (Real.pi^2/(3*(r:ℝ)^2)) * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 by intro; ring,
    Finset.sum_sub_distrib, ← Finset.mul_sum, he,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hb
  have hid : (r:ℝ) - Real.pi^2/(3*(r:ℝ)^2)*((r:ℝ)*((r:ℝ)^2-1)/12) =
      (r:ℝ)*(1-Real.pi^2/36) + Real.pi^2/(36*(r:ℝ)) := by
    field_simp
    ; ring
  rw [hid] at hb
  exact le_trans (le_add_of_nonneg_right (by positivity)) hb
end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

lemma characterProduct_bijective (r d : ℕ) [Fact (Nat.Prime r)]
    (hd : (d:ZMod r) ≠ 0) : Function.Bijective (paperCharacterProduct d : Fin r → Fin r) := by
  have hi : Function.Injective (paperCharacterProduct d : Fin r → Fin r) := by
    intro a b hab
    apply Fin.ext
    have he : (d:ZMod r)*(a.val:ZMod r) = (d:ZMod r)*(b.val:ZMod r) := by
      have := congrArg (fun j : Fin r => (j.val:ZMod r)) hab
      simpa [paperCharacterProduct, Nat.cast_mul] using this
    have he' := mul_left_cancel₀ hd he
    have := congrArg ZMod.val he'
    simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,rfl⟩

/-- Keep each nonzero character's own peak contribution, with its exact weight. -/
lemma coverage_exact_peak_lower (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) :
    (1/(r:ℝ)) * ∑ k ∈ (Finset.univ.erase (⟨0,(Fact.out : Nat.Prime r).pos⟩ : Fin r)),
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
      Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
        (reducedPeak r m (paperCharacterProduct d k)).val) ≤ reducedCoverageMass r n m d := by
  classical
  let S := Finset.univ.erase (⟨0,(Fact.out : Nat.Prime r).pos⟩ : Fin r)
  let peak := asymmetricPairPeak r n m d hn
  let f : (Fin (2^n) × Fin (2^m)) → ℝ := fun out =>
    if (d:ZMod r) ∈ reducedShiftCandidates r n m out
      then asymmetricPairMass r n m d out else 0
  have hf : ∀ out, 0 ≤ f out := by
    intro out; dsimp [f]; split
    · exact asymmetricPairMass_nonneg _ _ _ _ _
    · rfl
  have hp (k : Fin r) (hk : k ∈ S) :
      (1/(r:ℝ)) * (Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
      Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
        (reducedPeak r m (paperCharacterProduct d k)).val)) ≤ f (peak k) := by
    have hkz : (k.val:ZMod r) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      have hk0 : k ≠ ⟨0,(Fact.out : Nat.Prime r).pos⟩ := (Finset.mem_erase.mp hk).1
      apply hk0; apply Fin.ext
      simpa [ZMod.val_natCast_of_lt k.isLt] using hv
    dsimp [f,peak]
    have hm : (d:ZMod r) ∈ reducedShiftCandidates r n m (asymmetricPairPeak r n m d hn k) :=
      reducedShiftCandidates_correct r n m d hn k hkz
    rw [if_pos hm]
    unfold asymmetricPairMass
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum
      (f := fun i : Fin r =>
        Complex.normSq (paperPhaseAmplitude n ((i.val:ℝ)/r) (paperPeak r n hn k).val) *
        Complex.normSq (paperPhaseAmplitude m ((((d*i.val)%r:ℕ):ℝ)/r)
          (reducedPeak r m (paperCharacterProduct d k)).val))
      (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Finset.mem_univ k)
  calc
    _ = ∑ k ∈ S, (1/(r:ℝ)) *
        (Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
        Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
          (reducedPeak r m (paperCharacterProduct d k)).val)) := Finset.mul_sum ..
    _ ≤ ∑ k ∈ S, f (peak k) := Finset.sum_le_sum hp
    _ = ∑ out ∈ S.image peak, f out := by
      rw [Finset.sum_image]
      intro k _ l _ he
      exact asymmetricPairPeak_injective r n m d hn he
    _ ≤ ∑ out, f out := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun out _ _ => hf out)
    _ = reducedCoverageMass r n m d := rfl

/-- Uniform in the correlation between the two residual marginals. -/
theorem coverage_quadratic (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) (hodd : r%2=1)
    (hN : ((2^n:ℕ):ZMod r) ≠ 0) (hM : ((2^m:ℕ):ZMod r) ≠ 0)
    (hd : (d:ZMod r) ≠ 0) :
    1 - Real.pi^2/18 - 1/(r:ℝ) ≤ reducedCoverageMass r n m d := by
  classical
  have hr := (Fact.out : Nat.Prime r).pos
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  let z : Fin r := ⟨0,hr⟩
  let u (k : Fin r) := Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val)
  let v (k : Fin r) := Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
    (reducedPeak r m (paperCharacterProduct d k)).val)
  have hu (k : Fin r) : u k ≤ 1 := peak_mass_le_one _ _ _
  have hv (k : Fin r) : v k ≤ 1 := peak_mass_le_one _ _ _
  have hp (k : Fin r) : u k + v k - 1 ≤ u k * v k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hu k)) (sub_nonneg.mpr (hv k))]
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase z) (fun k hk => hp k)
  have he := Finset.sum_erase_add Finset.univ (fun k => u k+v k-1) (Finset.mem_univ z)
  have hz : u z+v z-1 ≤ 1 := by linarith [hu z,hv z]
  have huSum : (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k, u k := by
    simpa [u, paper_reduced_eq] using average_peak_quadratic r n hodd (by positivity) hN
  have hvSum : (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k, v k := by
    have heq := (characterProduct_bijective r d hd).sum_comp
      (fun k => Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    dsimp [v]
    rw [heq]
    exact average_peak_quadratic r m hodd (by positivity) hM
  have hl : (r:ℝ)*(1-Real.pi^2/18)-1 ≤ ∑ k ∈ Finset.univ.erase z, u k*v k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he hsum
    linarith
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1/(r:ℝ))
  have hi : (1/(r:ℝ))*((r:ℝ)*(1-Real.pi^2/18)-1) = 1-Real.pi^2/18-1/(r:ℝ) := by
    field_simp
  rw [hi] at hb
  exact hb.trans (coverage_exact_peak_lower r n m d hn)

end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

def peakPolynomial (x : ℝ) : ℝ :=
  1-Real.pi^2*x^2/3+2*Real.pi^4*x^4/45-Real.pi^6*x^6/315

def marginalBound : ℝ := 1-Real.pi^2/36+Real.pi^4/1800-Real.pi^6/141120

lemma pi_sq_le_ten : Real.pi^2 ≤ 10 := by
  have h := Real.pi_lt_d6
  nlinarith [Real.pi_pos]

/-- A finite-size proof: expand the squared amplitude, and lower-bound each cosine.
    The finite-size correction is nonnegative, so no limiting argument is needed. -/
lemma geometric_sextic (N : ℕ) (hN : 0<N) (t : ℝ) (ht : |(N:ℝ)*t| ≤ 1/2) :
    peakPolynomial ((N:ℝ)*t) ≤
      Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  rw [geometric_normSq]
  have hb := Finset.sum_le_sum (s := Finset.range N) (fun x hx =>
    Finset.sum_le_sum (s := Finset.range N) (fun y hy =>
      cos_lower_six (2*Real.pi*t*((x:ℝ)-(y:ℝ)))))
  have hid : (∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
      (1-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2+
        (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^4/24-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^6/720)) =
      (N:ℝ)^2 - (2*Real.pi^2*t^2)*((N:ℝ)^2*((N:ℝ)^2-1)/6) +
      (2*Real.pi^4*t^4/3)*((N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30) -
      (4*Real.pi^6*t^6/45)*((N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84) := by
    simp only [show ∀ x y : ℕ,
      (1-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2+
        (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^4/24-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^6/720) =
      1-(2*Real.pi^2*t^2)*((x:ℝ)-(y:ℝ))^2+
        (2*Real.pi^4*t^4/3)*((x:ℝ)-(y:ℝ))^4-
        (4*Real.pi^6*t^6/45)*((x:ℝ)-(y:ℝ))^6 by intros; ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_range_difference_sq, difference_sum_4, difference_sum_6]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (N:ℝ)⁻¹)
  let z := Real.pi^2*((N:ℝ)*t)^2
  let w := (N:ℝ)⁻¹^2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hw0 : 0 ≤ w := sq_nonneg _
  have hz3 : z ≤ 3 := by
    have hx2 : ((N:ℝ)*t)^2 ≤ 1/4 := by nlinarith [sq_abs ((N:ℝ)*t), abs_nonneg ((N:ℝ)*t)]
    calc
      z ≤ 10*((N:ℝ)*t)^2 := mul_le_mul_of_nonneg_right pi_sq_le_ten (sq_nonneg _)
      _ ≤ 3 := by linarith
  have he : (N:ℝ)⁻¹^2 * ((N:ℝ)^2 - (2*Real.pi^2*t^2)*((N:ℝ)^2*((N:ℝ)^2-1)/6) +
      (2*Real.pi^4*t^4/3)*((N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30) -
      (4*Real.pi^6*t^6/45)*((N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84)) =
      peakPolynomial ((N:ℝ)*t) + w*z*((3-z)/9+w*z*(3-z)/45+(14+10*w^2)*z^2/945) := by
    dsimp [w,z,peakPolynomial]
    field_simp
    ; ring
  rw [he] at hb'
  have hzpos : 0 ≤ 3-z := sub_nonneg.mpr hz3
  have hc : 0 ≤ w*z*((3-z)/9+w*z*(3-z)/45+(14+10*w^2)*z^2/945) := by
    apply mul_nonneg (mul_nonneg hw0 hz0)
    positivity
  linarith

lemma polynomial_marginal (r : ℕ) (hr : 0<r) (hodd : r%2=1) :
    (r:ℝ)*marginalBound ≤ ∑ k : Fin r,
      peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have he : (∑ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ))) =
      (r:ℝ) - (Real.pi^2/(3*(r:ℝ)^2))*((r:ℝ)*((r:ℝ)^2-1)/12) +
      (2*Real.pi^4/(45*(r:ℝ)^4))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240) -
      (Real.pi^6/(315*(r:ℝ)^6))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344) := by
    simp only [show ∀ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) =
      1-(Real.pi^2/(3*(r:ℝ)^2))*((k.val:ℝ)-(r/2:ℕ))^2+
      (2*Real.pi^4/(45*(r:ℝ)^4))*((k.val:ℝ)-(r/2:ℕ))^4-
      (Real.pi^6/(315*(r:ℝ)^6))*((k.val:ℝ)-(r/2:ℕ))^6 by intro; dsimp [peakPolynomial]; ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      centered_second r hodd, centered_4 r hodd, centered_6 r hodd]
    simp
  rw [he]
  let w := (r:ℝ)⁻¹^2
  have hid : (r:ℝ) - (Real.pi^2/(3*(r:ℝ)^2))*((r:ℝ)*((r:ℝ)^2-1)/12) +
      (2*Real.pi^4/(45*(r:ℝ)^4))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240) -
      (Real.pi^6/(315*(r:ℝ)^6))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344) =
      (r:ℝ)*marginalBound +
      (r:ℝ)*w*Real.pi^2*(15-Real.pi^2)/540 + (r:ℝ)*w*Real.pi^6/20160 +
      (r:ℝ)*w^2*7*Real.pi^4*(56-5*Real.pi^2)/302400 +
      31*(r:ℝ)*Real.pi^6*w^3/423360 := by
    dsimp [w,marginalBound]
    field_simp
    ; ring
  rw [hid]
  have h15 : 0 ≤ 15-Real.pi^2 := by linarith [pi_sq_le_ten]
  have h56 : 0 ≤ 56-5*Real.pi^2 := by linarith [pi_sq_le_ten]
  have hw : 0 ≤ w := sq_nonneg _
  have hc : 0 ≤
      (r:ℝ)*w*Real.pi^2*(15-Real.pi^2)/540 + (r:ℝ)*w*Real.pi^6/20160 +
      (r:ℝ)*w^2*7*Real.pi^4*(56-5*Real.pi^2)/302400 +
      31*(r:ℝ)*Real.pi^6*w^3/423360 := by positivity
  linarith

lemma marginal_numeric : (7731:ℝ)/10000 ≤ marginalBound := by
  have hl : (31415:ℝ)/10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hu : Real.pi ≤ (31416:ℝ)/10000 := by linarith [Real.pi_lt_d6]
  have h2 := pow_le_pow_left₀ Real.pi_pos.le hu 2
  have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 31415/10000) hl 4
  have h6 := pow_le_pow_left₀ Real.pi_pos.le hu 6
  dsimp [marginalBound]
  norm_num at h2 h4 h6
  linarith

lemma average_peak_sextic (r n : ℕ) [Fact (Nat.Prime r)]
    (hodd : r%2=1) (hNz : ((2^n:ℕ):ZMod r) ≠ 0) :
    (r:ℝ)*marginalBound ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hNR : ((2^n:ℕ):ℝ) ≠ 0 := by positivity
  have h (k : Fin r) : peakPolynomial
      ((((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))/(r:ℝ)) ≤
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
    have he : ((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) =
        (2^n:ℕ)*(k.val:ℝ)/r - (reducedPeakRaw r n k:ℝ) := by field_simp
    have hs := nearNumerator_abs r n k.val (reducedPeakRaw r n k) hr (reducedPeakRaw_near r n k)
    have hsmall : |((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ))| ≤ 1/2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<(2^n:ℕ))]
      calc
        _ ≤ ((2^n:ℕ):ℝ)*(1/(2*(2^n:ℕ))) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 1/2 := by field_simp
    have hb := geometric_sextic (2^n) (by positivity)
      ((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) hsmall
    change _ ≤ Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) at hb
    rw [he, raw_residual r n k hodd, raw_reduced_mass_eq r n k] at hb
    exact hb
  calc
    _ ≤ ∑ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) := polynomial_marginal r hr hodd
    _ = ∑ k : Fin r, peakPolynomial
        ((((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))/(r:ℝ)) := by
      exact ((residualIndex_bijective r (2^n) hNz).sum_comp
        (fun k => peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)))).symm
    _ ≤ _ := Finset.sum_le_sum (fun k hk => h k)

theorem coverage_of_average (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) (a : ℝ)
    (hl : (r:ℝ)*a ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val))
    (hright : (r:ℝ)*a ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    (hd : (d:ZMod r) ≠ 0) :
    2*a-1-1/(r:ℝ) ≤ reducedCoverageMass r n m d := by
  classical
  have hr := (Fact.out : Nat.Prime r).pos
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  let z : Fin r := ⟨0,hr⟩
  let u (k : Fin r) := Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val)
  let v (k : Fin r) := Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
    (reducedPeak r m (paperCharacterProduct d k)).val)
  have hu (k : Fin r) : u k ≤ 1 := peak_mass_le_one _ _ _
  have hv (k : Fin r) : v k ≤ 1 := peak_mass_le_one _ _ _
  have hp (k : Fin r) : u k + v k - 1 ≤ u k * v k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hu k)) (sub_nonneg.mpr (hv k))]
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase z) (fun k hk => hp k)
  have he := Finset.sum_erase_add Finset.univ (fun k => u k+v k-1) (Finset.mem_univ z)
  have hz : u z+v z-1 ≤ 1 := by linarith [hu z,hv z]
  have huSum : (r:ℝ)*a ≤ ∑ k, u k := by
    simpa [u, paper_reduced_eq] using hl
  have hvSum : (r:ℝ)*a ≤ ∑ k, v k := by
    have heq := (characterProduct_bijective r d hd).sum_comp
      (fun k => Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    dsimp [v]
    rw [heq]
    exact hright
  have hl : (r:ℝ)*(2*a-1)-1 ≤ ∑ k ∈ Finset.univ.erase z, u k*v k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he hsum
    linarith
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1/(r:ℝ))
  have hi : (1/(r:ℝ))*((r:ℝ)*(2*a-1)-1) = 2*a-1-1/(r:ℝ) := by
    field_simp
  rw [hi] at hb
  exact hb.trans (coverage_exact_peak_lower r n m d hn)


/-- Our uniform acceptance improvement, valid for every nonzero logarithm. -/
theorem secpCoverage_546 (d : ℕ) (hd : (d:ZMod ShorECDLP.order) ≠ 0) :
    (546:ℝ)/1000 ≤ reducedCoverageMass ShorECDLP.order 256 208 d := by
  letI : Fact (Nat.Prime ShorECDLP.order) := ⟨ShorECDLP.Secp256k1.order_prime⟩
  have htwo : (2:ZMod ShorECDLP.order) ≠ 0 := by
    change ((2:ℕ):ZMod ShorECDLP.order) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff 2 ShorECDLP.order]
    norm_num [ShorECDLP.order]
  have hN : ((2^256:ℕ):ZMod ShorECDLP.order) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ htwo
  have hM : ((2^208:ℕ):ZMod ShorECDLP.order) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ htwo
  have hodd : ShorECDLP.order%2=1 := by norm_num [ShorECDLP.order]
  have hb := coverage_of_average ShorECDLP.order 256 208 d reducedLeftPrecision_order marginalBound
    (average_peak_sextic ShorECDLP.order 256 hodd hN)
    (average_peak_sextic ShorECDLP.order 208 hodd hM) hd
  have hr : 1/(ShorECDLP.order:ℝ) ≤ 1/10000 := by norm_num [ShorECDLP.order]
  have hn : (546:ℝ)/1000 ≤ 2*marginalBound-1-1/(ShorECDLP.order:ℝ) := by
    linarith [marginal_numeric]
  exact hn.trans hb

end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Secp256k1
noncomputable section

lemma secpVerified_546 (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (546:ℝ)/1000 ≤ reducedVerifiedMass Q d := by
  rw [reducedVerifiedMass_eq Q d hd]
  apply secpCoverage_546 d
  intro hz
  have he := (secpCandidate_correct Q d hd (0:ZMod ShorECDLP.order)).mpr hz.symm
  simp only [ZMod.val_zero, zero_nsmul] at he
  exact hn he.symm

end
end ShorECDLP.Acceptance

end Port_UniformAcceptance
