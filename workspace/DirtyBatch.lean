import ShorECDLP.Submission.Entrant.Streaming.Dirty.DirtyMCX
import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution

namespace ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Compact

def batchOpCircuit (base : Wire) (source : Fin 4) (target : Fin 6) : Circuit :=
  dirtyEndpointTranspositionCircuit (ChallengeMigration.batchWord base ⟨source.val, by omega⟩)
    (ChallengeMigration.batchWord base 4) (ChallengeMigration.batchWord base target)
    (ChallengeMigration.batchFlag base)

theorem batchSwap_geometry (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) :
    DirtyEndpointGeometry (ChallengeMigration.batchWord base ⟨source.val, by omega⟩)
      (ChallengeMigration.batchWord base 4) (ChallengeMigration.batchWord base target)
      (ChallengeMigration.batchFlag base) := by
  refine ⟨ChallengeMigration.batchWord_injective base _,
    ChallengeMigration.batchWord_injective base _, ChallengeMigration.batchWord_injective base _, ?_, ?_⟩
  · intro i j
    exact ⟨ChallengeMigration.batchWord_apart base _ _
        (fun h => hs (congrArg Fin.val h)) i j,
      ChallengeMigration.batchWord_apart base _ _ ht.symm i j⟩
  · intro i
    exact ⟨(Nat.ne_of_lt (ChallengeMigration.batchWord_bound base _ i)).symm,
      (Nat.ne_of_lt (ChallengeMigration.batchWord_bound base _ i)).symm,
      (Nat.ne_of_lt (ChallengeMigration.batchWord_bound base _ i)).symm⟩

attribute [local irreducible] dirtyEndpointTranspositionCircuit

theorem batchOpCircuit_model (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) (st : BasisState)
    (hc : Clean (ChallengeMigration.batchScratch base) st)
    (hz : st (ChallengeMigration.batchFlag base) = false) :
    let out := Classical.run (batchOpCircuit base source target) st
    (∀ j, out ∘ ChallengeMigration.batchWord base j =
      ChallengeMigration.batchSwap source target (fun k => st ∘ ChallengeMigration.batchWord base k) j) ∧
      Clean (ChallengeMigration.batchScratch base) out ∧
      out (ChallengeMigration.batchFlag base) = false ∧
      (∀ w, (∀ i, w ≠ ChallengeMigration.batchWord base target i) → out w = st w) := by
  dsimp only
  unfold batchOpCircuit
  have h := dirtyEndpointTransposition_correct _ _ _ _
    (batchSwap_geometry base source target hs ht) st hz
  refine ⟨?_, ?_, h.2.1, h.2.2⟩
  · intro j
    by_cases hj : j = target
    · subst j
      simpa [ChallengeMigration.batchSwap, Function.update] using h.1
    · simp only [ChallengeMigration.batchSwap, Function.update_of_ne hj]
      funext i
      exact h.2.2 _ (fun k => ChallengeMigration.batchWord_apart base j target hj i k)
  · intro w hw
    rw [h.2.2 w (fun i => by
      have hs' := ChallengeMigration.batchScratch_above base w hw
      have ht' := ChallengeMigration.batchWord_bound base target i
      dsimp [ChallengeMigration.batchFlag] at hs'
      dsimp only [Wire] at *
      omega)]
    exact hc w hw

end ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
