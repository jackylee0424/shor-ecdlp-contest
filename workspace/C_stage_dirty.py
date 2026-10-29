#!/usr/bin/env python3
"""Stage Brief 11's dirty-comparator modules without editing shared drafts.

The generated lab files are named C_*.lean.  Matching importable modules are
written only below the explicitly selected bench's Entrant/Streaming/Dirty/.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re


LAB = Path(__file__).resolve().parent.parent
ROOT_NS = "ShorECDLP.Paper2607_13816.ChallengeMigration"
DIRTY_NS = ROOT_NS + ".Dirty"
STREAM = "ShorECDLP.Submission.Entrant.Streaming"
DIRTY_STREAM = STREAM + ".Dirty"
PROTECTED = "ShorECDLP.Submission.«2607_13816».Challenge"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {text.count(old)}")
    return text.replace(old, new, 1)


def dirty_namespace(text: str) -> str:
    text = text.replace(f"namespace {ROOT_NS}\n", f"namespace {DIRTY_NS}\n")
    text = text.replace(f"end {ROOT_NS}\n", f"end {DIRTY_NS}\n")
    return text


def write_pair(bench_root: Path, relative: str, text: str) -> None:
    lab_name = "C_" + relative.replace("/", "_")
    lab_path = LAB / "workspace" / lab_name
    bench_path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty" / relative
    lab_path.parent.mkdir(parents=True, exist_ok=True)
    bench_path.parent.mkdir(parents=True, exist_ok=True)
    lab_path.write_text(text)
    bench_path.write_text(text)


def map_imports(text: str, protected_names: set[str]) -> str:
    text = re.sub(
        rf"(?m)^import {re.escape(STREAM)}\.(?!Dirty\.)(\S+)$",
        rf"import {DIRTY_STREAM}.\1",
        text,
    )
    for name in protected_names:
        text = text.replace(
            f"import {PROTECTED}.{name}\n",
            f"import {DIRTY_STREAM}.Challenge.{name}\n",
        )
    return text


def dirty_mcx(bench_root: Path) -> None:
    text = (LAB / "workspace/DirtyMCX.lean").read_text()
    addition = r'''

theorem zeroMaskFrom_length_zero (register : List Wire) (bit : Nat) :
    (zeroMaskFrom register 0 bit).length = register.length := by
  induction register generalizing bit with
  | nil => rfl
  | cons w ws ih =>
    rw [zeroMaskFrom]
    simp only [Nat.zero_testBit, Bool.false_eq_true, if_false, List.length_append,
      ih, List.length_cons, List.length_nil]
    omega

theorem zeroMask_length_zero (register : List Wire) :
    (zeroMask register 0).length = register.length :=
  zeroMaskFrom_length_zero register 0

theorem dirtyRegisterEqualCircuit_length
    (a target donor : Fin 513 → Wire) (flag : Wire) :
    (dirtyRegisterEqualCircuit a target donor flag).length = 4096 := by
  simp only [dirtyRegisterEqualCircuit, List.length_append, xorWordCircuit,
    List.length_map, equalityCells, List.length_ofFn, zeroMask_length_zero,
    dirtyMCX_length]

theorem dirtyEndpointTests_length (a b target : Fin 513 → Wire) (flag : Wire) :
    (dirtyEndpointTests a b target flag).length = 8192 := by
  simp only [dirtyEndpointTests, List.length_append, dirtyRegisterEqualCircuit_length]

theorem dirtyEndpointTransposition_length
    (a b target : Fin 513 → Wire) (flag : Wire) :
    (dirtyEndpointTranspositionCircuit a b target flag).length = 17410 := by
  simp only [dirtyEndpointTranspositionCircuit, List.length_append,
    dirtyEndpointTests_length, endpointWordCircuit_length, endpointUpdateCells,
    List.length_ofFn]
'''
    text = replace_once(text, "\nend ShorECDLP.Compact\n", addition + "\nend ShorECDLP.Compact\n", "DirtyMCX end")
    write_pair(bench_root, "DirtyMCX.lean", text)


def protected_modules(bench_root: Path) -> None:
    names = {
        "BatchedEndpoint", "BatchState", "BatchQuery", "BatchExecution",
        "BatchCoherent", "BatchFrame", "BatchPhysical", "BatchPlacement",
        "PlacedBatch", "BatchTemplate", "BatchCost", "WindowBody",
    }
    source_dir = LAB / "workspace/spooky_src"

    # BatchedEndpoint owns the changed gate sequence; all other structure stays upstream.
    text = dirty_namespace((source_dir / "BatchedEndpoint.lean").read_text())
    text = f"import {DIRTY_STREAM}.DirtyMCX\n" + text
    old = '''def batchOpCircuit (base : Wire) (source : Fin 4) (target : Fin 6) : Circuit :=
  endpointTranspositionCircuit (batchWord base ⟨source.val,by omega⟩)
    (batchWord base 4) (batchWord base target) (batchFlag base) (batchScratch base)
'''
    new = '''def batchOpCircuit (base : Wire) (source : Fin 4) (target : Fin 6) : Circuit :=
  ShorECDLP.Compact.dirtyEndpointTranspositionCircuit
    (batchWord base ⟨source.val,by omega⟩) (batchWord base 4)
    (batchWord base target) (batchFlag base)
'''
    text = replace_once(text, old, new, "BatchedEndpoint circuit")
    write_pair(bench_root, "Challenge/BatchedEndpoint.lean", text)

    # State is unchanged but duplicated so every downstream unqualified name is local.
    text = dirty_namespace((source_dir / "BatchState.lean").read_text())
    text = map_imports(text, names)
    write_pair(bench_root, "Challenge/BatchState.lean", text)

    # Keep query facts, replace only the clean V-chain geometry/model section.
    text = dirty_namespace((source_dir / "BatchQuery.lean").read_text())
    text = map_imports(text, names)
    start = text.index("theorem batchWord_layout")
    finish = text.index("theorem batchRawMask_frame", start)
    model = r'''theorem batchSwap_geometry (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) :
    ShorECDLP.Compact.DirtyEndpointGeometry
      (batchWord base ⟨source.val, by omega⟩) (batchWord base 4)
      (batchWord base target) (batchFlag base) := by
  refine ⟨batchWord_injective base _, batchWord_injective base _,
    batchWord_injective base _, ?_, ?_⟩
  · intro i j
    exact ⟨batchWord_apart base _ _ (fun h => hs (congrArg Fin.val h)) i j,
      batchWord_apart base _ _ ht.symm i j⟩
  · intro i
    exact ⟨(Nat.ne_of_lt (batchWord_bound base _ i)).symm,
      (Nat.ne_of_lt (batchWord_bound base _ i)).symm,
      (Nat.ne_of_lt (batchWord_bound base _ i)).symm⟩

attribute [local irreducible] ShorECDLP.Compact.dirtyEndpointTranspositionCircuit

theorem batchOpCircuit_model (base : Wire) (source : Fin 4) (target : Fin 6)
    (hs : source.val ≠ target.val) (ht : target ≠ 4) (st : BasisState)
    (hc : Clean (batchScratch base) st) (hz : st (batchFlag base) = false) :
    let out := Classical.run (batchOpCircuit base source target) st
    (∀ j, out ∘ batchWord base j = batchSwap source target
      (fun k => st ∘ batchWord base k) j) ∧
      Clean (batchScratch base) out ∧ out (batchFlag base) = false ∧
      (∀ w, (∀ i, w ≠ batchWord base target i) → out w = st w) := by
  dsimp only
  unfold batchOpCircuit
  have h := ShorECDLP.Compact.dirtyEndpointTransposition_correct _ _ _ _
    (batchSwap_geometry base source target hs ht) st hz
  refine ⟨?_, ?_, h.2.1, h.2.2⟩
  · intro j
    by_cases hj : j = target
    · subst j
      simpa [batchSwap, Function.update] using h.1
    · simp only [batchSwap, Function.update_of_ne hj]
      funext i
      exact h.2.2 _ (fun k => batchWord_apart base j target hj i k)
  · intro w hw
    rw [h.2.2 w (fun i => by
      have hs' := batchScratch_above base w hw
      have ht' := batchWord_bound base target i
      exact (Nat.ne_of_lt (ht'.trans hs')).symm)]
    exact hc w hw

'''
    text = text[:start] + model + text[finish:]
    write_pair(bench_root, "Challenge/BatchQuery.lean", text)

    for name in ("BatchExecution", "BatchFrame", "PlacedBatch"):
        text = dirty_namespace((source_dir / f"{name}.lean").read_text())
        text = map_imports(text, names)
        write_pair(bench_root, f"Challenge/{name}.lean", text)

    # Normalize the dependent pair's count to a numeral.  This keeps downstream
    # Straight composition from unfolding the entire lookup program merely to
    # compare finish indices.
    text = dirty_namespace((source_dir / "BatchPlacement.lean").read_text())
    text = map_imports(text, names)
    begin = text.index("def placedBatchProgram")
    end = text.index("noncomputable def placedBatchSource", begin)
    replacement = '''def placedBatchProgramRaw (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  relabelCompiled batchPlacement
    (batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath start)

theorem placedBatchProgramRaw_count (w : OddWindow) (start : Nat) :
    (placedBatchProgramRaw w start).1 = 458738 := by
  simp only [placedBatchProgramRaw, relabelCompiled]
  rw [batchedEndpointProgram_count _ _ _ _ _ _ batchWindowTree_layout]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega

def placedBatchStraight (w : OddWindow) (start : Nat) :
    Straight 983040 start (start + 458738) :=
  let p := placedBatchProgramRaw w start
  castFinish (congrArg (fun count => start + count)
    (placedBatchProgramRaw_count w start)) p.2

def placedBatchProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  ⟨458738, placedBatchStraight w start⟩

'''
    text = text[:begin] + replacement + text[end:]
    old_run = '''  exact relabelCompiled_run _ _ _ _ _
    (batchedEndpointProgram_run _ (batchWindowRows w) 1024
      batchWindowTree 836 pointLookupPath start history)
'''
    new_run = '''  simp only [placedBatchStraight, castFinish_instantiate]
  simp only [placedBatchProgramRaw, placedBatchSource, relabelCompiled,
    relabelStraight_instantiate, AdaptiveCircuit.run_relabel,
    batchedEndpointProgram, lookupProgram_run, batchOps_source]
'''
    text = replace_once(text, old_run, new_run, "BatchPlacement run")
    text = text.replace("theorem placedBatchProgram_run", "theorem placedBatchStraight_run", 1)
    text = text.replace(
        '''    compiledRun (placedBatchProgram w start) (readConstant coefficientAt Q) history =
      (placedBatchSource Q w).run := by''',
        '''    ((placedBatchStraight w start).instantiate (readConstant coefficientAt Q) history).run =
      (placedBatchSource Q w).run := by''',
        1,
    )
    count_begin = text.index("theorem placedBatchProgram_count")
    count_end = text.index("\n\nend ", count_begin)
    count_replacement = '''theorem placedBatchProgram_count (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).1 = 458738 := rfl'''
    text = text[:count_begin] + count_replacement + text[count_end:]
    write_pair(bench_root, "Challenge/BatchPlacement.lean", text)

    text = dirty_namespace((source_dir / "BatchCoherent.lean").read_text())
    text = map_imports(text, names)
    old = '''  | swap source target =>
    unfold batchStepCircuit batchOpCircuit
    unfold endpointTranspositionCircuit
    rw [Classical.hpFree_append, Classical.hpFree_append]
    exact ⟨⟨endpointTests_HPFree _ _ _ _ _,endpointWordCircuit_HPFree _ _⟩,
      endpointTests_HPFree _ _ _ _ _⟩
'''
    new = '''  | swap source target =>
    unfold batchStepCircuit batchOpCircuit
    exact ShorECDLP.Compact.dirtyEndpointTransposition_HPFree _ _ _ _
'''
    text = replace_once(text, old, new, "BatchCoherent HPFree")
    write_pair(bench_root, "Challenge/BatchCoherent.lean", text)

    for name in ("BatchPhysical", "BatchTemplate"):
        text = dirty_namespace((source_dir / f"{name}.lean").read_text())
        text = map_imports(text, names)
        old = '''      unfold batchOpCircuit
      exact endpointTransposition_wellFormed _ _ _ _ _ (batchSwap_geometry base source target h.1 h.2)
'''
        if name == "BatchPhysical":
            new = '''      unfold batchOpCircuit
      exact ShorECDLP.Compact.dirtyEndpointTransposition_wellFormed _ _ _ _
        (batchSwap_geometry base source target h.1 h.2)
'''
        else:
            # BatchTemplate uses the same proof with the local hypothesis named hop.
            old = old.replace("h.1 h.2", "hop.1 hop.2")
            new = '''      unfold batchOpCircuit
      exact ShorECDLP.Compact.dirtyEndpointTransposition_wellFormed _ _ _ _
        (batchSwap_geometry base source target hop.1 hop.2)
'''
        text = replace_once(text, old, new, f"{name} wellFormed")
        if name == "BatchTemplate":
            text = text.replace(
                '''theorem placedBatchProgram_wellFormed (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).2.WellFormed := by
  have hd''',
                '''theorem placedBatchStraight_wellFormed (w : OddWindow) (start : Nat) :
    (placedBatchStraight w start).WellFormed := by
  simp only [placedBatchStraight, castFinish_wellFormed,
    placedBatchProgramRaw]
  have hd''',
                1,
            )
        write_pair(bench_root, f"Challenge/{name}.lean", text)

    text = dirty_namespace((source_dir / "BatchCost.lean").read_text())
    text = map_imports(text, names)
    begin = text.index("theorem batchOpCircuit_tCount")
    end = text.index("theorem batchQuery_tCount", begin)
    replacement = '''theorem batchOpCircuit_tCount (base : Wire) (source : Fin 4) (target : Fin 6) :
    ShorECDLP.tCount (batchOpCircuit base source target) = 64414 := by
  unfold batchOpCircuit
  exact ShorECDLP.Compact.dirtyEndpointTransposition_tCount _ _ _ _

'''
    text = text[:begin] + replacement + text[end:]
    text = text.replace("35826 + batchCost", "64414 + batchCost")
    text = text.replace("98*nodes+573216", "98*nodes+1030624")
    text = text.replace("= 3784382", "= 4241790")
    write_pair(bench_root, "Challenge/BatchCost.lean", text)

    text = dirty_namespace((source_dir / "WindowBody.lean").read_text())
    text = map_imports(text, names)
    text = text.replace(
        "[sharedCoordinateProgram w, sharedYNegateProgram w, placedBatchProgram w, sharedYNegateProgram w]",
        "[sharedCoordinateProgram w, sharedYNegateProgram w, "
        "(fun cursor => ⟨458738, placedBatchStraight w cursor⟩), sharedYNegateProgram w]",
    )
    text = text.replace(
        "sequenceProgram 983040 (batchedWindowSegments w) start",
        "sequenceProgram 983040 (sharedCoordinateProgram w :: sharedYNegateProgram w :: "
        "(fun cursor => ⟨458738, placedBatchStraight w cursor⟩) :: "
        "sharedYNegateProgram w :: List.nil) start",
    )
    marker = "theorem batchedWindowCore_run"
    pos = text.index(marker)
    core_eq = '''theorem batchedWindowCore_eq :
    batchedWindowCore = fun w start => sequenceProgram 983040
      (sharedCoordinateProgram w :: sharedYNegateProgram w ::
        (fun cursor => ⟨458738, placedBatchStraight w cursor⟩) ::
        sharedYNegateProgram w :: List.nil) start := rfl

'''
    text = text[:pos] + core_eq + text[pos:]
    text = text.replace("placedBatchProgram_run", "placedBatchStraight_run")
    text = text.replace(
        "intro cursor h; exact placedBatchStraight_run w cursor Q h",
        "intro cursor h; simpa only [compiledRun] using placedBatchStraight_run w cursor Q h",
    )
    text = text.replace("List.range' 4102 512", "List.range' 4102 1")
    text = text.replace("batchedResetWires.length = 3931", "batchedResetWires.length = 3420")
    write_pair(bench_root, "Challenge/WindowBody.lean", text)


def ported_modules(bench_root: Path) -> None:
    original = bench_root / "ShorECDLP/Submission/Entrant/Streaming"
    protected_names = {
        "BatchedEndpoint", "BatchState", "BatchQuery", "BatchExecution",
        "BatchCoherent", "BatchFrame", "BatchPhysical", "BatchPlacement",
        "PlacedBatch", "BatchTemplate", "BatchCost", "WindowBody",
    }
    replacements = {
        "3784382": "4241790",
        "514030776": "514488184",
        "14393320473": "14406127897",
        "14393374641": "14406182065",
        "86360247846": "86437092390",
        "860607482": "860606971",
        "5163644892": "5163641826",
        "3932": "3421",
        "3931": "3420",
    }
    for path in sorted(original.rglob("*.lean")):
        if "/Dirty/" in path.as_posix():
            continue
        rel = path.relative_to(original).as_posix()
        text = path.read_text()
        text = dirty_namespace(text)
        text = map_imports(text, protected_names)
        text = text.replace("p.entryForStreaming coefficients", "OuterPlan.entryForStreaming coefficients p")
        text = text.replace("p.positionsForStreaming", "(OuterPlan.positionsForStreaming p)")
        text = text.replace("p.layoutForStreaming", "(OuterPlan.layoutForStreaming p)")
        text = text.replace("batchedOuterPlan.layoutForStreaming",
                            "(OuterPlan.layoutForStreaming batchedOuterPlan)")
        for old, new in replacements.items():
            text = text.replace(old, new)
        if rel == "Challenge/WindowPhysical.lean":
            text = f"import {DIRTY_STREAM}.Challenge.WindowBody\n" + text
        write_pair(bench_root, rel, text)

    # Support uses only the five words and flag; no clean-chain labels survive.
    path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty/Challenge/BatchSupport.lean"
    text = path.read_text()
    text = f"import {DIRTY_STREAM}.Challenge.WindowBody\n" + text
    begin = text.index("theorem batchOpCircuit_support")
    end = text.index("theorem batchOps_support", begin)
    replacement = r'''theorem batchOpCircuit_support (base : Wire) (source : Fin 4) (target : Fin 6) :
    circuitWires (batchOpCircuit base source target) ⊆ List.range' base 3079 := by
  unfold batchOpCircuit
  apply ShorECDLP.Compact.dirtyEndpointTransposition_support
  · intro i
    simp only [List.mem_range'_1, batchWord]
    have := i.isLt
    dsimp only [Wire] at *
    omega
  · intro i
    simp only [List.mem_range'_1, batchWord]
    have := i.isLt
    dsimp only [Wire] at *
    omega
  · intro i
    simp only [List.mem_range'_1, batchWord]
    have := i.isLt
    dsimp only [Wire] at *
    omega
  · simp only [List.mem_range'_1, batchFlag]
    dsimp only [Wire]
    omega

'''
    text = text[:begin] + replacement + text[end:]
    text = text.replace("3590", "3079")
    text = text.replace("(placedBatchProgram w start).2", "(placedBatchStraight w start)")
    text = text.replace(
        "placedBatchProgram,relabelCompiled_support",
        "placedBatchStraight,placedBatchProgramRaw,straightWires_castFinish,relabelCompiled_support",
    )
    text = text.replace(
        '''  simp only [placedBatchStraight,placedBatchProgramRaw,straightWires_castFinish,relabelCompiled_support,List.map_map]''',
        '''  unfold placedBatchStraight
  rw [straightWires_castFinish]
  simp only [placedBatchProgramRaw,relabelCompiled_support,List.map_map]''',
    )
    path.write_text(text)
    (LAB / "workspace/C_Challenge_BatchSupport.lean").write_text(text)

    # The dirty transposition has 17,410 gates (four 4,096-gate comparisons plus update).
    path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty/Challenge/LookupSlots.lean"
    text = path.read_text()
    begin = text.index("theorem batchOpCircuit_length_le")
    end = text.index("theorem endpointSelectGates_length_le", begin)
    replacement = '''theorem batchOpCircuit_length_le (base : Wire) (source : Fin 4) (target : Fin 6) :
    (batchOpCircuit base source target).length ≤ 17410 := by
  unfold batchOpCircuit
  rw [ShorECDLP.Compact.dirtyEndpointTransposition_length]

'''
    text = text[:begin] + replacement + text[end:]
    text = text.replace("13326", "17410")
    text = text.replace("≤ 1183793236", "≤ 1183858580")
    text = text.replace("(placedBatchProgram w start).2.gateSlots", "(placedBatchStraight w start).gateSlots")
    text = text.replace(
        "placedBatchProgram,relabelCompiled,relabelStraight_slots",
        "placedBatchStraight,placedBatchProgramRaw,castFinish_gateSlots,relabelCompiled,relabelStraight_slots",
    )
    text = text.replace(
        '''  simp only [placedBatchStraight,placedBatchProgramRaw,castFinish_gateSlots,relabelCompiled,relabelStraight_slots,batchedEndpointProgram,
    lookupProgram_slots]''',
        '''  unfold placedBatchStraight
  rw [castFinish_gateSlots]
  simp only [placedBatchProgramRaw,relabelCompiled,relabelStraight_slots,batchedEndpointProgram,
    lookupProgram_slots]''',
    )
    path.write_text(text)
    (LAB / "workspace/C_Challenge_LookupSlots.lean").write_text(text)

    path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty/Challenge/WindowSlots.lean"
    text = path.read_text()
    text = text.replace("1183793236", "1183858580")
    text = text.replace("2683845980", "2683911324")
    path.write_text(text)
    (LAB / "workspace/C_Challenge_WindowSlots.lean").write_text(text)

    # The larger reversible comparator proof needs more elaboration fuel only here.
    path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty/Challenge/ActualPhysical.lean"
    text = path.read_text()
    text = f"import {DIRTY_STREAM}.Challenge.WindowBody\n" + text
    text = text.replace(
        "attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram placedBatchProgram",
        "attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram",
        1,
    )
    begin = text.index("theorem batchedWindowCore_wellFormed")
    end = text.index("attribute [local irreducible] batchedWindowCore", begin)
    replacement = '''private theorem sequenceFour_wellFormed {n : Nat}
    (a b d : FixedSegment n)
    (c : (start : Nat) → Straight n start (start + 458738))
    (ha : ∀ start, (a start).2.WellFormed)
    (hb : ∀ start, (b start).2.WellFormed)
    (hc : ∀ start, (c start).WellFormed)
    (hd : ∀ start, (d start).2.WellFormed) (start : Nat) :
    (sequenceProgram n
      (a :: b :: (fun cursor => ⟨458738, c cursor⟩) :: d :: List.nil) start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ha cursor
  · exact hb cursor
  · simpa only using hc cursor
  · exact hd cursor

set_option maxRecDepth 10000 in
theorem batchedWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.WellFormed := by
  rw [batchedWindowCore_eq]
  exact sequenceFour_wellFormed (a := sharedCoordinateProgram w)
    (b := sharedYNegateProgram w) (c := placedBatchStraight w)
    (d := sharedYNegateProgram w) (sharedCoordinateProgram_wellFormed w)
    (sharedYNegateProgram_wellFormed w) (placedBatchStraight_wellFormed w)
    (sharedYNegateProgram_wellFormed w) start

'''
    text = text[:begin] + replacement + text[end:]
    path.write_text(text)
    (LAB / "workspace/C_Challenge_ActualPhysical.lean").write_text(text)

    path = bench_root / "ShorECDLP/Submission/Entrant/Streaming/Dirty/Challenge/WindowCounts.lean"
    text = path.read_text()
    text = text.replace(
        "compiledTCount (placedBatchProgram w start)",
        "compiledTCount ⟨458738, placedBatchStraight w start⟩",
    )
    text = text.replace(
        "placedBatchProgram,relabelCompiled,compiledTCount",
        "placedBatchStraight,placedBatchProgramRaw,relabelCompiled,compiledTCount,castFinish_instantiate",
    )
    text = text.replace(",placedBatchProgram_count]", "]")
    text = text.replace(
        '''  simp only [placedBatchStraight,placedBatchProgramRaw,relabelCompiled,compiledTCount,castFinish_instantiate,relabelStraight_instantiate,
    AdaptiveCircuit.relabel_tCount,batchedEndpointProgram,lookupProgram_tCount,batchOps_source,
    placedBatchSource]''',
        '''  simp only [compiledTCount]
  unfold placedBatchStraight
  rw [castFinish_instantiate]
  simp only [placedBatchProgramRaw,relabelCompiled,relabelStraight_instantiate,
    AdaptiveCircuit.relabel_tCount,batchedEndpointProgram,lookupProgram_tCount,batchOps_source,
    placedBatchSource]''',
    )
    path.write_text(text)
    (LAB / "workspace/C_Challenge_WindowCounts.lean").write_text(text)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bench", type=Path, required=True)
    args = parser.parse_args()
    expected = Path("/home/gitzard/shorecdlp-c")
    if args.bench.resolve() != expected:
        parser.error(f"Brief 11 permits only {expected}")
    dirty_mcx(args.bench)
    protected_modules(args.bench)
    ported_modules(args.bench)
    print("Staged dirty comparator modules in workspace/C_* and the separate bench.")


if __name__ == "__main__":
    main()
