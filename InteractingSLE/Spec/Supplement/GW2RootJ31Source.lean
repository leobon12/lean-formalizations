/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Program
import InteractingSLE.Spec.Supplement.GW2RootJ31Buffer
import InteractingSLE.Spec.Supplement.GW2CvCover

/-!
# Finite future buffers in the actual canonical physical programs

Packet PROVE-T14-GW2ROOT2. Old death flags are retained information.
The next record retains its own lifetime flag; its recorded lifetime,
rather than the time of the artificial joined record, caps the future
buffer. Thus a dead old piece cannot create a fresh positive-time sample.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Every prescribed old ordinary piece survived its retained own-time cutoff. -/
def oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : Prop :=
  ∀ j : Fin (historyProgram c r l).length,
    (stopRec c.hκ c.h12p c.βA c.c₀ c.h
      (schedSpec (rootPt r.1) (historyProgram c r l)) j ω).2.2 = false

/-- The actual next piece's retained record, with its own death flag. -/
def nextRecord (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Ω → RecData :=
  stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (futureProgram c r l a)) (historyProgram c r l).length

theorem measurableSet_oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : MeasurableSet {ω | oldSuccess c r l ω} := by
  have hm : ∀ j : Fin (historyProgram c r l).length, MeasurableSet
      {ω | (stopRec c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (historyProgram c r l)) j ω).2.2 = false} :=
    fun j => ((measurable_snd.comp measurable_snd).comp
      (measurable_stopRec c.hβA.1 c.hh.1 _ j)) (measurableSet_singleton false)
  simpa only [oldSuccess, ofPred_forall] using MeasurableSet.iInter hm

theorem measurable_nextRecord (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (nextRecord c r l a) :=
  measurable_stopRec c.hβA.1 c.hh.1 _ _

/-- The explicit physical failure time of a future switched experiment. -/
def sourceBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : ℝ≥0 :=
  open scoped Classical in
  if ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω then
    min (nextRecord c r l a ω).2.1.toNNReal
      (switchedBuffer (rootPt r.1) c.s (historyTime c r l + candidateCap c r a)
        (historyTime c r l) (candidateCap c r a) (candidateBuffer a)
        (futurePair c r l a ω)) else 0

theorem measurable_sourceBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceBuffer c r l a) := by
  classical
  have hc : MeasurableSet (RootCv.coverEvent c r) :=
    stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _ _ (RootCv.measurableSet_coverEvent c r)
  exact Measurable.ite (hc.inter (measurableSet_oldSuccess c r l))
    (((measurable_fst.comp (measurable_snd.comp
      (measurable_nextRecord c r l a))).ennreal_toNNReal).min
        ((measurable_switchedBuffer _ _ _ _ _ _).comp (measurable_futurePair c r l a)))
    measurable_const

theorem sourceBuffer_le (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceBuffer c r l a ω ≤ candidateCap c r a := by
  classical
  unfold sourceBuffer
  split_ifs
  · exact (min_le_right _ _).trans (switchedBuffer_le _ _ _ _ _ _ _)
  · exact zero_le

theorem sourceBuffer_eq_zero_of_old_death (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (hfail : ¬oldSuccess c r l ω) :
    sourceBuffer c r l a ω = 0 := ite_eq_right (fun h => hfail h.2)

/-- Outside the protected root event the whole future experiment is killed. -/
theorem sourceBuffer_eq_zero_of_not_cover (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (hf : ω ∉ RootCv.coverEvent c r) :
    sourceBuffer c r l a ω = 0 := ite_eq_right (fun h => hf h.1)

theorem sourceBuffer_le_next_time (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceBuffer c r l a ω ≤ (nextRecord c r l a ω).2.1.toNNReal := by
  classical
  unfold sourceBuffer
  split_ifs
  · exact min_le_left _ _
  · exact zero_le

/-- This is an actual positivity result for the explicit formula. Its source
instantiation at a switched history still requires the stated physical separation. -/
theorem sourceBuffer_pos (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hcov : ω ∈ RootCv.coverEvent c r) (hold : oldSuccess c r l ω)
    (hlife : 0 < (nextRecord c r l a ω).2.1.toNNReal)
    (hsep : 0 < separationRead (rootPt r.1) c.s
      (historyTime c r l + candidateCap c r a) (historyTime c r l) (futurePair c r l a ω)) :
    0 < sourceBuffer c r l a ω := by
  rw [sourceBuffer, ite_eq_left ⟨hcov, hold⟩]
  exact lt_min hlife (switchedBuffer_pos _ _ _ _ _ _ _ (candidateCap_pos c r a) hsep)

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
