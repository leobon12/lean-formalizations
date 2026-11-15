/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Facts

/-!
# A successful test really extends the physical retained history

Packet PROVE-T14-GW2ROOT2. This is an all-outcome result: the old
death flags and the next piece's available own time are supplied by the
actual test gate. Cutoff-independence compares the candidate program
with the DIFFERENT program retaining the successful query.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The source buffer is bounded by the next actual canonical lifetime,
not merely by the lifetime of the artificial concatenated record. -/
theorem sourceBuffer_coe_le_next_lifetime (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (sourceBuffer c r l a ω : ℝ≥0∞) ≤
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (futureProgram c r l a)) (historyProgram c r l).length ω).2 := by
  have hn : (nextRecord c r l a ω).2.1 ≠ ⊤ :=
    ne_top_of_le_ne_top (specDelta_ne_top _ _) (min_le_left _ _)
  calc
    (sourceBuffer c r l a ω : ℝ≥0∞) ≤
        ((nextRecord c r l a ω).2.1.toNNReal : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr (sourceBuffer_le_next_time c r l a ω)
    _ = (nextRecord c r l a ω).2.1 := ENNReal.coe_toNNReal hn
    _ ≤ _ := min_le_right _ _

theorem historyProgram_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (θ : c.Θ) (q : c.Q) :
    historyProgram c r ((θ, q) :: l) =
      historyProgram c r l ++ [((θ : ℝ), (q : ℝ≥0))] := by
  simp only [historyProgram, entryList_cons, schedOf_cons]

variable [StandardBorelSpace Ω]

/-- On a successful query, the next piece is alive in the query's own
canonical program. No source regularity or probability assertion is used. -/
theorem next_piece_live_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    let spec := schedSpec (rootPt r.1)
      (historyProgram c r l ++ [((candidateAngle c r a : ℝ), (q : ℝ≥0))])
    specDelta spec (historyProgram c r l).length <
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec (historyProgram c r l).length ω).2 := by
  have hTq : historyTime c r l < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((sourceEntry_ge_historyTime c r l a ω).trans_lt ht.1)
  have hqF : ((q : ℝ≥0) : ℝ) <
      (historyTime c r l : ℝ) + sourceBuffer c r l a ω := by
    simpa only [experiment, experimentData, sourceFailure, NNReal.coe_add] using ht.2.1
  have hδ : (q : ℝ≥0) - historyTime c r l < sourceBuffer c r l a ω := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_sub hTq.le]
    linarith
  have hlt := (ENNReal.coe_lt_coe.mpr hδ).trans_le
    (sourceBuffer_coe_le_next_lifetime c r l a ω)
  have he := RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h
    (rootPt r.1) (candidateAngle c r a) (historyProgram c r l)
    (historyTime c r l + candidateCap c r a) q ω
  change _ < (canonSpecFam _ _ _ _ _
    (schedSpec (rootPt r.1) (historyProgram c r l ++
      [((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a)]))
        (historyProgram c r l).length ω).2 at hlt
  rw [he] at hlt
  simpa only [RootH29.specDelta_last, historyTime] using hlt

/-- Every passed test extends the literal successful physical prefix,
including every old flag and the new query's flag. -/
theorem oldSuccess_cons_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    oldSuccess c r ((candidateAngle c r a, q) :: l) ω := by
  have hold := oldSuccess_of_test c r l a q ω ht
  have hnext := next_piece_live_of_test c r l a q ω ht
  rintro ⟨j, hj'⟩
  have hj : j < (historyProgram c r l).length + 1 := by
    simpa only [historyProgram_cons, List.length_append, List.length_singleton] using hj'
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (historyProgram c r ((candidateAngle c r a, q) :: l))) j ω).2.2 = false
  rw [historyProgram_cons]
  by_cases hjold : j < (historyProgram c r l).length
  · rw [stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hjold ω]
    exact hold ⟨j, hjold⟩
  · have hje : j = (historyProgram c r l).length := by omega
    rw [hje]
    exact (RootCv.recOf_flag_eq_false_iff _ _).mpr hnext

omit [StandardBorelSpace Ω] in
/-- COVER's initial retained piece already has its literal success flag. -/
theorem oldSuccess_nil_of_cover (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (ω : Ω) (hcov : ω ∈ RootCv.coverEvent c r) : oldSuccess c r [] ω := by
  rintro ⟨j, hj'⟩
  have hj : j = 0 := by
    simp only [historyProgram, entryList, List.map_nil, schedOf, List.reverse_nil,
      List.length_singleton] at hj'
    omega
  subst j
  exact hcov.2.1

/-- Every actual alive history is a successful physical history, everywhere.
This conclusion does not assume any of the open C24 geometry fields. -/
theorem oldSuccess_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive (RootCv.coverEvent c r) l) :
    oldSuccess c r l ω := by
  cases l with
  | nil => exact oldSuccess_nil_of_cover c r ω ha
  | cons x l =>
    obtain ⟨_, htest⟩ := ha
    obtain ⟨a, htest⟩ := mem_iUnion.mp htest
    obtain ⟨hang, ht⟩ := mem_iUnion.mp htest
    have he : (candidateAngle c r a, x.2) = x := Prod.ext hang rfl
    rw [← he]
    exact oldSuccess_cons_of_test c r l a x.2 ω ht

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
