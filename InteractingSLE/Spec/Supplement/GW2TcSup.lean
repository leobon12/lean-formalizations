/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TbSets

/-!
# A set whose avoidance events are marks and which contains a marked local set is marked local

Packet PROVE-GW2-RELDET, ruling R113 (`GW2TbHull.SchedCurveLocalStatement`). The explored trace of the schedule up to
a physical time is the physical explored curve, plus, after the candidate's death or the program end, a frozen
continuation determined by the explored path. An exact identification at every time is not needed. It is enough that
the physical curve (marked local by round 10's tools) lies in the trace, and that the trace's avoidance events are
marks:

* **`isHistoryAvoidanceLocal_of_superset_marks`**: if `S` is marked local for field-determined marks `ℋ` with marks as
  avoidance events, `T`'s avoidance events are marks, and almost surely `S ∩ ℍ ⊆ T`, then `T` is marked local for `ℋ`;
* **`schedCurveLocal_of_phys`** (conditional helper): the conclusion of `SchedCurveLocalStatement` at one `q` from such
  marks `𝓜`, a physical curve `S` that is `𝓜`-marked local and lies in the trace on `oldSuccess`, and the trace's
  avoidance events being marks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

section Sup

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A superset of a marked local set with marks as avoidance events is marked local.** -/
theorem isHistoryAvoidanceLocal_of_superset_marks (hhm : Measurable h) {S T : Ω → Set ℂ}
    (hloc : IsHistoryAvoidanceLocal ℋ S h P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω) U})
    (hTm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (T ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) (hST : ∀ᵐ ω ∂P, S ω ∩ H ⊆ T ω) :
    IsHistoryAvoidanceLocal ℋ T h P := by
  have hU := (isHistoryAvoidanceLocal_union_marks hhm hloc hSm hTm hℋd).2
  refine WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_
  have h1 := WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hU hUH hG hd hF
    (hℋd _ (((hSm U hUH).inter (hTm U hUH)).inter hF |>.congr (by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left])))
  refine aeSigma_of_ae_eq h1 ?_
  filter_upwards [hST] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left]
  apply propext
  constructor
  · rintro ⟨hT, hωF⟩
    refine ⟨⟨?_, hT⟩, hωF⟩
    rw [disjoint_left]
    intro z hzS hzU
    exact disjoint_left.1 hT (hω ⟨hzS, hUH hzU⟩) hzU
  · rintro ⟨⟨-, hT⟩, hωF⟩
    exact ⟨hT, hωF⟩

end Sup

section Sched

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The explored curve set is marked local from a physical curve inside it** (conditional helper for
`SchedCurveLocalStatement` at one time `q`): marks `𝓜` containing the null sets and the history records, an
`𝓜`-marked local set `S` lying in the explored trace on `oldSuccess`, and the trace's avoidance events being marks. -/
theorem schedCurveLocal_of_phys {u₀ : ℂ → ℝ} (q : ℝ≥0)
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hrec : ∀ j : Fin ((entryList l).length + 1),
      @Measurable Ω Exist.StagedLaw.RecData 𝓜.1 _ (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j))
    (hd : 𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P)
    {S : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal 𝓜.1 S (centredField c.h u₀) c.P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (S ω) U})
    (hTm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω ∧ Disjoint (schedTr c r l a ω '' Icc 0 q) U})
    (hST : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → S ω ∩ H ⊆ schedTr c r l a ω '' Icc 0 q) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveL c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedCurveL c r l a q) (centredField c.h u₀) c.P := by
  classical
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  -- the curve on `oldSuccess`, `ℍ` off it, has its avoidance events in the marks
  have hev0 : ∀ U : Opens ℂ, (U : Set ℂ) = ∅ → ∀ X : Ω → Set ℂ, {ω | Disjoint (X ω) U} = univ := by
    intro U hU X
    ext ω
    simp only [hU, mem_ofPred_eq, disjoint_empty, mem_univ]
  have hCm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveL c r l a q ω) U} := by
    intro U hUH
    by_cases hU : (U : Set ℂ) = ∅
    · rw [hev0 U hU]
      exact MeasurableSet.univ
    · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
      have e : {ω | Disjoint (schedCurveL c r l a q ω) U} =
          {ω | oldSuccess c r l ω ∧ Disjoint (schedTr c r l a ω '' Icc 0 q) U} := by
        ext ω
        by_cases hω : oldSuccess c r l ω
        · simp only [schedCurveL, hω, ↓reduceIte, mem_ofPred_eq, true_and]
        · simp only [schedCurveL, hω, ↓reduceIte, mem_ofPred_eq, false_and, iff_false]
          exact fun hd' => disjoint_left.1 hd' (hUH hz) hz
      rw [e]
      exact hTm U hUH
  refine ⟨hCm, isHistoryAvoidanceLocal_of_superset_marks (measurable_centredField c.hh.1 u₀)
    (S := fun ω => if ω ∈ {ω | oldSuccess c r l ω} then S ω else H) ?_ ?_ hCm hd ?_⟩
  · -- `S` on `oldSuccess`, `ℍ` off it
    exact (isHistoryAvoidanceLocal_ite_H (measurable_centredField c.hh.1 u₀) hloc hSm hd hE).2
  · exact (isHistoryAvoidanceLocal_ite_H (measurable_centredField c.hh.1 u₀) hloc hSm hd hE).1
  · filter_upwards [hST] with ω hω
    by_cases hωE : oldSuccess c r l ω
    · have h1 : (if oldSuccess c r l ω then S ω else H) = S ω := by simp only [hωE, ↓reduceIte]
      have h2 : schedCurveL c r l a q ω = schedTr c r l a ω '' Icc 0 q := by
        simp only [schedCurveL, hωE, ↓reduceIte]
      rw [h1, h2]
      exact hω hωE
    · have h1 : (if oldSuccess c r l ω then S ω else H) = H := by simp only [hωE, ↓reduceIte]
      have h2 : schedCurveL c r l a q ω = H := by simp only [schedCurveL, hωE, ↓reduceIte]
      rw [h1, h2]
      exact inter_subset_left

end Sched

end InteractingSLE.Theorem14.GW2Rd
