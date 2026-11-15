/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice16Unions
import InteractingSLE.Spec.Sec5.Aux61GAlignCompare

/-! # Initial source comparisons with all marked unions constructed

The actual smaller means come from the source couplings. Retained
reference times make their larger unions local for the existing initial
marks. The only comparison argument left here is the physical boundary
access and reference-height germ cover, not an entire comparison record.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ULoc Aux61Marks
open LawUnique GlueCond LocalSets WholeField
universe u

/-- Construct every mean and marked-union field of the exact current
comparison type from the actual source coupling and retained references. -/
theorem source_comparisons_of_past_germs
    (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (hgerms : ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀,
      ∃ (j : SourceReferenceIndex) (z₀ : ℂ),
        z₀ ∈ sourceReferenceSet S (pastReferenceIndex q j) x ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, (S.marksData F).baseSets i 0 x ∩ ball z₀ r ⊆
          sourceReferenceSet S (pastReferenceIndex q j) x) ∧
        Tendsto ((S.marksData F).chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q j) x
          (((S.marksData F).chart i x).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i x).2.2
            (((S.marksData F).chart i x).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0)) :
    Nonempty (Aux61GAlign.ZeroComparisons (S.marksData F) i) := by
  obtain ⟨g, hg, hh, hp⟩ := exists_source_reference_family S F i
  exact ⟨{
    index := SourceReferenceIndex
    countable := inferInstance
    patch := fun j => sourceReferenceSet S (pastReferenceIndex q j)
    patchMean := fun j => g (pastReferenceIndex q j)
    physicalMean := fun j => sourceReferenceMean S (pastReferenceIndex q j)
    union := pastReferenceUnion S F i q
    unionMarks := fun _ => (S.marksData F).baseMarks i 0
    event := fun _ => univ
    patch_measurable := fun j => measurable_sourceReferenceSet S (pastReferenceIndex q j)
    patch_closed := fun j => ae_of_all _ (sourceReferenceSet_closed S (pastReferenceIndex q j))
    patch_unbounded := fun j => ae_of_all _ (sourceReferenceSet_unbounded S (pastReferenceIndex q j))
    patch_mean := fun j => hg (pastReferenceIndex q j)
    physical_harmonic := fun j => hh (pastReferenceIndex q j)
    represents := fun j => hp (pastReferenceIndex q j)
    union_marks_le := fun _ => nullMarks_le
    union_measurable := fun j => past_union_recorded S F hR i q hq hsets j
    union_closed := fun j => past_union_closed S F hR i q j
    union_local := fun j => past_union_local S F hR i q hq hsets hretained j
    marks_le := fun _ => le_rfl
    set_recorded := fun _ => hsets
    set_subset := fun _ _ => inter_subset_left.trans subset_union_left
    patch_recorded := fun j => past_reference_recorded S F hR.chart_measurable i q hq j
    patch_subset := fun _ _ => inter_subset_left.trans subset_union_right
    event_measurable := fun _ => MeasurableSet.univ
    union_eq := fun j => by
      filter_upwards [past_union_eq S F hR i q hq hretained j] with x hx _
      exact hx
    cover := by
      filter_upwards [hgerms] with x hx he b hb
      obtain ⟨j, z, hz, hr, hl, hm⟩ := hx he b hb
      exact ⟨j, z, mem_univ _, hz, hr, hl, hm⟩ }⟩

end InteractingSLE.Sec5.Aux61GChoice16
