/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice16Recorded

/-! # Construct the actual initial comparison unions

The clamped reference hulls are recorded by the existing initial marks
and are contained in the current marked set almost surely. Their actual
unions with that set are therefore recorded, marked local, and equal to
the current set almost surely. No larger-union input is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ULoc Aux61Marks
open LawUnique GlueCond LocalSets WholeField
universe u

/-- The actual larger comparison union for a retained reference. -/
def pastReferenceUnion (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
    (i : F.ι) (q : ℚ) (j : SourceReferenceIndex) (p : S.Ω × HistorySpace 0 0) : Set ℂ :=
  (S.marksData F).baseSets i 0 p ∪ sourceReferenceSet S (pastReferenceIndex q j) p

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
  (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
  (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
    ((S.marksData F).baseSets i 0))
include hR hq hsets

/-- The larger union is recorded by the same initial marked sigma-algebra. -/
theorem past_union_recorded (j : SourceReferenceIndex) :
    Measurable[(S.marksData F).baseMarks i 0, hittingSigma] (pastReferenceUnion S F i q j) :=
  @measurable_union_hitting _ ((S.marksData F).baseMarks i 0) _ _ hsets
    (past_reference_recorded S F hR.chart_measurable i q hq j)

variable (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
  (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
    (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
include hretained

/-- Actual union locality follows from the coupling's initial locality
and its recorded enlargement. No union-locality premise remains. -/
theorem past_union_local (j : SourceReferenceIndex) :
    IsHistoryAvoidanceLocal ((S.marksData F).baseMarks i 0)
      (pastReferenceUnion S F i q j) (S.marksData F).cfield S.μ := by
  have hloc := source_initial_locality S F hR i hsets
    (source_initial_contains S F hR i hretained)
  exact Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hloc
    (past_union_recorded S F hR i q hq hsets j) (ae_of_all _ fun _ => subset_union_left)

omit hsets in
/-- The actual comparison union agrees almost surely with the current
marked set; its reference is genuinely a retained physical subset. -/
theorem past_union_eq (j : SourceReferenceIndex) : ∀ᵐ p ∂S.μ,
    pastReferenceUnion S F i q j p = (S.marksData F).baseSets i 0 p := by
  filter_upwards [past_reference_subset S F hR i q hq hretained j] with p hp
  exact union_eq_left.2 hp

omit hq hsets hretained in
/-- Relative closedness and containment in H hold at every sample, including
the totalized marked sets away from the live event. -/
theorem past_union_closed (j : SourceReferenceIndex) (p : S.Ω × HistorySpace 0 0) :
    pastReferenceUnion S F i q j p ⊆ H ∧ IsOpen (H \ pastReferenceUnion S F i q j p) := by
  have hA := sourceSets_closed F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    S.κ S.ownField hR.spec i 0 p
  have hB := sourceReferenceSet_closed S (pastReferenceIndex q j) p
  refine ⟨union_subset hA.1 hB.1, ?_⟩
  change IsOpen (H \ ((S.marksData F).baseSets i 0 p ∪
    sourceReferenceSet S (pastReferenceIndex q j) p))
  rw [← sdiff_inter_sdiff]
  exact hA.2.inter hB.2

end InteractingSLE.Sec5.Aux61GChoice16
