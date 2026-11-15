/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignReferences

/-! # A fixed countable family of actual physical boundary references -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting LawUnique GlueCond Cond44Ref WangWu LocalSets
universe u

/-- All rational own prefixes and the retained counterflow hull. -/
abbrev SourceReferenceIndex := ℚ ⊕ Unit

/-- The actual smaller sets used for the two boundary branches. -/
def sourceReferenceSet (S : SourceSetting.{u}) :
    SourceReferenceIndex → S.Ω × HistorySpace 0 0 → Set ℂ
  | .inl j, p => hullAt (rationalTime j) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)
  | .inr _, p => cfHullQ (rationalTime S.s) p.2

/-- The corresponding known physical means, before chart transport. -/
def sourceReferenceMean (S : SourceSetting.{u}) :
    SourceReferenceIndex → S.Ω × HistorySpace 0 0 → ℂ → ℝ
  | .inl j, p => couplingMean S.κ (fun t : ℝ => S.own.W t.toNNReal p.1)
      (rationalTime j) (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR j p.1)
  | .inr _, p => fun z =>
      cfMeanQ S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
        (sourceCounterExtension S) (rationalTime S.s) p.2 z +
      Impl.forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR z

/-- All actual smaller sets are hitting measurable on the source space. -/
theorem measurable_sourceReferenceSet (S : SourceSetting.{u}) (j : SourceReferenceIndex) :
    Measurable[_, hittingSigma] (sourceReferenceSet S j) := by
  cases j with
  | inl q =>
      exact (measurable_hullAt (rationalTime q)).comp
        ((measurable_killedHistory S.own.coupling.2.2.2.1).comp measurable_fst)
  | inr j => exact (measurable_cfHullQ (rationalTime S.s)).comp measurable_snd

/-- Relative closedness holds at every sample, including regularized ones. -/
theorem sourceReferenceSet_closed (S : SourceSetting.{u}) (j : SourceReferenceIndex)
    (p : S.Ω × HistorySpace 0 0) :
    sourceReferenceSet S j p ⊆ H ∧ IsOpen (H \ sourceReferenceSet S j p) := by
  cases j with
  | inl q => exact hullAt_relClosed _ _
  | inr j => exact cfHullQ_relClosed _ _

/-- Both kinds of smaller sets satisfy the unbounded-component hypothesis
of the reused boundary comparison theorem. -/
theorem sourceReferenceSet_unbounded (S : SourceSetting.{u}) (j : SourceReferenceIndex)
    (p : S.Ω × HistorySpace 0 0) :
    ∀ z ∈ lowerUnion (sourceReferenceSet S j p),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (sourceReferenceSet S j p)) z) := by
  cases j with
  | inl q => exact not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)
  | inr j => exact not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)

/-- The entire fixed countable family has actual local means with the
harmonicity and physical pairing fields needed by `ZeroComparisons`.
Those fields are consequences of the source coupling. -/
theorem exists_source_reference_family (S : SourceSetting.{u})
    (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι) :
    ∃ g₂ : SourceReferenceIndex → S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      (∀ j, IsLocalSetMean (sourceReferenceSet S j) (S.marksData F).cfield S.μ (g₂ j)) ∧
      (∀ j, ∀ᵐ p ∂S.μ, InnerProductSpace.HarmonicOnNhd
        (sourceReferenceMean S j p) (H \ sourceReferenceSet S j p)) ∧
      (∀ j, ∀ᵐ p ∂S.μ, ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ sourceReferenceSet S j p →
        g₂ j p φ = ∫ z, (sourceReferenceMean S j p z - (S.marksData F).originalMean z) * φ z) := by
  choose gA gG hA hG hpA hpG using exists_source_physical_references S F i
  let g₂ : SourceReferenceIndex → S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens :=
    Sum.elim gA (fun _ => gG 0)
  refine ⟨g₂, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl q => exact hA q
    | inr j => exact hG 0
  · intro j
    cases j with
    | inl q => exact (hpA q).mono fun _ hp => hp.1
    | inr j => exact (hpG 0).mono fun _ hp => hp.1
  · intro j
    cases j with
    | inl q => exact (hpA q).mono fun _ hp => hp.2
    | inr j => exact (hpG 0).mono fun _ hp => hp.2

end InteractingSLE.Sec5.Aux61GAlign
