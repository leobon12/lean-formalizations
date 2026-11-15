/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInResidualPairing
import InteractingSLE.Spec.Sec7.PocketSideInFaceGerm

/-!
# R.5 from the conditional old-chart increment law

PROVE-POCKET-SIDEIN. The remaining field input says that the transported
physical mean difference is the local-set mean of the actual increment
of the residual zero-boundary field. The actual geometry and harmonic
representation are derived. The law's regular global extension supplies
locality and the incident zero germ without asserting locality after
restriction to an event that can depend on the future.
This named conditional law does not replace a source theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- The conditional restart/local-set law still to be instantiated for
the actual old and current records. It records an exact distributional
identity. The global increment agrees with the geometric set on its event;
the event-restricted set itself need not be local. -/
def HasOldChartIncrementLaw {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : Set Ω) (old current : Ω → Chart)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ A : Ω → Set ℂ, ∃ hResidual gIncrement : Ω → DistOn upperHalfPlaneOpens,
    IsZeroBoundaryGFF upperHalfPlaneOpens hResidual P ∧
    Measurable[mΩ, hittingSigma] A ∧
    (∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
    IsLocalSetMean A hResidual P gIncrement ∧
    ∀ᵐ ω ∂P, ω ∈ M → A ω = oldChartAddedSet M old current ω ∧
      ∀ hc : (old ω).IsConformal, gIncrement ω = Chart.pullField hc (gNow ω - gOld ω)

/-- The named increment law supplies the zero physical mean germ on
every certified old incident collar, simultaneously in all representatives
and all real accesses. No increment-representation premise remains. -/
theorem ae_physical_germ_of_old_chart_increment_law {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {M : Set Ω} {old current : Ω → Chart}
    {gOld gNow : Ω → DistOn upperHalfPlaneOpens}
    (hOld : ∀ ω ∈ M, (old ω).IsConformal)
    (hCurrent : ∀ ω ∈ M, (current ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((current ω).dom : Set ℂ) ⊆ (old ω).dom)
    (hLaw : HasOldChartIncrementLaw P M old current gOld gNow) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ vOld vNow : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vOld (old ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old ω).dom →
        gOld ω φ = ∫ z, vOld z * φ z) →
      InnerProductSpace.HarmonicOnNhd vNow (current ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (current ω).dom →
        gNow ω φ = ∫ z, vNow z * φ z) → ∀ (ξ x r : ℝ),
      0 < r → (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (current ω).dom →
      Tendsto (fun z => (old ω).1 ((current ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => vNow ((current ω).2.1 z) - vOld ((current ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨A, hResidual, gIncrement, hZero, hMeas, hRegular, hMean, hIdentity⟩ := hLaw
  have hGermLaw : IsGermConditionalLaw A hResidual P :=
    ⟨gIncrement, hMean⟩
  have hLocal : IsLocalSet A hResidual P :=
    ((isLocalSet_tfae hZero hMeas hRegular).out 3 4).1 hGermLaw
  filter_upwards [ae_incident_zero_germ_of_local_increment hZero hMeas hLocal hMean, hIdentity]
    with ω hZeroGerm hIdentity hω vOld vNow hvOld hRepOld hvNow hRepNow ξ x r hr hCollar hTransition
  obtain ⟨hSet, hField⟩ := hIdentity hω
  have hRep := pull_mean_difference_representation (hOld ω hω) (hInclusion ω hω)
    hvOld hRepOld hvNow hRepNow
  have hHarmonic : InnerProductSpace.HarmonicOnNhd
      (fun z => vNow ((old ω).2.1 z) - vOld ((old ω).2.1 z))
      (H \ A ω) := by
    simpa only [hSet, compl_oldChartAddedSet hω] using hRep.1
  have hRepresentation (φ : TestOn upperHalfPlaneOpens)
      (hφ : tsupport φ ⊆ H \ A ω) :
      gIncrement ω φ = ∫ z, (vNow ((old ω).2.1 z) - vOld ((old ω).2.1 z)) * φ z := by
    rw [hField (hOld ω hω)]
    exact hRep.2 φ (by rwa [hSet, compl_oldChartAddedSet hω] at hφ)
  have hWithin : Tendsto (fun z => (old ω).1 ((current ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hTransition,
      eventually_nhdsWithin_of_forall fun z hz =>
        (hOld ω hω).fwd_mem (hInclusion ω hω ((hCurrent ω hω).inv_mem_dom hz))⟩
  have hAvoid : Disjoint (H ∩ ball (x : ℂ) r) (A ω) := by
    rw [hSet]
    exact oldChartAddedSet_disjoint_of_inverse_collar hω hCollar
  have hGerm := hZeroGerm _ hHarmonic hRepresentation ξ x _ hWithin ⟨r, hr, hAvoid⟩
  refine hGerm.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [(hOld ω hω).inv_fwd (hInclusion ω hω ((hCurrent ω hω).inv_mem_dom hz))]

end InteractingSLE.Sec7.PocketStopSide
