/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActCollar
import InteractingSLE.Spec.Sec7.Lemma78MeanReal

/-!
# R.5: boundary germs from the old-chart local increment law

PROVE-POCKET-SIDEIN. In the old conditional chart, the added set is a local
set of the residual zero-boundary GFF. Its local-set mean decays on an
untouched real half-disc. The exact conditional increment law and its
physical-chart representation remain named inputs; the germ limit is proved.
No equality of complete conditional means and no independence of nested
pockets is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- An incident chart approach through a trace-free old upper half-disc
approaches through the complement of the actual added set. -/
theorem tendsto_compl_of_incident_halfDisc {A : Set ℂ} {ξ u : ℝ} {F : ℂ → ℂ}
    (hF : Tendsto F (𝓝[H] (ξ : ℂ)) (𝓝[H] (u : ℂ)))
    {r : ℝ} (hr : 0 < r) (hfree : Disjoint (H ∩ ball (u : ℂ) r) A) :
    Tendsto F (𝓝[H] (ξ : ℂ)) (𝓝[H \ A] (u : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hF.mono_right nhdsWithin_le_nhds, ?_⟩
  filter_upwards [hF.eventually self_mem_nhdsWithin,
    (hF.mono_right nhdsWithin_le_nhds).eventually (ball_mem_nhds (u : ℂ) hr)]
    with z hzH hzball
  exact ⟨hzH, fun hzA => disjoint_left.1 hfree ⟨hzH, hzball⟩ hzA⟩

/-- Ordinary local-set boundary decay proves R.5's zero increment germ along
every surviving incident approach in the old chart, on one event. -/
theorem ae_incident_zero_germ_of_local_increment {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    {A : Ω → Set ℂ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, v z * φ z) → ∀ (ξ u : ℝ) (F : ℂ → ℂ),
      Tendsto F (𝓝[H] (ξ : ℂ)) (𝓝[H] (u : ℂ)) →
      (∃ r > 0, Disjoint (H ∩ ball (u : ℂ) r) (A ω)) →
      Tendsto (fun z => v (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  filter_upwards [IsLocalSetMean.ae_tendsto_zero_of_real hh hAm hAloc hg,
    hAloc.2.1] with ω hdecay ⟨hAH, _⟩ v hv hrep ξ u F hF hfree
  obtain ⟨r, hr, hfree⟩ := hfree
  have hball : Disjoint (ball (u : ℂ) r) (A ω) := disjoint_left.2 fun z hz hzA =>
    disjoint_left.1 hfree ⟨hAH hzA, hz⟩ hzA
  exact (hdecay v hv hrep u ⟨r, hr, hball⟩).comp
    (tendsto_compl_of_incident_halfDisc hF hr hfree)

/-- Exact R.5 source input: the conditional increment mean represents the
difference of the two physical means in the old chart. The boundary germ
comparison is a conclusion, not an additional premise. -/
theorem ae_old_germ_preserved_of_local_increment {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    {A : Ω → Set ℂ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A h P)
    (hIncrementMean : IsLocalSetMean A h P g)
    {vNow vOld : Ω → ℂ → ℝ} {invOld : Ω → ℂ → ℂ}
    (hIncrementRepresentation : ∀ᵐ ω ∂P,
      InnerProductSpace.HarmonicOnNhd
        (fun z => vNow ω (invOld ω z) - vOld ω (invOld ω z)) (H \ A ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, (vNow ω (invOld ω z) - vOld ω (invOld ω z)) * φ z) :
    ∀ᵐ ω ∂P, ∀ (ξ u : ℝ) (F : ℂ → ℂ),
      Tendsto F (𝓝[H] (ξ : ℂ)) (𝓝[H] (u : ℂ)) →
      (∃ r > 0, Disjoint (H ∩ ball (u : ℂ) r) (A ω)) →
      Tendsto (fun z => vNow ω (invOld ω (F z)) - vOld ω (invOld ω (F z)))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  filter_upwards [ae_incident_zero_germ_of_local_increment hh hAm hAloc hIncrementMean,
    hIncrementRepresentation] with ω hzero hrep ξ u F hF hfree
  exact hzero _ hrep.1 hrep.2 ξ u F hF hfree

end InteractingSLE.Sec7.PocketStopSide
