/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MeanIdNested
import InteractingSLE.Spec.Sec5.Aux61GInstCorrection

/-! # Marked nested boundary cancellation in the restart coordinate -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec5.Aux61GInst
open LocalSets

/-- Proposition 3.8 cancels the old mean on every boundary patch of the
restart chart, including a seed patch separated from the other retained set.
The physical sets need not have simple boundaries. -/
theorem ae_relative_boundary_chart {Ω : Type*} {𝒥 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥)
    (h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤ 𝒥)
    {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₀m : Measurable[𝒥] g₀)
    (hg₀h : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ (A₁ ω ∪ A₂ ω)))
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ (A₁ ω ∪ A₂ ω)) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂)
    (F : Ω → ℂ → ℂ) (p : Ω → ℝ → ℂ) (O : Ω → Set ℝ)
    (hF : ∀ᵐ ω ∂P, MapsTo (F ω) H (H \ (A₁ ω ∪ A₂ ω)))
    (hFlim : ∀ᵐ ω ∂P, ∀ a ∈ O ω, Tendsto (F ω) (𝓝[H] (a : ℂ)) (𝓝 (p ω a)))
    (hpatch : ∀ᵐ ω ∂P, ∀ a ∈ O ω,
      p ω a ∈ A₂ ω ∪ {z : ℂ | z.im = 0} ∧
        ∃ r > 0, A₁ ω ∩ ball (p ω a) r ⊆ A₂ ω) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g₀ ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ a ∈ O ω, Tendsto (u ∘ F ω) (𝓝[H] (a : ℂ)) (𝓝 0) := by
  have hr := Aux61MeanId.ae_tendsto_sub_of_condLaw hh hA₁ hA₂ hA₁c hA₂c hunb
    h𝒥 h₂𝒥 h₁₂𝒥 hg₀m hg₀h hg₀c hg₂
  filter_upwards [hr, hF, hFlim, hpatch] with ω hω hFω hlim hpat
  obtain ⟨u, huh, hur, hub⟩ := hω
  refine ⟨u, huh, hur, fun a ha => ?_⟩
  apply (hub (p ω a) (hpat a ha).1 (hpat a ha).2).comp
  refine tendsto_nhdsWithin_iff.2 ⟨hlim a ha, ?_⟩
  have hev : ∀ᶠ z : ℂ in 𝓝[H] (a : ℂ), z ∈ H := self_mem_nhdsWithin
  exact hev.mono fun z hz => hFω hz

end InteractingSLE.Sec5.Aux61GInst
