/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewGermMean
import InteractingSLE.Spec.Sec6.Prop61Compare
import InteractingSLE.Spec.Sec6.CondMeanStop

/-!
# Boundary values of the joint retained mean from the two individual means

Proposition 3.8, read at prime ends by the landed union-comparison theorem,
transfers the individual side values to the joint local-set mean. The explicit
remaining geometric datum classifies each nonexceptional prime end as a side
of one retained set with a free collar, and identifies its surviving word.
No boundary-limit hypothesis on the joint mean is required here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE.Theorem14.SB.SewGerm

open LocalSets

/-- The prime ends of a retained component are accounted for by individual
retained sides or original real intervals, except finitely many marked fibers.
At each such prime end one individual mean has the specified finite word. -/
def HasUnionWordBoundary (A₁ A₂ : Set ℂ) (u₀ v w₁ w₂ : ℂ → ℝ) (χ : ℝ)
    (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ z₀ ∈ H \ (A₁ ∪ A₂), ∃ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
    IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    IsConformalBijection φc (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) H ∧
    IsBoundedHarmonicExtension b jumps G ∧
    ContinuousOn L (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    (∀ z ∈ connectedComponentIn (H \ (A₁ ∪ A₂)) z₀,
      deriv φc z = ‖deriv φc z‖ * Complex.exp (L z * Complex.I)) ∧
    E.Finite ∧
    EqOn v (fun z => G (φc z) - χ * L z) (connectedComponentIn (H \ (A₁ ∪ A₂)) z₀) ∧
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      (∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ A₁ ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₂ ∩ ball p r ⊆ A₁) ∧
        Tendsto (fun ζ => (w₁ (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) ∨
      (∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ A₂ ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₁ ∩ ball p r ⊆ A₂) ∧
        Tendsto (fun ζ => (w₂ (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0))

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens} {A₁ A₂ : Ω → Set ℂ}

/-- The Gaussian mean of the retained union inherits the actual individual
boundary values. Conditional independence of the sets follows from field
determination of the first set; Proposition 3.8 supplies both side comparisons. -/
theorem ae_survivingWordBoundary_union
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap X inferInstance) P)
    (hl₁ : IsLocalSet A₁ X P) (hl₂ : IsLocalSet A₂ X P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) X P g)
    (hg₁ : IsLocalSetMean A₁ X P g₁) (hg₂ : IsLocalSetMean A₂ X P g₂)
    (u₀ : ℂ → ℝ) (v : Ω → ℂ → ℝ) (χ : ℝ)
    (b : Ω → ℝ → ℝ) (jumps : Ω → Finset ℝ) {D : Set Ω}
    (hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω →
        g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω →
        g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundary (A₁ ω) (A₂ ω) u₀ (v ω) w₁ w₂ χ (b ω) (jumps ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ z, w z * φ z) →
      HasSurvivingWordBoundary (A₁ ω ∪ A₂ ω) u₀ (v ω) w χ (b ω) (jumps ω) := by
  have hci : CondIndepEv (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hX.measurable.comap_le hA₂.comap_le hd₁
  have hcmp₁ := Sec6.ae_tendsto_comp_sub_of_union_symm hX hA₁ hA₂ hci hl₁ hl₂ hunb₁ hg hg₁
  have hcmp₂ := Sec6.ae_tendsto_comp_sub_of_union hX hA₁ hA₂ hci hl₁ hl₂ hunb₂ hg hg₂
  filter_upwards [hcmp₁, hcmp₂, hg₁.2.1, hg₂.2.1, hword]
    with ω hc₁ hc₂ hg₁ω hg₂ω hwω hωD w hw hrep z₀ hz₀
  obtain ⟨w₁, hw₁, hrep₁⟩ := hg₁ω
  obtain ⟨w₂, hw₂, hrep₂⟩ := hg₂ω
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ :=
    hwω hωD w₁ w₂ hw₁ hrep₁ hw₂ hrep₂ z₀ hz₀
  refine ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, ?_⟩
  intro q hq hqE
  have hmaps₁ : MapsTo f (ball 0 1) (H \ A₁ ω) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A₁ ω ∪ A₂ ω)) z₀ (hf.2.mapsTo hζ)
    exact ⟨hz.1, fun hA => hz.2 (Or.inl hA)⟩
  have hmaps₂ : MapsTo f (ball 0 1) (H \ A₂ ω) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A₁ ω ∪ A₂ ω)) z₀ (hf.2.mapsTo hζ)
    exact ⟨hz.1, fun hA => hz.2 (Or.inr hA)⟩
  rcases hlim q hq hqE with ⟨p, hp, hpA, hr, hs⟩ | ⟨p, hp, hpA, hr, hs⟩
  · have hc := hc₁ w w₁ hw hrep hw₁ hrep₁ f q p hmaps₁ hp hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring
  · have hc := hc₂ w w₂ hw hrep hw₂ hrep₂ f q p hmaps₂ hp hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring

end InteractingSLE.Theorem14.SB.SewGerm
