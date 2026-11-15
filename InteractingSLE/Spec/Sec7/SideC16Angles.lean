/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119HeightsFlow

/-! # Rational own-prefix heights at arbitrary flow angles

PROVE-SIDE-COLLAR2, R98. Apply the existing canonical flow-line height
theorem at every rational own stop. The angle is an arbitrary real;
there is no reduction modulo `2π` or restriction to `[-π/2, π/2]`.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideC16
open LocalSets Aux119Heights StripGeom WholeField

/-- For a canonical infinite constant-angle flow, every positive point
in the open half-plane has an actual rational own-prefix height. This
supplies both sides of generic Aux. 119, including the outer-arm angles. -/
theorem ae_rational_ownHeights_allAngles
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {θ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps 0 θ P h η ζ)
    {W : ℝ≥0 → Ω → ℝ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω)
      (fun t => η ω t - ((0 : ℝ) : ℂ)))
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc : ∀ ω, Continuous (η ω)) (h0 : ∀ ω, η ω 0 = 0)
    (hm : ∀ t, Measurable fun ω => η ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal η (centredField h u₀) P)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q, IsLocalSetMean (fun ω => η ω '' Icc 0 q ∩ H) (centredField h u₀) P (g q)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → η ω s ∈ H → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (η ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (η ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          g q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ θ (η ω) 0 (fun t => W t ω) q (η ω s) v u₀ := by
  have hEvery : ∀ q : ℚ≥0, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (η ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (η ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, s < q → η ω s ∈ H →
        HasSideHeights κ θ (η ω) 0 (fun t => W t ω) q (η ω s) v u₀ := by
    intro q
    have hq := ae_hasSideHeights_of_isFlowLine hκ hb hh hη htr hu₀ hc h0 hm hdet hloc (q : ℝ≥0)
      (ae_of_all _ fun _ _ _ _ => rfl) (hg q)
    filter_upwards [hq, hζ] with ω hqω hζω v hv hrep s hsq hsH
    exact hqω (by rw [hζω]; exact ENNReal.coe_lt_top) v hv hrep s hsq hsH
  filter_upwards [ae_all_iff.mpr hEvery] with ω hω s _hs hsH
  obtain ⟨q, hsq⟩ := exists_rat_gt (s : ℝ)
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast s.coe_nonneg.trans hsq.le
  let q' : ℚ≥0 := ⟨q, hq0⟩
  have hsq' : s < (q' : ℝ≥0) := by exact_mod_cast hsq
  exact ⟨q', hsq', fun v hv hrep => hω q' v hv hrep s hsq' hsH⟩

end InteractingSLE.Sec7.SideC16
