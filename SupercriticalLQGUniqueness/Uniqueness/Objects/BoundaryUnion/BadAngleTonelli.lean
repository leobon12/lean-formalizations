import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic.TonelliBound
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion.Bad




 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic

theorem expected_bad_angle_mass_le_of_pointwise
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (μ : Measure LQGMetric.DistC) [SFinite μ]
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) (B : ℝ≥0∞)
    (hpoint : ∀ θ : ℝ,
      μ {g | (g, θ) ∈ Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs} ≤ B) :
    (∫⁻ g, ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs (g, θ)
      ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) ∂μ) ≤
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ * B := by
  classical
  let E := Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs
  have hE : MeasurableSet E :=
    Objects.BoundaryUnion.measurableSet_bad_boundary_relation ξ Q D hD c s R hs
  have h := lintegral_indicator_sections_le μ
    (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) E hE B hpoint
  simpa only [Objects.BoundaryUnion.badPointIndicator, Set.indicator, E] using h

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic
