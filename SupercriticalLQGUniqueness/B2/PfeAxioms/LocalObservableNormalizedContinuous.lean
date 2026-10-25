import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteContinuous

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuous_normalizedLFPPMetric_internal
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {U : Set ℂ} (hU : IsOpen U) :
    Continuous (fun p : U × U =>
      (PfeWeyl.normalizedLFPPMetric ξ a φ).internal U (p.1, p.2)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hscale : ∀ u v : ℂ,
      PfeWeyl.normalizedLFPPMetric ξ a φ (u, v) =
        c * PfeWeyl.lfppLSCMetric ξ φ (u, v) := by
    intro u v
    rw [PfeWeyl.normalizedLFPPMetric_apply, PfeWeyl.lfppLSCMetric_apply]
  have hpoint : ∀ p : U × U,
      (PfeWeyl.normalizedLFPPMetric ξ a φ).internal U (p.1, p.2) =
        c * (PfeWeyl.lfppLSCMetric ξ φ).internal U (p.1, p.2) := by
    intro p
    exact Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
      (PfeWeyl.lfppLSCMetric ξ φ)
      (PfeWeyl.normalizedLFPPMetric ξ a φ) c hc0 ENNReal.ofReal_ne_top
      hscale U (p.1, p.2)
  simp_rw [hpoint]
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    (continuousOn_lfppLSCMetric_internal ξ φ hU)

end SupercriticalLQGUniqueness.B2.PfeAxioms
