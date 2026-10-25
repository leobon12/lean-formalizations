import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPUpper
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3

 







set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem normalizedLFPPMetric_internal_le_lfppDOn
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {U : Set ℂ} (x y : U) :
    (PfeWeyl.normalizedLFPPMetric ξ a φ).internal U (x, y) ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn ξ φ U x y := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hc0 : c ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hscale : ∀ u v : ℂ,
      PfeWeyl.normalizedLFPPMetric ξ a φ (u, v) =
        c * PfeWeyl.lfppLSCMetric ξ φ (u, v) := by
    intro u v
    rw [PfeWeyl.normalizedLFPPMetric_apply, PfeWeyl.lfppLSCMetric_apply]
  rw [Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
    (PfeWeyl.lfppLSCMetric ξ φ)
    (PfeWeyl.normalizedLFPPMetric ξ a φ) c hc0 ENNReal.ofReal_ne_top
    hscale U (x, y)]
  simpa only [mul_comm, c] using
    (mul_le_mul_left (lfppLSCMetric_internal_le_lfppDOn ξ φ x y) c)

end SupercriticalLQGUniqueness.B2.PfeAxioms
