import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPEquality
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPNeighborhood

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem normalizedLFPPMetric_internal_eq_lfppDOn
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {U : Set ℂ} (hU : IsOpen U) (x y : U) :
    (PfeWeyl.normalizedLFPPMetric ξ a φ).internal U (x, y) =
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn ξ φ U x y := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hscale : ∀ u v : ℂ,
      PfeWeyl.normalizedLFPPMetric ξ a φ (u, v) =
        c * PfeWeyl.lfppLSCMetric ξ φ (u, v) := by
    intro u v
    rw [PfeWeyl.normalizedLFPPMetric_apply, PfeWeyl.lfppLSCMetric_apply]
  rw [Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
    (PfeWeyl.lfppLSCMetric ξ φ)
    (PfeWeyl.normalizedLFPPMetric ξ a φ) c hc0 ENNReal.ofReal_ne_top
    hscale U (x, y)]
  exact congrArg (c * ·) (lfppLSCMetric_internal_eq_lfppDOn ξ φ hU x y)

theorem neighborhoodInternal_normalized_eq_neighborhoodLFPP
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {V : Set ℂ} (hV : IsOpen V) (x y : V) (ρ : ℝ) :
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric ξ a φ) V x y ρ =
      neighborhoodLFPP ξ a φ V x y ρ := by
  unfold neighborhoodInternal neighborhoodLFPP
  apply iInf_congr
  intro u
  apply iInf_congr
  intro hu
  apply iInf_congr
  intro v
  apply iInf_congr
  intro hv
  exact normalizedLFPPMetric_internal_eq_lfppDOn ξ a φ hV u v

end SupercriticalLQGUniqueness.B2.PfeAxioms
