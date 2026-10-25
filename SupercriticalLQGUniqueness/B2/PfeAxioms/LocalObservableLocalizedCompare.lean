import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalizedLFPP

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem normalizedLocalizedLFPPMetric_internal_eq_localizedLFPP
    (ξ : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ))
    (ε : Set.Ioi (0 : ℝ)) (g : DistC)
    {U : Set ℂ} (hU : IsOpen U) (x y : U) :
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
      (locMollifyC (ε : ℝ) ε.property g)).internal U (x, y) =
      ENNReal.ofReal ((a : ℝ)⁻¹) * localizedLFPP ξ ε g U x y := by
  exact normalizedLFPPMetric_internal_eq_lfppDOn (ξ : ℝ) a
    (locMollifyC (ε : ℝ) ε.property g) hU x y

theorem normalized_localized_heat_internal_compare
    (ξ : Set.Ioi (0 : ℝ)) (a ε : Set.Ioi (0 : ℝ))
    (g : DistC) (φ : C(ℂ, ℝ))
    {U : Set ℂ} (hU : IsOpen U)
    {c : ℝ} (hc : 0 ≤ c)
    (hcomp : ∀ z w : ℂ,
      localizedLFPP ξ ε g U z w ≤ ENNReal.ofReal c * lfppDOn (ξ : ℝ) φ U z w ∧
      lfppDOn (ξ : ℝ) φ U z w ≤ ENNReal.ofReal c * localizedLFPP ξ ε g U z w)
    (x y : U) :
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
      (locMollifyC (ε : ℝ) ε.property g)).internal U (x, y) ≤
        ENNReal.ofReal c *
          (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ).internal U (x, y) ∧
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ).internal U (x, y) ≤
        ENNReal.ofReal c *
          (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
            (locMollifyC (ε : ℝ) ε.property g)).internal U (x, y) := by
  rw [normalizedLocalizedLFPPMetric_internal_eq_localizedLFPP ξ a ε g hU x y,
    normalizedLFPPMetric_internal_eq_lfppDOn (ξ : ℝ) a φ hU x y]
  constructor
  · calc
      ENNReal.ofReal ((a : ℝ)⁻¹) * localizedLFPP ξ ε g U x y ≤
          ENNReal.ofReal ((a : ℝ)⁻¹) *
            (ENNReal.ofReal c * lfppDOn (ξ : ℝ) φ U x y) :=
        by simpa only [mul_comm] using
          (mul_le_mul_left (hcomp x y).1 (ENNReal.ofReal ((a : ℝ)⁻¹)))
      _ = ENNReal.ofReal c *
          (ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn (ξ : ℝ) φ U x y) := by
        ac_rfl
  · calc
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDOn (ξ : ℝ) φ U x y ≤
          ENNReal.ofReal ((a : ℝ)⁻¹) *
            (ENNReal.ofReal c * localizedLFPP ξ ε g U x y) :=
        by simpa only [mul_comm] using
          (mul_le_mul_left (hcomp x y).2 (ENNReal.ofReal ((a : ℝ)⁻¹)))
      _ = ENNReal.ofReal c *
          (ENNReal.ofReal ((a : ℝ)⁻¹) * localizedLFPP ξ ε g U x y) := by
        ac_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
