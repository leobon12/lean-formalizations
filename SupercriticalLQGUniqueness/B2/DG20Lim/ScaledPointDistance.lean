import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPAffine
import SupercriticalLQGUniqueness.B2.Polylog.P4Prob

 


set_option autoImplicit false
noncomputable section

open LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_affine_edist_inv
    (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ))
    {φ φ' : C(ℂ, ℝ)} {b c : ℂ} (hc : c ≠ 0)
    (k₀ : ℝ)
    (hφ : ∀ x, φ' x = φ (b + c * x) + k₀)
    (x y : ℂ) :
    edist ((normalizedContLFPP ξ a φ).pt (b + c * x))
      ((normalizedContLFPP ξ a φ).pt (b + c * y)) =
      (ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
        ((a' : ℝ) * ‖c‖)))⁻¹ *
        edist ((normalizedContLFPP ξ a' φ').pt x)
          ((normalizedContLFPP ξ a' φ').pt y) := by
  let κ : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
    ((a' : ℝ) * ‖c‖))
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hκpos : 0 < (a : ℝ) * Real.exp (ξ * k₀) /
      ((a' : ℝ) * ‖c‖) :=
    div_pos (mul_pos a.property (Real.exp_pos _)) (mul_pos a'.property hcpos)
  have hκ0 : κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκpos).ne'
  have hκtop : κ ≠ ∞ := ENNReal.ofReal_ne_top
  have hscale := normalizedContLFPP_affine_edist ξ a a' hc k₀ hφ x y
  change edist ((normalizedContLFPP ξ a' φ').pt x)
      ((normalizedContLFPP ξ a' φ').pt y) =
      κ * edist ((normalizedContLFPP ξ a φ).pt (b + c * x))
        ((normalizedContLFPP ξ a φ).pt (b + c * y)) at hscale
  calc
    edist ((normalizedContLFPP ξ a φ).pt (b + c * x))
        ((normalizedContLFPP ξ a φ).pt (b + c * y)) =
      (κ⁻¹ * κ) *
        edist ((normalizedContLFPP ξ a φ).pt (b + c * x))
          ((normalizedContLFPP ξ a φ).pt (b + c * y)) := by
            rw [ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
    _ = κ⁻¹ * edist ((normalizedContLFPP ξ a' φ').pt x)
          ((normalizedContLFPP ξ a' φ').pt y) := by rw [hscale]; ac_rfl

 

theorem normalizedContLFPP_unit_point_scale
    (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (r : Set.Ioi (0 : ℝ)) (cavg : ℝ) :
    edist ((normalizedContLFPP ξ a φ).pt 0)
      ((normalizedContLFPP ξ a φ).pt (r : ℂ)) =
      (ENNReal.ofReal ((a : ℝ) * Real.exp (-(ξ * cavg)) /
        ((a' : ℝ) * (r : ℝ))))⁻¹ *
        edist ((normalizedContLFPP ξ a'
          (B2.Polylog.unitField φ r cavg)).pt 0)
          ((normalizedContLFPP ξ a'
            (B2.Polylog.unitField φ r cavg)).pt 1) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast r.property.ne'
  have hφ (x : ℂ) : B2.Polylog.unitField φ r cavg x =
      φ ((0 : ℂ) + (r : ℂ) * x) + -cavg := by
    simp [B2.Polylog.unitField_apply]
  have h := normalizedContLFPP_affine_edist_inv ξ a a' hr0
    (-cavg) hφ 0 1
  simpa only [zero_add, mul_zero, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Set.mem_Ioi.mp r.property), mul_neg] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
