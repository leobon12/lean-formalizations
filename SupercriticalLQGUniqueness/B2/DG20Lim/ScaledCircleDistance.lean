import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPAffine
import SupercriticalLQGUniqueness.B2.DG20Lim.PointScaleRealCoeff
import SupercriticalLQGUniqueness.B2.DG20Lim.UnitAnnulusCoords

 

set_option autoImplicit false
noncomputable section

open Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem normalizedContLFPP_unit_circle_scale
    (ξ : ℝ) (a a' : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (r : Ioi (0 : ℝ)) (cavg : ℝ) :
    LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
      ((B2.Polylog.dilateHomeo r.property) '' unitInnerCircle.toSet)
      ((B2.Polylog.dilateHomeo r.property) '' unitOuterCircle.toSet) =
      ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * cavg)) *
      LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a' (B2.Polylog.unitField φ r cavg))
        unitInnerCircle.toSet unitOuterCircle.toSet := by
  let κ : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ) * Real.exp (-(ξ * cavg)) /
    ((a' : ℝ) * (r : ℝ)))
  have hκpos : 0 < (a : ℝ) * Real.exp (-(ξ * cavg)) /
      ((a' : ℝ) * (r : ℝ)) :=
    div_pos (mul_pos a.property (Real.exp_pos _))
      (mul_pos a'.property r.property)
  have hκ0 : κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκpos).ne'
  have hκtop : κ ≠ ∞ := ENNReal.ofReal_ne_top
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast r.property.ne'
  have hφ (x : ℂ) : B2.Polylog.unitField φ r cavg x =
      φ ((0 : ℂ) + (r : ℂ) * x) + -cavg := by
    simp [B2.Polylog.unitField_apply]
  have hT (x : ℂ) : B2.Polylog.dilateHomeo r.property x =
      (0 : ℂ) + (r : ℂ) * x := by
    rw [B2.Polylog.dilateHomeo_apply r.property, Complex.real_smul]
    simp
  have hscale := (normalizedContLFPP_affine_costs ξ a a' hr0 (-cavg)
    hφ (B2.Polylog.dilateHomeo r.property) hT
    unitRatAnnulus.toSet unitInnerCircle.toSet unitOuterCircle.toSet).2
  have hscale' : LQGMetric.Blueprint.setDist
      (normalizedContLFPP ξ a' (B2.Polylog.unitField φ r cavg))
      unitInnerCircle.toSet unitOuterCircle.toSet =
      κ * LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
        ((B2.Polylog.dilateHomeo r.property) '' unitInnerCircle.toSet)
        ((B2.Polylog.dilateHomeo r.property) '' unitOuterCircle.toSet) := by
    simpa only [κ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Set.mem_Ioi.mp r.property), mul_neg] using hscale
  rw [← point_scale_real_coefficient ξ a a' r cavg]
  calc
    LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
      ((B2.Polylog.dilateHomeo r.property) '' unitInnerCircle.toSet)
      ((B2.Polylog.dilateHomeo r.property) '' unitOuterCircle.toSet) =
        (κ⁻¹ * κ) * LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
          ((B2.Polylog.dilateHomeo r.property) '' unitInnerCircle.toSet)
          ((B2.Polylog.dilateHomeo r.property) '' unitOuterCircle.toSet) := by
            rw [ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
    _ = κ⁻¹ * LQGMetric.Blueprint.setDist
        (normalizedContLFPP ξ a' (B2.Polylog.unitField φ r cavg))
        unitInnerCircle.toSet unitOuterCircle.toSet := by rw [hscale']; ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Lim
