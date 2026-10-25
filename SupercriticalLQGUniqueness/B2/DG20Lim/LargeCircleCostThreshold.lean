import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledCircleDistance

 

set_option autoImplicit false
noncomputable section

open Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_scaled_circle_threshold
    (ξ : ℝ) (a a' : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (r : Ioi (0 : ℝ)) (c : ℝ) (T M : ℝ)
    (hT : 0 < T) (hM : 0 < M)
    (hfac : T * M ≤
      ((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c))
    (hunit : ENNReal.ofReal M⁻¹ ≤
      finiteCircleCoords
        (normalizedContLFPP ξ a' (B2.Polylog.unitField φ r c))
        (unitInnerCircle, unitOuterCircle)) :
    ENNReal.ofReal T ≤
      LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
        ((B2.Polylog.dilateHomeo r.property) '' unitInnerCircle.toSet)
        ((B2.Polylog.dilateHomeo r.property) '' unitOuterCircle.toSet) := by
  rw [normalizedContLFPP_unit_circle_scale]
  have hfac' : ENNReal.ofReal (T * M) ≤
      ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c)) :=
    ENNReal.ofReal_le_ofReal hfac
  have hprod : ENNReal.ofReal (T * M) * ENNReal.ofReal M⁻¹ =
      ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_mul (mul_pos hT hM).le]
    congr 1
    field_simp [hM.ne']
  rw [finiteCircleCoords] at hunit
  calc
    ENNReal.ofReal T = ENNReal.ofReal (T * M) * ENNReal.ofReal M⁻¹ := hprod.symm
    _ ≤ ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c)) *
          LQGMetric.Blueprint.setDist
            (normalizedContLFPP ξ a' (B2.Polylog.unitField φ r c))
            unitInnerCircle.toSet unitOuterCircle.toSet :=
      mul_le_mul hfac' hunit bot_le bot_le

end SupercriticalLQGUniqueness.B2.DG20Lim
