import SupercriticalLQGUniqueness.B2.DG20Lim.PointScaleRealCoeff

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_scaled_point_le_power
    (ξ : ℝ) (a a' : Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (r : Ioi (0 : ℝ)) (c : ℝ)
    (C p M : ℝ) (hC : 0 ≤ C)
    (hpow : ((r : ℝ) * (a' : ℝ) / (a : ℝ)) *
        Real.exp (ξ * c) ≤ C * (r : ℝ) ^ p)
    (hunit : edist ((normalizedContLFPP ξ a'
        (B2.Polylog.unitField φ r c)).pt 0)
      ((normalizedContLFPP ξ a'
        (B2.Polylog.unitField φ r c)).pt 1) ≤
        ENNReal.ofReal M) :
    edist ((normalizedContLFPP ξ a φ).pt 0)
      ((normalizedContLFPP ξ a φ).pt (r : ℂ)) ≤
        ENNReal.ofReal (C * (r : ℝ) ^ p * M) := by
  rw [normalizedContLFPP_unit_point_scale ξ a a' φ r c,
    point_scale_real_coefficient ξ a a' r c]
  have hfactor :
      ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c)) ≤
      ENNReal.ofReal (C * (r : ℝ) ^ p) :=
    ENNReal.ofReal_le_ofReal hpow
  calc
    ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c)) *
      edist ((normalizedContLFPP ξ a'
        (B2.Polylog.unitField φ r c)).pt 0)
        ((normalizedContLFPP ξ a'
          (B2.Polylog.unitField φ r c)).pt 1) ≤
      ENNReal.ofReal (C * (r : ℝ) ^ p) *
        ENNReal.ofReal M :=
          mul_le_mul hfactor hunit zero_le zero_le
    _ = ENNReal.ofReal (C * (r : ℝ) ^ p * M) := by
      rw [ENNReal.ofReal_mul
        (mul_nonneg hC (Real.rpow_nonneg r.property.le _))]

end SupercriticalLQGUniqueness.B2.DG20Lim
