import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledPointDistance
import SupercriticalLQGUniqueness.B2.DG20Lim.PointScaleRealCoeff

 


set_option autoImplicit false
noncomputable section

open Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_translate_point_distance
    (ξ : ℝ) (a : Ioi (0 : ℝ))
    {φ ψ : C(ℂ, ℝ)} (z v : ℂ) (c : ℝ)
    (hψ : ∀ x, ψ x = φ (x + z) - c) :
    edist ((normalizedContLFPP ξ a φ).pt z)
      ((normalizedContLFPP ξ a φ).pt (v + z)) =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        edist ((normalizedContLFPP ξ a ψ).pt 0)
          ((normalizedContLFPP ξ a ψ).pt v) := by
  have hψ' (x : ℂ) : ψ x = φ (z + (1 : ℂ) * x) + -c := by
    simpa only [one_mul, add_comm, sub_eq_add_neg] using hψ x
  have h := normalizedContLFPP_affine_edist_inv ξ a a
    (b := z) (c := (1 : ℂ)) one_ne_zero (-c) hψ' 0 v
  have hcoeff := point_scale_real_coefficient ξ a a
    ⟨1, by norm_num⟩ c
  simp only [one_mul, mul_zero, add_zero, norm_one, mul_neg] at h
  rw [hcoeff] at h
  have ha : ((a : ℝ) / (a : ℝ)) = 1 := div_self a.property.ne'
  simpa only [one_mul, ha, add_comm z v] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
