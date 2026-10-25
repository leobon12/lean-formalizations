import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledPointDistance
import SupercriticalLQGUniqueness.B2.DG20Lim.PolarPointTightness

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_point_le_crossLenIn
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (U : Set ℂ) (z w : ℂ) :
    edist ((normalizedContLFPP ξ a φ).pt z)
      ((normalizedContLFPP ξ a φ).pt w) ≤
        ENNReal.ofReal (a : ℝ)⁻¹ * crossLenIn ξ φ U {z} {w} := by
  rw [normalizedContLFPP_edist_eq_lfppMetric,
    B2.Median.lfppMetric_apply, B2.LscTop.lfppDistance_eq_lfppD]
  have hdist : lfppD ξ φ z w ≤ crossLenIn ξ φ U {z} {w} := by
    simp only [crossLenIn, iInf_singleton]
    apply le_iInf
    intro P
    exact iInf_le_of_le
      (⟨P.1, P.2.1, fun _ _ => mem_univ _⟩ :
        {P : ℝ → ℂ // IsPiecewiseC1Path P z w ∧
          ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ univ}) le_rfl
  simpa only [mul_comm] using
    (mul_le_mul_left hdist (ENNReal.ofReal (a : ℝ)⁻¹))

end SupercriticalLQGUniqueness.B2.DG20Lim
