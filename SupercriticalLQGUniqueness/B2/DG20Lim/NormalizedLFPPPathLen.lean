import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundPointBound
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPP

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem normalizedContLFPP_len_le_lfppLen
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) :
    (normalizedContLFPP ξ a φ).len P 0 1 ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ P := by
  let M := lfppContMetric ξ φ φ.continuous
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hlen : (normalizedContLFPP ξ a φ).len P 0 1 = c * M.len P 0 1 := by
    unfold ContMetric.len LQGMetric.MetricGeometry.curveLength
    exact LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
      (F := (normalizedContLFPP ξ a φ).pt ∘ P)
      (G := M.pt ∘ P) (c := c)
      (fun s t => by
        simp only [Function.comp_apply]
        rw [ContMetric.edist_pt, LQGMetric.LFPP.edist_lfppContMetric]
        rw [normalizedContLFPP, ContMetric.smulPos_apply,
          ENNReal.ofReal_mul (inv_pos.mpr a.property).le,
          lfppContMetric_apply, ENNReal.ofReal_toReal
            (LQGMetric.LFPP.lfppD_ne_top φ.continuous (P s) (P t))])
      (Icc 0 1)
  rw [hlen]
  exact mul_le_mul_of_nonneg_left
    (LQGMetric.LFPP.len_le_lfppLen φ.continuous hP le_rfl le_rfl) zero_le

end SupercriticalLQGUniqueness.B2.DG20Lim
