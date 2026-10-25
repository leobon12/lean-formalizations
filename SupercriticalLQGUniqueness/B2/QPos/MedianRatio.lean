import SupercriticalLQGUniqueness.B2.QPos.UpperPowerWindow

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem median_le_quantile_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) {p : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2) (n : ℕ) :
    lambdaN ξ W P n ≤ LambdaN ξ W P n (ENNReal.ofReal p) *
      ellN ξ W P n (ENNReal.ofReal p) := by
  let _ := hW.isProbabilityMeasure
  have hq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hq2 : ENNReal.ofReal p ≤ 2⁻¹ :=
    (ENNReal.ofReal_le_ofReal hph).trans_eq ofReal_half_eq'
  have hℓ : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hq0 (hq2.trans_lt inv_two_lt_one') n
  have hmed : lambdaN ξ W P n ≤ ellBarN ξ W P n (ENNReal.ofReal p) :=
    T20B.lambdaN_le_ellBarN hq0 hq2 n
  have hratio : ellBarN ξ W P n (ENNReal.ofReal p) /
      ellN ξ W P n (ENNReal.ofReal p) ≤
        LambdaN ξ W P n (ENNReal.ofReal p) :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) /
      ellN ξ W P k (ENNReal.ofReal p)) (Finset.self_mem_range_succ n)
  have hbar : ellBarN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p) := by
    exact (div_le_iff₀ hℓ).mp hratio
  exact hmed.trans hbar

end SupercriticalLQGUniqueness.B2.QPos
