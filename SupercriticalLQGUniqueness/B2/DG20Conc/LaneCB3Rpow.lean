import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3RatioMoment

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneC_B3_ratio_ofReal_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ Q ζ : ℝ) (n K : ℕ) (ω : Ω)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal
        ((laneCB3Scale ξ Q ζ P W n K /
          lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω) ^ q) =
      (ENNReal.ofReal
        (laneCB3Scale ξ Q ζ P W n K /
          lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω)) ^ q := by
  have hψ := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le n)
  have hL : 0 < lenObs ξ (psiMN Qψ W P 0 n)
      (rectAB 1 1) ω :=
    lenObs_pos hψ.cont _ (by norm_num [rectAB]) (by norm_num [rectAB])
      (by norm_num [MarkedRect.crossWidth, rectAB]) ω
  have hx : 0 ≤ laneCB3Scale ξ Q ζ P W n K /
      lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω :=
    div_nonneg (by
      unfold laneCB3Scale
      exact (mul_pos (by positivity) (lambdaN_pos hW (n - K))).le) hL.le
  exact (ENNReal.ofReal_rpow_of_nonneg hx hq).symm

end SupercriticalLQGUniqueness.B2.DG20Conc
