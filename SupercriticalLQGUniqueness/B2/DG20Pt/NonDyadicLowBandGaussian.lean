import SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicCompareCoupling
import LQGMetric.Papers.DDDF.S6P28Sup

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_low_band_unit_square_gaussian
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (s u : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤
        ⨆ v : ferniqueBox 0 1,
          |phiVer W P ((2 : ℝ) ^ (-s)) 1 v ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * Real.log 2)) := by
  let a : ℝ := (2 : ℝ) ^ (-s)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    exact (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).2
      (Or.inl ⟨by norm_num, by linarith⟩)
  have hahalf : (1 / 2 : ℝ) ≤ a := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ -s by linarith)
    norm_num at h ⊢
    exact h
  have hδ₁ : ((2 : ℝ) ^ (0 : ℕ))⁻¹ ≤ 2 * a := by
    norm_num at hahalf ⊢
    linarith
  have hδ₂ : a ≤ ((2 : ℝ) ^ (0 : ℕ))⁻¹ := by
    norm_num
    exact ha1.le
  have hsharp := LQGMetric.DDDF.S6P28.phiVer_sup_tail_sharp hW 0 hδ₁ hδ₂ hu
  have hlog0 : 0 < Real.log (1 / a) :=
    Real.log_pos (one_lt_one_div ha0 ha1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log (1 / a) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    exact (div_le_iff₀ ha0).2 (by nlinarith)
  have hquot : u ^ 2 / (2 * Real.log 2) ≤
      u ^ 2 / (2 * Real.log (1 / a)) := by
    exact div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
  have hexp : Real.exp (-u ^ 2 / (2 * Real.log (1 / a))) ≤
      Real.exp (-u ^ 2 / (2 * Real.log 2)) :=
    Real.exp_le_exp.2 (by simpa only [neg_div] using neg_le_neg hquot)
  simp only [pow_zero, mul_one] at hsharp
  simpa only [a] using
    hsharp.trans (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2))

end SupercriticalLQGUniqueness.B2.DG20Pt
