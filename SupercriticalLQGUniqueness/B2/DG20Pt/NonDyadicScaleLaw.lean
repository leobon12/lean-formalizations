import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicTight

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_phiVer_scale_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    P.map (fun ω x => phiVer W P a b ((r : ℂ) * x) ω) =
      P.map (fun ω x => phiVer W P (a / r) (b / r) x ω) := by
  have h₁ := isPhiVersion_phiVer hW ha hab
  have h₂ := isPhiVersion_phiVer hW (div_pos ha hr)
    (div_le_div_of_nonneg_right hab hr.le)
  exact map_modification_scale hW ha hab hr
    (fun x => h₁.meas _) (fun x => h₂.meas _)
    (fun x => h₁.ae_eq _) (fun x => h₂.ae_eq _) measurable_id

 
private theorem dyadic_band_div_rpow (n : ℕ) (s : ℝ) :
    ((2 : ℝ)⁻¹ ^ n) / (2 : ℝ) ^ s =
      (2 : ℝ) ^ (-((n : ℝ) + s)) := by
  have hpow : (2 : ℝ)⁻¹ ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]
  rw [div_eq_mul_inv, hpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) s,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

 

theorem dg20_phiMN_real_shift_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n : ℕ) (s : ℝ) :
    P.map (fun ω x => phiMN W P 0 n ((↑((2 : ℝ) ^ s) : ℂ) * x) ω) =
      P.map (fun ω x => phiVer W P
        ((2 : ℝ) ^ (-((n : ℝ) + s))) ((2 : ℝ) ^ (-s)) x ω) := by
  have h := dg20_phiVer_scale_law P W hW
    (show 0 < (2 : ℝ)⁻¹ ^ n by positivity)
    (show (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 0 by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n))
    (show 0 < (2 : ℝ) ^ s by positivity)
  convert h using 1
  · simp only [phiMN, pow_zero]
  · simp only [pow_zero, dyadic_band_div_rpow, one_div]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) s]

end SupercriticalLQGUniqueness.B2.DG20Pt
