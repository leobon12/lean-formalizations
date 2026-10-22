import HigherDimLQGMetric.Sec9.Interfaces
import HigherDimLQGMetric.ScaleBin.Ratio
import HigherDimLQGMetric.ScaleBin.Point

/-!
# The macroscopic normalizer ratio in [S] §9

The increment between sphere averages at radii `R` and `8R` has uniformly bounded
variance. A two-sided Gaussian tail bounds the ratio of the two normalizers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- The upper half of (33), uniformly over radii and whole-space LGFs. -/
theorem macroRatioShape {d : ℕ} (hd : 2 ≤ d) (ξ Q : ℝ) : MacroRatioShape d ξ Q := by
  obtain ⟨V, hV, hvar⟩ := ScaleBin.exists_point_variance_bound hd
  intro δ hδ
  by_cases hδbig : 1 ≤ δ
  · refine ⟨1, le_refl _, ?_⟩
    intro Ω _ P _ h hh R hR
    calc
      P {ω | 1 * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hδbig
  let T : ℝ := V + 1 + Real.log (2 / δ) / 2
  let L : ℝ := Real.exp (|ξ| * T)
  have hδ2 : 0 < 2 / δ := div_pos (by norm_num) hδ
  have hδle : δ < 1 := lt_of_not_ge hδbig
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg ((one_le_div hδ).2 (by linarith))
  have hT : 0 ≤ T := by
    dsimp [T]
    linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (abs_nonneg _) hT)
  refine ⟨L, hL, ?_⟩
  intro Ω _ P _ h hh R hR
  let X : Ω → ℝ := fun ω => sphereAvg (h ω) R 0 - sphereAvg (h ω) (8 * R) 0
  have hG := hh.hasGaussianLaw_sphereAvg_sub hd hR (by positivity : 0 < 8 * R) 0 0
  have hXv : Var[X; P] ≤ V := by
    have hz : ‖(0 : Rd d)‖ < 5 * R := by simpa using (show (0 : ℝ) < 5 * R by positivity)
    have hv := hvar hh hR (le_refl R) (0 : Rd d) hz
    simpa only [div_self hR.ne', Real.log_one, add_zero, mul_one] using hv
  have ht := ScaleBin.gaussian_abs_tail_le hG.1 hG.2 hXv (A := T)
  have hbound : 2 * Real.exp (-2 * T + 2 * V) ≤ δ := by
    have heq : -2 * T + 2 * V = -2 - Real.log (2 / δ) := by dsimp [T]; ring
    rw [heq, Real.exp_sub, Real.exp_log hδ2]
    have hexp : Real.exp (-2) ≤ 1 := (Real.exp_le_one_iff).2 (by norm_num)
    calc
      2 * (Real.exp (-2) / (2 / δ)) = δ * Real.exp (-2) := by
        field_simp
      _ ≤ δ := by nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hexp)]
  have hsubset : {ω | L * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0} ⊆
      {ω | T ≤ |X ω|} := by
    intro ω hw
    have hS : 0 < macroS ξ Q (h ω) R := by
      dsimp [macroS]
      positivity
    have hratio : L < sNorm ξ Q (h ω) R 0 / macroS ξ Q (h ω) R :=
      (lt_div_iff₀ hS).2 hw
    rw [ScaleBin.sNorm_div_macroS_eq_exp hR hR (h ω) 0] at hratio
    simp only [div_self hR.ne', Real.log_one, mul_zero, zero_add] at hratio
    have hlogexp : |ξ| * T < ξ * X ω := by
      exact Real.exp_lt_exp.mp hratio
    have hmul : ξ * X ω ≤ |ξ| * |X ω| := by
      calc ξ * X ω ≤ |ξ * X ω| := le_abs_self _
        _ = |ξ| * |X ω| := abs_mul _ _
    by_contra hn
    have hsmall : |X ω| < T := lt_of_not_ge hn
    have hsmall' := mul_le_mul_of_nonneg_left hsmall.le (abs_nonneg ξ)
    linarith
  calc
    P {ω | L * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0}
        ≤ P {ω | T ≤ |X ω|} := measure_mono hsubset
    _ = ENNReal.ofReal (P.real {ω | T ≤ |X ω|}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (ht.trans hbound)

end HigherDimLQGMetric
