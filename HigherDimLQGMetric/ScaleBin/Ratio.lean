import HigherDimLQGMetric.ScaleBin.Grid

/-!
# From a Gaussian sphere-average increment to the normalizer ratio

For small `ε`, the interval `ε²R ≤ r ≤ εR` gives two logarithmic scales.
The extra `1` in the point-tail threshold is absorbed by `-log ε ≥ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.ScaleBin

open HigherDimLFPP (Rd)

/-- Exact logarithmic form of the ratio in Lemma 8.1. -/
theorem sNorm_div_macroS_eq_exp {d : ℕ} {ξ Q r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (g : DistRd d) (z : Rd d) :
    sNorm ξ Q g r z / macroS ξ Q g R =
      Real.exp (ξ * Q * Real.log (r / R) +
        ξ * (sphereAvg g r z - sphereAvg g (8 * R) 0)) := by
  unfold sNorm macroS
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hR]
  calc
    Real.exp (Real.log r * (ξ * Q)) * Real.exp (ξ * sphereAvg g r z) /
      (Real.exp (Real.log R * (ξ * Q)) * Real.exp (ξ * sphereAvg g (8 * R) 0)) =
        Real.exp (Real.log r * (ξ * Q) + ξ * sphereAvg g r z -
          (Real.log R * (ξ * Q) + ξ * sphereAvg g (8 * R) 0)) := by
            rw [Real.exp_sub, Real.exp_add, Real.exp_add]
    _ = Real.exp (ξ * Q * Real.log (r / R) +
        ξ * (sphereAvg g r z - sphereAvg g (8 * R) 0)) := by
      rw [Real.log_div hr.ne' hR.ne']
      congr 1
      ring

/-- A point obeying the Chernoff threshold satisfies both scale-bin inequalities. -/
theorem ratio_bounds_of_small_increment {d : ℕ} {ξ Q D R r ε : ℝ}
    (hξ : 0 < ξ) (hQ : 0 < Q) (hD : 0 ≤ D)
    (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ Real.exp (-1))
    (hrlo : ε ^ 2 * R ≤ r) (hrhi : r ≤ ε * R)
    (g : DistRd d) (z : Rd d)
    (hX : |sphereAvg g r z - sphereAvg g (8 * R) 0| <
      (D + (d : ℝ) + 2) * (1 + Real.log (R / r))) :
    ε ^ (2 * ξ * Q + 3 * ξ * (D + (d : ℝ) + 2) + 1) ≤
      sNorm ξ Q g r z / macroS ξ Q g R ∧
      sNorm ξ Q g r z / macroS ξ Q g R ≤
        ε ^ (-(2 * ξ * Q + 3 * ξ * (D + (d : ℝ) + 2) + 1)) := by
  have hε1 : ε < 1 := lt_of_le_of_lt hεsmall (by norm_num)
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (pow_pos hε 2) hR) hrlo
  have ht : 0 < r / R := div_pos hr hR
  have htlo : ε ^ 2 ≤ r / R := (le_div_iff₀ hR).2 hrlo
  have hthi : r / R ≤ ε := (div_le_iff₀ hR).2 hrhi
  have hlogε : Real.log ε ≤ -1 := by
    simpa only [Real.log_exp] using Real.log_le_log hε hεsmall
  have hlogneg : Real.log ε < 0 := by linarith
  have hlogtlo : 2 * Real.log ε ≤ Real.log (r / R) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      (Real.log_le_log (pow_pos hε 2) htlo)
  have hlogthi : Real.log (r / R) ≤ Real.log ε :=
    Real.log_le_log ht hthi
  have hlogratio : Real.log (R / r) = -Real.log (r / R) := by
    rw [show R / r = (r / R)⁻¹ by field_simp, Real.log_inv]
  have hK : 0 ≤ D + (d : ℝ) + 2 := by positivity
  have hA : (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
      3 * (D + (d : ℝ) + 2) * (-Real.log ε) := by
    rw [hlogratio]
    have h1 : 1 - Real.log (r / R) ≤ 3 * (-Real.log ε) := by linarith
    nlinarith only [mul_nonneg hK (sub_nonneg.mpr h1)]
  have hXL := (abs_lt.mp hX).1
  have hXU := (abs_lt.mp hX).2
  let B : ℝ := 2 * ξ * Q + 3 * ξ * (D + (d : ℝ) + 2) + 1
  let X : ℝ := sphereAvg g r z - sphereAvg g (8 * R) 0
  let Y : ℝ := ξ * Q * Real.log (r / R) + ξ * X
  have hYlo : B * Real.log ε ≤ Y := by
    dsimp [B, Y, X]
    have hmul1 := mul_nonneg (mul_nonneg hξ.le hQ.le)
      (sub_nonneg.mpr hlogtlo)
    have hmul2 := mul_nonneg hξ.le
      (show 0 ≤ X + 3 * (D + (d : ℝ) + 2) * (-Real.log ε) by
        dsimp [X]
        linarith only [hXL, hA])
    nlinarith only [hmul1, hmul2, hlogneg]
  have hYhi : Y ≤ -B * Real.log ε := by
    dsimp [B, Y, X]
    have hmul1 := mul_nonneg (mul_nonneg hξ.le hQ.le)
      (sub_nonneg.mpr hlogthi)
    have hmul2 := mul_nonneg hξ.le
      (show 0 ≤ 3 * (D + (d : ℝ) + 2) * (-Real.log ε) - X by
        dsimp [X]
        linarith only [hXU, hA])
    have hmul3 : 0 ≤ (3 * ξ * Q + 1) * (-Real.log ε) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith only [hmul1, hmul2, hmul3]
  rw [sNorm_div_macroS_eq_exp hr hR, Real.rpow_def_of_pos hε,
    Real.rpow_def_of_pos hε]
  constructor
  · apply Real.exp_le_exp.mpr
    dsimp [B] at hYlo
    nlinarith only [hYlo]
  · apply Real.exp_le_exp.mpr
    dsimp [B] at hYhi
    nlinarith only [hYhi]

end HigherDimLQGMetric.ScaleBin
