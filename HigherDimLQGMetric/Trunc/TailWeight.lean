import HigherDimLQGMetric.Trunc.RadialAll
import HigherDimLQGMetric.ConvField.RadialWeightIntegrable

/-! A scale independent sphere growth bound on the tail of the localized kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

def l2c_tailWeight {d : ℕ} (ε s : ℝ) : ℝ :=
  (1 - radBump (d := d) (Real.sqrt ε / 2) (Real.sqrt ε)
      ((ε * s) • e₁ d)) * l2b_growthWeight (ε * s)

theorem l2c_tailWeight_nonneg {d : ℕ} (ε s : ℝ) :
    0 ≤ l2c_tailWeight (d := d) ε s := by
  have hb := l2c_radBump_mem_Icc (Real.sqrt ε / 2) (Real.sqrt ε)
    ((ε * s) • e₁ d)
  have hw : 0 ≤ l2b_growthWeight (ε * s) := by
    unfold l2b_growthWeight
    exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  exact mul_nonneg (sub_nonneg.2 hb.2) hw

theorem l2c_growthWeight_scaled_tail {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hs : 0 < s)
    (htail : Real.sqrt ε / 2 ≤ ε * s) :
    l2b_growthWeight (ε * s) ≤ 4 * l2b_growthWeight s := by
  have hsq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsqrtle : Real.sqrt ε ≤ 1 / 2 := by nlinarith [sq_nonneg (Real.sqrt ε - 1 / 2)]
  have hsone : 1 ≤ s := by
    have h1 : 1 / 2 ≤ Real.sqrt ε * s := by
      nlinarith [htail]
    nlinarith
  have hs4 : 1 ≤ 4 * ε * s ^ 2 := by
    have h1 : 1 / 2 ≤ Real.sqrt ε * s := by nlinarith [htail]
    have h2 := sq_nonneg (Real.sqrt ε * s - 1 / 2)
    nlinarith [sq_nonneg (Real.sqrt ε * s), hsq]
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hsone
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le (by linarith)
  have hlog4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlog_inv : Real.log (ε * s)⁻¹ ≤ Real.log (4 * s) := by
    apply Real.log_le_log (inv_pos.mpr (mul_pos hε hs))
    have haux : 1 / (ε * s) ≤ 4 * s :=
      (div_le_iff₀ (mul_pos hε hs)).2 (by nlinarith [hs4])
    simpa only [one_div] using haux
  have hlog_mul : Real.log (ε * s) ≤ Real.log s := by
    rw [Real.log_mul hε.ne' hs.ne']
    linarith
  have hlog4s : Real.log (4 * s) = Real.log 4 + Real.log s :=
    Real.log_mul (by norm_num) hs.ne'
  have hws1 : 1 ≤ l2b_growthWeight s := by
    unfold l2b_growthWeight
    exact le_max_of_le_right (le_max_right _ _)
  have hwslog : Real.log s ≤ l2b_growthWeight s := by
    unfold l2b_growthWeight
    calc Real.log s ≤ max (Real.log s) 0 := le_max_left _ _
      _ = (max (Real.log s) 0) ^ (1 / 2 + 1 / 2 : ℝ) := by norm_num
      _ ≤ max ((max (Real.log s) 0) ^ (1 / 2 + 1 / 2 : ℝ)) 1 := le_max_left _ _
      _ ≤ _ := le_max_right _ _
  have hprod : 0 < ε * s := mul_pos hε hs
  have hlogps : max (Real.log (ε * s)) 0 ≤ Real.log s := by
    exact max_le hlog_mul hlogs
  simp only [l2b_growthWeight, show (1 / 2 + 1 / 2 : ℝ) = 1 by ring,
    Real.rpow_one] at *
  apply max_le
  · rw [hlog4s] at hlog_inv
    linarith
  · apply max_le
    · linarith
    · linarith

theorem l2c_tailWeight_eq_zero_of_inner {d : ℕ} (hd : 2 ≤ d)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (hinner : ε * s ≤ Real.sqrt ε / 2) :
    l2c_tailWeight (d := d) ε s = 0 := by
  have hnorm : ‖(ε * s) • e₁ d‖ = ε * s := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
      Real.norm_eq_abs, abs_of_pos (mul_pos hε hs)]
  have hb : radBump (d := d) (Real.sqrt ε / 2) (Real.sqrt ε)
      ((ε * s) • e₁ d) = 1 := by
    apply l2c_radBump_eq_one (by positivity)
      (by have hp := Real.sqrt_pos.2 hε; linarith)
    rw [hnorm]
    exact hinner
  simp only [l2c_tailWeight, hb, sub_self, zero_mul]

theorem l2c_tailWeight_le {d : ℕ} (hd : 2 ≤ d) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hs : 0 < s) :
    l2c_tailWeight (d := d) ε s ≤ 4 * l2b_growthWeight s := by
  by_cases hinner : ε * s ≤ Real.sqrt ε / 2
  · rw [l2c_tailWeight_eq_zero_of_inner hd hε hs hinner]
    have hw : 0 ≤ l2b_growthWeight s := by
      unfold l2b_growthWeight
      exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    positivity
  · have htail : Real.sqrt ε / 2 ≤ ε * s := le_of_not_ge hinner
    have hbound := l2c_growthWeight_scaled_tail hε hεsmall hs htail
    have hb := l2c_radBump_mem_Icc (Real.sqrt ε / 2) (Real.sqrt ε)
      ((ε * s) • e₁ d)
    have hw : 0 ≤ l2b_growthWeight (ε * s) := by
      unfold l2b_growthWeight
      exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    unfold l2c_tailWeight
    calc
      (1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) ((ε * s) • e₁ d)) *
          l2b_growthWeight (ε * s)
        ≤ 1 * l2b_growthWeight (ε * s) := by
          gcongr
          exact sub_le_self 1 hb.1
      _ ≤ 4 * l2b_growthWeight s := by simpa using hbound

theorem l2c_tailWeight_eventually_zero {d : ℕ} (hd : 2 ≤ d)
    {s : ℝ} (hs : 0 < s) :
    (fun ε : ℝ => l2c_tailWeight (d := d) ε s) =ᶠ[𝓝[>] (0 : ℝ)]
      fun _ => 0 := by
  have hδ : 0 < 1 / (4 * s ^ 2) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  apply l2c_tailWeight_eq_zero_of_inner hd hε.1 hs
  have hsq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.1.le
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hs2 : ε * s ^ 2 ≤ 1 / 4 := by
    have hss : 0 < 4 * s ^ 2 := by positivity
    have := (le_div_iff₀ hss).1 hε.2.le
    nlinarith
  have hbound : Real.sqrt ε * s ≤ 1 / 2 := by
    nlinarith [mul_nonneg hsqrt hs.le]
  have hmul := mul_le_mul_of_nonneg_left hbound hsqrt
  nlinarith [hmul]

end HigherDimLQGMetric
