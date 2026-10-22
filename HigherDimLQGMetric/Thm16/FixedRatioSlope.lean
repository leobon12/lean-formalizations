import HigherDimLQGMetric.Thm16.BoundedSlope
import HigherDimLQGMetric.Thm16.RatioAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Geometric telescoping identifies the slope using only fixed scale ratios. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

theorem l9c_log_c_of_fixed_ratio {a c : ℝ → ℝ} {lam K : ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → 0 < a ε)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hK : 1 ≤ K)
    (hA : Tendsto (fun ε => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 lam))
    (hR : ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      K⁻¹ * c r ≤ l9c_ratio a ε r ∧
        l9c_ratio a ε r ≤ K * c r)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.log (c r) - Real.log K ≤ (1 - lam) * Real.log r ∧
      (1 - lam) * Real.log r ≤ Real.log (c r) + Real.log K := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1,
        Filter.Eventually.of_forall fun n => (pow_pos hr n)⟩
  have hseq : Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    hpow.comp (Filter.tendsto_add_atTop_nat 1)
  let b : ℕ → ℝ := fun n => Real.log (a (r ^ n))
  have hb : Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop
      (𝓝 (lam * Real.log r)) := by
    have ht := (hA.comp hpow).mul_const (Real.log r)
    apply ht.congr'
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
    have hlogr : Real.log r ≠ 0 := (Real.log_neg hr hr1).ne
    have hlog : Real.log (r ^ n) = (n : ℝ) * Real.log r := Real.log_pow r n
    dsimp [b]
    rw [hlog]
    field_simp [hn0, hlogr]
  have hstep : ∀ᶠ n : ℕ in atTop,
      Real.log r - (Real.log (c r) + Real.log K) ≤ b (n + 1) - b n ∧
      b (n + 1) - b n ≤ Real.log r - (Real.log (c r) - Real.log K) := by
    filter_upwards [hseq.eventually (hR r hr)] with n hratio
    have hrn : 0 < r ^ n := pow_pos hr n
    have hrns : 0 < r ^ (n + 1) := pow_pos hr (n + 1)
    have heps : r ^ (n + 1) / r = r ^ n := by
      rw [pow_succ]
      exact mul_div_cancel_right₀ _ hr.ne'
    have hratpos : 0 < l9c_ratio a (r ^ (n + 1)) r := by
      unfold l9c_ratio
      rw [heps]
      exact div_pos (mul_pos hr (ha _ hrn)) (ha _ hrns)
    have hlogratio : Real.log (l9c_ratio a (r ^ (n + 1)) r) =
        Real.log r + b n - b (n + 1) := by
      unfold l9c_ratio
      rw [heps, Real.log_div (mul_ne_zero hr.ne' (ha _ hrn).ne') (ha _ hrns).ne',
        Real.log_mul hr.ne' (ha _ hrn).ne']
    have hloglo : Real.log (c r) - Real.log K ≤
        Real.log (l9c_ratio a (r ^ (n + 1)) r) := by
      have hh := Real.log_le_log (mul_pos (inv_pos.mpr hKpos) (hc r hr)) hratio.1
      rw [Real.log_mul (inv_ne_zero hKpos.ne') (hc r hr).ne', Real.log_inv] at hh
      linarith
    have hloghi : Real.log (l9c_ratio a (r ^ (n + 1)) r) ≤
        Real.log (c r) + Real.log K := by
      have hh := Real.log_le_log hratpos hratio.2
      rw [Real.log_mul hKpos.ne' (hc r hr).ne'] at hh
      linarith
    dsimp [b]
    rw [hlogratio] at hloglo hloghi
    constructor <;> linarith
  obtain ⟨hlo, hhi⟩ := l9c_limit_slope_of_bounded_steps hb hstep
  constructor <;> linarith

end HigherDimLQGMetric
