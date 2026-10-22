import HigherDimLQGMetric.Sec8b.Prop86ClassRate

/-! Fixed moment and sample-size parameters that beat every requested power. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter
open scoped Topology

theorem s7b_exists_k_threshold (k : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
      (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ) := by
  have htend : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (1 / 2 : ℝ))
      (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_inv_nhdsGT_zero
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ) :=
    htend.eventually (eventually_ge_atTop _)
  obtain ⟨ε₀, hε₀, hεall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  exact ⟨ε₀, hε₀, fun hε hεlt => hεall ⟨hε, hεlt⟩⟩

theorem s7b_rate_parameters (d : ℕ) (hd : 1 ≤ d)
    {κ N : ℝ} (hκ : 0 < κ) (hN : 0 < N) :
    ∃ pH : ℝ, 1 < pH ∧ ∃ k : ℕ, 1 ≤ k ∧
      (1 / 4 : ℝ) + (2 * d * k : ℕ) * pH⁻¹ -
        (⌈κ * k⌉₊ : ℝ) / 2 ≤ -N := by
  let pH : ℝ := 16 * d / κ + 2
  let k : ℕ := ⌈8 * (N + 1) / κ⌉₊ + 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpH : 1 < pH := by
    have hp : 0 < 16 * (d : ℝ) / κ := by positivity
    dsimp [pH]
    linarith only [hp]
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hκpH : κ * pH = 16 * d + 2 * κ := by
    dsimp [pH]
    field_simp
  have hdiv : 2 * (d : ℝ) * pH⁻¹ ≤ κ / 8 := by
    have hp : 0 < pH := by linarith only [hpH]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hκpH, hκ]
  have hprod : ((2 * d * k : ℕ) : ℝ) * pH⁻¹ ≤ κ * k / 8 := by
    have hm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg k)
    push_cast at hm ⊢
    nlinarith only [hm]
  have hceil : κ * k ≤ (⌈κ * k⌉₊ : ℝ) := Nat.le_ceil _
  have hkceil : 8 * (N + 1) / κ ≤ (k : ℝ) := by
    have hc : 8 * (N + 1) / κ ≤
        (⌈8 * (N + 1) / κ⌉₊ : ℝ) :=
      Nat.le_ceil _
    dsimp [k]
    push_cast
    linarith only [hc]
  have hκk : 8 * (N + 1) ≤ κ * k := by
    have h := mul_le_mul_of_nonneg_left hkceil hκ.le
    have hcancel : κ * (8 * (N + 1) / κ) = 8 * (N + 1) := by
      field_simp
    rw [hcancel] at h
    nlinarith only [h]
  refine ⟨pH, hpH, k, hk, ?_⟩
  nlinarith only [hprod, hceil, hκk, hN]

end HigherDimLQGMetric
