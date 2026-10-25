import Mathlib




 











set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

theorem ev_pos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := eventually_mem_nhdsWithin

theorem ev_lt {a : ℝ} (ha : 0 < a) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < a :=
  Filter.mem_of_superset (Ioo_mem_nhdsGT ha) fun _ hx => hx.2

theorem ev_le {a : ℝ} (ha : 0 < a) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ a :=
  (ev_lt ha).mono fun _ hx => hx.le

 
theorem tendsto_rpow_nhdsGT {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun x : ℝ => x ^ θ) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
  rw [Real.zero_rpow hθ.ne'] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

theorem ev_rpow_lt {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ θ < c :=
  (tendsto_rpow_nhdsGT hθ).eventually_lt_const hc

 
theorem ev_mul_rpow_lt {θ a c : ℝ} (hθ : 0 < θ) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), a * x ^ θ < c := by
  filter_upwards [ev_rpow_lt hθ (div_pos hc ha)] with x hx
  calc a * x ^ θ < a * (c / a) := mul_lt_mul_of_pos_left hx ha
    _ = c := by field_simp

 
theorem ev_two_mul_rpow_lt {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), (2 * x) ^ θ < c := by
  have h2 : 0 < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos two_pos θ
  filter_upwards [ev_pos, ev_mul_rpow_lt hθ h2 hc] with x hx hlt
  rw [Real.mul_rpow (by norm_num) hx.le]
  exact hlt

theorem ev_atTop_gt (a : ℝ) : ∀ᶠ y in atTop, a < y := eventually_gt_atTop a

theorem ev_nat_ge (n : ℕ) : ∀ᶠ k in atTop, n ≤ k := eventually_ge_atTop n

 
theorem ev_pow_lt {r c : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, r ^ n < c :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually_lt_const hc

 
theorem ev_pow_rpow_lt {r θ c : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (r ^ n) ^ θ < c := by
  have h := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
  rw [Real.zero_rpow hθ.ne'] at h
  exact (h.comp (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)).eventually_lt_const hc

 
theorem ev_gauss_le {E b : ℝ} (hE : 0 < E) (hb : 0 < b) :
    ∀ᶠ y in atTop, 2 * Real.exp (-(y ^ 2) / (2 * E)) ≤ b := by
  have hsq : Tendsto (fun y : ℝ => y ^ 2 / (2 * E)) atTop atTop := by
    have : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have h2 : 0 < (2 * E)⁻¹ := inv_pos.2 (by linarith)
    simpa only [div_eq_mul_inv] using this.atTop_mul_const h2
  have hexp : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2 / (2 * E)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
  filter_upwards [hexp.eventually_lt_const (show (0 : ℝ) < b / 2 by linarith)] with y hy
  have e : -(y ^ 2) / (2 * E) = -(y ^ 2 / (2 * E)) := by ring
  rw [e]
  linarith

 
theorem exists_linear_le_two_pow {a c K : ℝ} (hK : 0 < K) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 21 * (((k : ℝ) + 3) * a + c) ≤ K * (2 : ℝ) ^ ((k : ℝ) / 4) := by
  set q : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hq0 : 0 < q := by linarith
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ ((k : ℝ) / 4) = q ^ k := by
    intro k
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / q ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 hq1
  have h2 : Tendsto (fun n : ℕ => 1 / q ^ n) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (q⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hq0.le) (inv_lt_one_of_one_lt₀ hq1)
    simpa only [one_div, inv_pow] using this
  have h3 : Tendsto (fun n : ℕ => 21 * |a| * ((n : ℝ) ^ 1 / q ^ n) +
      21 * |3 * a + c| * (1 / q ^ n)) atTop (𝓝 0) := by
    have := ((h1.const_mul (21 * |a|)).add (h2.const_mul (21 * |3 * a + c|)))
    simpa only [mul_zero, add_zero] using this
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h3.eventually_lt_const hK)
  refine ⟨k₀, fun k hk => ?_⟩
  have hb := hk₀ k hk
  have hqk : 0 < q ^ k := pow_pos hq0 k
  rw [hpow k]
  have e : 21 * |a| * ((k : ℝ) ^ 1 / q ^ k) + 21 * |3 * a + c| * (1 / q ^ k) =
      (21 * |a| * k + 21 * |3 * a + c|) / q ^ k := by
    field_simp
  rw [e, div_lt_iff₀ hqk] at hb
  have hlin : 21 * (((k : ℝ) + 3) * a + c) ≤ 21 * |a| * k + 21 * |3 * a + c| := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 : 21 * (((k : ℝ) + 3) * a + c) = 21 * (k * a) + 21 * (3 * a + c) := by ring
    rw [e1]
    have h4 : (k : ℝ) * a ≤ |a| * k := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self a) hk0
    have h5 : 3 * a + c ≤ |3 * a + c| := le_abs_self _
    linarith
  linarith

 

theorem ev_count {a c K : ℝ} (hK : 0 < K) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < x →
      21 * (((k : ℝ) + 3) * a + c) ≤ K * (2 : ℝ) ^ ((k : ℝ) / 4) := by
  obtain ⟨k₀, hk₀⟩ := exists_linear_le_two_pow (a := a) (c := c) hK
  filter_upwards [ev_le (show (0 : ℝ) < (1 / 2) ^ (k₀ + 1) by positivity)] with x hx k hk
  refine hk₀ k ?_
  by_contra hlt
  push Not at hlt
  have h1 : (1 / 2 : ℝ) ^ (k₀ + 1) ≤ (1 / 2 : ℝ) ^ (k + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
