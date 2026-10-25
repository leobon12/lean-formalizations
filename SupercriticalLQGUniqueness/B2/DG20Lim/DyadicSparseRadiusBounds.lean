import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicGoodPoint

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem sparse_radius_bounds {K i : ℕ} (hi : i ∈ sparseDyadicIndices K) :
    1 / (2 : ℝ) ^ K ≤ (ratRad64 1 i : ℝ) ∧
      (ratRad64 1 i : ℝ) ≤ 1 / (2 : ℝ) ^ (K / 2) := by
  have hscale := sparseDyadicIndices_scale hi
  have hpowlo : (2 : ℝ) ^ (K / 2) ≤ (2 : ℝ) ^ (6 * i) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpowhi : (2 : ℝ) ^ (6 * i) ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hscale.2
  have hpK : 0 < (2 : ℝ) ^ K := by positivity
  have hpi : 0 < (2 : ℝ) ^ (6 * i) := by positivity
  have hpHalf : 0 < (2 : ℝ) ^ (K / 2) := by positivity
  rw [ratRad64_one_eq_dyadic]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  constructor
  · apply (div_le_div_iff₀ hpK hpi).mpr
    nlinarith
  · apply (div_le_div_iff₀ hpi hpHalf).mpr
    nlinarith

theorem tendsto_sparse_radius_upper_zero :
    Tendsto (fun K : ℕ => 2 / (2 : ℝ) ^ (K / 2)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun K : ℕ => ((1 / 2 : ℝ) ^ (K / 2))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have hmul := hpow.const_mul (2 : ℝ)
  simpa only [mul_zero, one_div_pow, mul_one_div] using hmul

end SupercriticalLQGUniqueness.B2.DG20Lim
