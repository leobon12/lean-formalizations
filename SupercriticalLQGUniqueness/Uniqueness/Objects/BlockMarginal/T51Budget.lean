import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Core2




 











set_option autoImplicit false

noncomputable section

open Set Filter Topology Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

theorem eventually_two_quarter_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, 2 * (1 / 4 : ℝ) ^ m ≤ c := by
  have ht : Tendsto (fun m : ℕ => 2 * (1 / 4 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).const_mul 2
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with m hm
  exact hm.le

theorem eventually_E20 (R : ℝ) {θ lam : ℝ} (hθ : 0 < θ) (hlam : 0 < lam) :
    ∀ᶠ m : ℕ in atTop, (2 * R ^ 2 + 1) * (2 * (1 / 4 : ℝ) ^ m) ^ θ ≤ lam ^ 2 := by
  have hK : 0 < 2 * R ^ 2 + 1 := by positivity
  set ε : ℝ := lam ^ 2 / (2 * R ^ 2 + 1) with hεdef
  have hε : 0 < ε := div_pos (by positivity) hK
  have hη : 0 < ε ^ θ⁻¹ := Real.rpow_pos_of_pos hε _
  filter_upwards [eventually_two_quarter_le hη] with m hm
  have h0 : 0 ≤ 2 * (1 / 4 : ℝ) ^ m := by positivity
  have h1 : (2 * (1 / 4 : ℝ) ^ m) ^ θ ≤ (ε ^ θ⁻¹) ^ θ := Real.rpow_le_rpow h0 hm hθ.le
  rw [Real.rpow_inv_rpow hε.le hθ.ne'] at h1
  calc (2 * R ^ 2 + 1) * (2 * (1 / 4 : ℝ) ^ m) ^ θ ≤ (2 * R ^ 2 + 1) * ε :=
        mul_le_mul_of_nonneg_left h1 hK.le
    _ = lam ^ 2 := by rw [hεdef]; field_simp

theorem pow_sixteen_eq_exp (n : ℕ) : (1 / 16 : ℝ) ^ n = Real.exp (-(n * Real.log 16)) := by
  rw [show -((n : ℝ) * Real.log 16) = (n : ℝ) * (-Real.log 16) by ring, Real.exp_nat_mul,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

theorem union_term_le {lam c : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hc : 0 ≤ c) (m : ℕ) :
    ((8 * (2 * gridHalf (lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) *
        (c * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) ≤
      8 * (π + 1) * c / lam * (1 / 16 : ℝ) ^ m := by
  set A : ℝ := (1 / 16 : ℝ) ^ m with hAdef
  have hA : 0 < A := pow_pos (by norm_num) m
  have hA1 : A ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set δ : ℝ := lam * A with hδdef
  have hδ : 0 < δ := mul_pos hlam hA
  have hδ1 : δ ≤ 1 := by
    calc δ = lam * A := rfl
      _ ≤ 1 * 1 := mul_le_mul hlam1 hA1 hA.le zero_le_one
      _ = 1 := one_mul 1
  have hEA : Objects.Density.endptScale m = A := rfl
  have hJ : (gridHalf (lam * Objects.Density.endptScale m) : ℝ) ≤ π / 2 / δ := by
    rw [hEA]
    exact Nat.floor_le (by positivity)
  have hcount : ((8 * (2 * gridHalf (lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) ≤
      8 * (π + 1) / δ := by
    push_cast
    have h1 : 2 * (gridHalf (lam * Objects.Density.endptScale m) : ℝ) + 1 ≤ π / δ + 1 := by
      have : 2 * (π / 2 / δ) = π / δ := by ring
      linarith
    have h2 : π / δ + 1 ≤ (π + 1) / δ := by
      rw [add_div]
      have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
      linarith
    have h3 : 8 * (π + 1) / δ = 8 * ((π + 1) / δ) := by ring
    rw [h3]
    linarith
  have hexp : Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ)) ≤ A ^ 2 := by
    rw [hAdef, ← pow_mul, pow_sixteen_eq_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
    nlinarith
  calc ((8 * (2 * gridHalf (lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) *
        (c * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ)))
      ≤ 8 * (π + 1) / δ * (c * A ^ 2) := by
        apply mul_le_mul hcount (mul_le_mul_of_nonneg_left hexp hc)
          (mul_nonneg hc (Real.exp_pos _).le) (by positivity)
    _ = 8 * (π + 1) * c / lam * A := by
        rw [hδdef]
        field_simp

theorem eventually_union_budget {lam c ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ((8 * (2 * gridHalf (lam * Objects.Density.endptScale m) + 1) : ℕ) : ℝ) *
        (c * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) ≤ ε := by
  have ht : Tendsto (fun m : ℕ => 8 * (π + 1) * c / lam * (1 / 16 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (8 * (π + 1) * c / lam)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm
  exact (union_term_le hlam hlam1 hc m).trans hm.le

theorem ofReal_div_chain (p : ℝ) (N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal p / 4 / 2 / N / 2 = ENNReal.ofReal (p / (16 * N)) := by
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := (ENNReal.ofReal_ofNat 4).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  have hN' : (N : ℝ≥0∞) = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [h4, ← ENNReal.ofReal_div_of_pos (by norm_num), h2,
    ← ENNReal.ofReal_div_of_pos (by norm_num), hN', ← ENNReal.ofReal_div_of_pos hNpos,
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  field_simp
  ring

theorem ofReal_div_eight (p : ℝ) : ENNReal.ofReal p / 4 / 2 = ENNReal.ofReal (p / 8) := by
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := (ENNReal.ofReal_ofNat 4).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  rw [h4, ← ENNReal.ofReal_div_of_pos (by norm_num), h2, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
