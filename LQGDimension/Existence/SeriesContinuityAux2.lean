import LQGDimension.Blueprint.Existence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometry and numerics for `GaussianSeriesLocallyUnifCont`

* `coord : ℝ × ℂ → (Fin 3 → ℝ)`, `(ε, z) ↦ (ε, re z, im z)`, compared with the sup norm of
  `ℝ × ℂ`: `‖coord s - coord t‖ ≤ ‖s - t‖ ≤ 2 ‖coord s - coord t‖`, and `‖coord s‖ ≤ m + 1` on
  `box m`.
* The level-`k` scales `hk R k = R / 4^k`, the chaining bound `Mk`, the Gaussian scale `σk`, the
  deviation `sk` and the threshold `rk = 2 (Mk + sk)`; `rk → 0`, the tail exponent is
  `-7 (k + 1)`, and `64^{k+1} · 2 e^{-7(k+1)} ≤ 2^{-k}`.
-/

noncomputable section

open Filter Topology Set Real

namespace LQGDimension

namespace SeriesCont

/-! ### The parameter map -/

/-- Coordinates `(ε, re z, im z)` of `(ε, z) ∈ ℝ × ℂ`. -/
def coord (s : ℝ × ℂ) : Fin 3 → ℝ := ![s.1, s.2.re, s.2.im]

theorem norm_coord_sub_le (s t : ℝ × ℂ) : ‖coord s - coord t‖ ≤ ‖s - t‖ := by
  have h1 : ‖s.1 - t.1‖ ≤ ‖s - t‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖s.2 - t.2‖ ≤ ‖s - t‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  have h3 : |s.2.re - t.2.re| ≤ ‖s.2 - t.2‖ := by
    simpa using Complex.abs_re_le_norm (s.2 - t.2)
  have h4 : |s.2.im - t.2.im| ≤ ‖s.2 - t.2‖ := by
    simpa using Complex.abs_im_le_norm (s.2 - t.2)
  rw [Real.norm_eq_abs] at h1
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [coord] using h1
  · simpa [coord] using h3.trans h2
  · simpa [coord] using h4.trans h2

theorem norm_sub_le_two_mul_coord (s t : ℝ × ℂ) : ‖s - t‖ ≤ 2 * ‖coord s - coord t‖ := by
  have c0 : |s.1 - t.1| ≤ ‖coord s - coord t‖ := by
    simpa [coord] using norm_le_pi_norm (coord s - coord t) 0
  have c1 : |s.2.re - t.2.re| ≤ ‖coord s - coord t‖ := by
    simpa [coord] using norm_le_pi_norm (coord s - coord t) 1
  have c2 : |s.2.im - t.2.im| ≤ ‖coord s - coord t‖ := by
    simpa [coord] using norm_le_pi_norm (coord s - coord t) 2
  have hz : ‖s.2 - t.2‖ ≤ |s.2.re - t.2.re| + |s.2.im - t.2.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (s.2 - t.2)
  have hn : 0 ≤ ‖coord s - coord t‖ := norm_nonneg _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · show ‖s.1 - t.1‖ ≤ _
    rw [Real.norm_eq_abs]
    linarith
  · show ‖s.2 - t.2‖ ≤ _
    linarith

theorem norm_coord_le_of_mem_box {m : ℕ} {s : ℝ × ℂ} (hs : s ∈ Blueprint.Existence.box m) :
    ‖coord s‖ ≤ (m : ℝ) + 1 := by
  rw [Blueprint.Existence.box, Set.mem_prod, Set.mem_Icc, mem_closedBall_zero_iff] at hs
  obtain ⟨⟨hlo, hhi⟩, hz⟩ := hs
  have hpos : 0 < s.1 := lt_of_lt_of_le (by positivity) hlo
  have h0 : |s.1| ≤ (m : ℝ) + 1 := by rw [abs_of_pos hpos]; exact hhi
  have h1 : |s.2.re| ≤ (m : ℝ) + 1 := (Complex.abs_re_le_norm _).trans hz
  have h2 : |s.2.im| ≤ (m : ℝ) + 1 := (Complex.abs_im_le_norm _).trans hz
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i
  · simpa [coord] using h0
  · simpa [coord] using h1
  · simpa [coord] using h2

/-! ### Scales and thresholds -/

/-- The level-`k` scale `R / 4^k`. -/
def hk (R : ℝ) (k : ℕ) : ℝ := R / 4 ^ k

/-- The chaining bound at level `k` (cells of diameter `3 hk`, Lipschitz constant `√(2Λ)`). -/
def Mk (R Λ : ℝ) (k : ℕ) : ℝ :=
  20 * √5 * √(2 * Λ) * √((((3 : ℕ) : ℝ) + 1) * (3 * hk R k))

/-- The Gaussian scale at level `k`. -/
def σk (R Λ : ℝ) (k : ℕ) : ℝ := √(6 * Λ * hk R k)

/-- The deviation at level `k`. -/
def sk (R Λ : ℝ) (k : ℕ) : ℝ := π * √(6 * Λ * hk R k * (7 * ((k : ℝ) + 1) / 2))

/-- The threshold at level `k`. -/
def rk (R Λ : ℝ) (k : ℕ) : ℝ := 2 * (Mk R Λ k + sk R Λ k)

theorem hk_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < hk R k := by
  unfold hk; positivity

theorem σk_pos {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (k : ℕ) : 0 < σk R Λ k := by
  unfold σk
  have := hk_pos hR k
  positivity

theorem sk_nonneg (R Λ : ℝ) (k : ℕ) : 0 ≤ sk R Λ k := by
  unfold sk
  have := Real.pi_pos
  positivity

theorem sq_σk {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (k : ℕ) :
    σk R Λ k ^ 2 = 6 * Λ * hk R k := by
  unfold σk
  have := hk_pos hR k
  rw [Real.sq_sqrt (by positivity)]

theorem sq_sqrt_two_mul_le {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (k : ℕ) :
    √(2 * Λ) ^ 2 * (3 * hk R k) ≤ σk R Λ k ^ 2 := by
  rw [sq_σk hR hΛ k, Real.sq_sqrt (by positivity)]
  apply le_of_eq
  ring

theorem tail_exponent_eq {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (k : ℕ) :
    -2 * sk R Λ k ^ 2 / (π ^ 2 * σk R Λ k ^ 2) = -7 * ((k : ℝ) + 1) := by
  have hh := hk_pos hR k
  have hsk : sk R Λ k ^ 2 = π ^ 2 * (6 * Λ * hk R k * (7 * ((k : ℝ) + 1) / 2)) := by
    unfold sk
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsk, sq_σk hR hΛ k]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hΛ' : Λ ≠ 0 := hΛ.ne'
  have hh' : hk R k ≠ 0 := hh.ne'
  field_simp

theorem tendsto_hk (R : ℝ) : Tendsto (hk R) atTop (𝓝 0) := by
  unfold hk
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

theorem tendsto_hk_mul (R : ℝ) :
    Tendsto (fun k : ℕ => hk R k * ((k : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)).const_mul R
  have h2 := (h1.add (tendsto_hk R))
  rw [mul_zero, zero_add] at h2
  refine h2.congr fun k => ?_
  unfold hk
  have : (0 : ℝ) < 4 ^ k := by positivity
  field_simp

theorem tendsto_sqrt_of_tendsto_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun k => √(f k)) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp hf
  rw [Real.sqrt_zero] at h
  exact h

theorem tendsto_rk (R Λ : ℝ) : Tendsto (rk R Λ) atTop (𝓝 0) := by
  have hM : Tendsto (Mk R Λ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k => (((3 : ℕ) : ℝ) + 1) * (3 * hk R k)) atTop (𝓝 0) := by
      have := ((tendsto_hk R).const_mul 3).const_mul ((((3 : ℕ) : ℝ) + 1))
      rw [mul_zero, mul_zero] at this
      exact this
    have h := (tendsto_sqrt_of_tendsto_zero h0).const_mul (20 * √5 * √(2 * Λ))
    rw [mul_zero] at h
    exact h
  have hs : Tendsto (sk R Λ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => 6 * Λ * hk R k * (7 * ((k : ℝ) + 1) / 2)) atTop (𝓝 0) := by
      have := (tendsto_hk_mul R).const_mul (21 * Λ)
      rw [mul_zero] at this
      refine this.congr fun k => ?_
      ring
    have h := (tendsto_sqrt_of_tendsto_zero h0).const_mul π
    rw [mul_zero] at h
    exact h
  have h := (hM.add hs).const_mul 2
  rw [add_zero, mul_zero] at h
  exact h

theorem level_count_bound (k : ℕ) :
    ((4 : ℝ) ^ (k + 1)) ^ 3 * (2 * Real.exp (-7 * ((k : ℝ) + 1))) ≤ (1 / 2) ^ k := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h7 : (128 : ℝ) ≤ Real.exp 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 7
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have h128 : (128 : ℝ) ^ (k + 1) ≤ Real.exp (7 * ((k : ℝ) + 1)) := by
    calc (128 : ℝ) ^ (k + 1) ≤ (Real.exp 7) ^ (k + 1) :=
          pow_le_pow_left₀ (by norm_num) h7 _
      _ = Real.exp (7 * ((k : ℝ) + 1)) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have hexp : Real.exp (-7 * ((k : ℝ) + 1)) = (Real.exp (7 * ((k : ℝ) + 1)))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [hexp]
  have hpos : (0 : ℝ) < 128 ^ (k + 1) := by positivity
  calc ((4 : ℝ) ^ (k + 1)) ^ 3 * (2 * (Real.exp (7 * ((k : ℝ) + 1)))⁻¹)
      ≤ ((4 : ℝ) ^ (k + 1)) ^ 3 * (2 * ((128 : ℝ) ^ (k + 1))⁻¹) := by
        gcongr
    _ = (1 / 2) ^ k := by
        have e1 : ((4 : ℝ) ^ (k + 1)) ^ 3 = 64 ^ (k + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        have e2 : (128 : ℝ) ^ (k + 1) = 64 ^ (k + 1) * 2 ^ (k + 1) := by
          rw [← mul_pow]
          norm_num
        rw [e1, e2, pow_succ 2 k, one_div_pow]
        have : (0 : ℝ) < 64 ^ (k + 1) := by positivity
        have : (0 : ℝ) < 2 ^ k := by positivity
        field_simp

end SeriesCont

end LQGDimension
