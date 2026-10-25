import Mathlib




 













set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventNumerics

theorem compare_inclusions {δ t : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hδt : δ < (21 / 20) * t) :
    2 * δ + (1 / 100) * t ≤ (11 / 5) * t ∧ (14 / 5) * t + (1 / 100) * t ≤ 3 * δ ∧
      δ / 4 + (1 / 100) * t < (3 / 10) * t ∧ (9 / 20) * t + (1 / 100) * t ≤ δ / 2 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem compare_power {q δ t : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδq : δ ≤ 1 / q) (ht : δ / q < t) :
    t ^ (-(1 : ℝ) / 8) ≤ δ ^ (-(1 : ℝ) / 4) := by
  have hq0 : 0 < q := by linarith
  have hdq : 0 < δ / q := div_pos hδ hq0
  have h1 : t ^ (-(1 : ℝ) / 8) ≤ (δ / q) ^ (-(1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_nonpos hdq ht.le (by norm_num)
  have h2 : (δ / q) ^ (-(1 : ℝ) / 8) = δ ^ (-(1 : ℝ) / 8) * q ^ ((1 : ℝ) / 8) := by
    rw [Real.div_rpow hδ.le hq0.le, div_eq_mul_inv, ← Real.rpow_neg hq0.le]
    congr 2; ring
  have h3 : q ≤ δ⁻¹ := by
    rw [le_inv_comm₀ hq0 hδ]; rw [one_div] at hδq; exact hδq
  have h4 : q ^ ((1 : ℝ) / 8) ≤ δ ^ (-(1 : ℝ) / 8) := by
    rw [show (-(1 : ℝ) / 8) = -((1 : ℝ) / 8) by ring, Real.rpow_neg hδ.le, ← Real.inv_rpow hδ.le]
    exact Real.rpow_le_rpow hq0.le h3 (by norm_num)
  calc t ^ (-(1 : ℝ) / 8) ≤ (δ / q) ^ (-(1 : ℝ) / 8) := h1
    _ = δ ^ (-(1 : ℝ) / 8) * q ^ ((1 : ℝ) / 8) := h2
    _ ≤ δ ^ (-(1 : ℝ) / 8) * δ ^ (-(1 : ℝ) / 8) := by
        gcongr
    _ = δ ^ (-(1 : ℝ) / 4) := by
        rw [← Real.rpow_add hδ]; congr 1; ring

theorem narrow_exponent {ξ Q n : ℝ} (hξ : 0 < ξ) (hn : (8 * Q + 12) / 3 ≤ n) :
    let ζ := ξ / (4 * (1 + ξ))
    ζ * n + (n + 1) * ξ * Q + ξ * (2 + ζ) * n ≤ (n - 1) * (ξ * (Q + 3)) := by
  intro ζ
  have hζ : ζ * (1 + ξ) = ξ / 4 := by
    simp only [ζ]; field_simp
  have key : (n - 1) * (ξ * (Q + 3)) - (ζ * n + (n + 1) * ξ * Q + ξ * (2 + ζ) * n)
      = (3 / 4) * ξ * n - 2 * ξ * Q - 3 * ξ := by
    have : ζ * n + ξ * ζ * n = (ξ / 4) * n := by rw [← hζ]; ring
    nlinarith [this]
  have : 0 ≤ (3 / 4) * ξ * n - 2 * ξ * Q - 3 * ξ := by nlinarith
  linarith

theorem gauss_exponent {ζ : ℝ} (hζ : 0 ≤ ζ) : 2 + ζ ≤ (2 + ζ) ^ 2 / (2 * (1 + ζ / 8)) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem grid_neighbour {ρ : ℝ} (hρ : 0 < ρ) :
    ρ < 6 / 5 * ρ ∧ 6 / 5 * ρ * Real.sqrt 2 < 2 * ρ ∧ Real.sqrt 2 / 2 * (6 / 5 * ρ) < ρ := by
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : Real.sqrt 2 < 5 / 3 := by linarith
  refine ⟨by linarith, by nlinarith, by nlinarith⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventNumerics

