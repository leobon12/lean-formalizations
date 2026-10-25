import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicArmSum

 



set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_point_costs_on_gaussian_good
    (ξ Q ζ L β T C Clam lam u : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hβ : 0 ≤ β) (hT : 1 ≤ T)
    (hC : 0 ≤ C) (hClam : 0 ≤ Clam) (hlam : 0 ≤ lam)
    (hfield : |u| ≤ (L + β * (k : ℝ)) / ξ) :
    let p₀ := (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ))
    let p₁ := (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))
    ENNReal.ofReal (2 * T ^ 2 * p₀ * Real.exp (ξ * u) * lam) ≤
      ENNReal.ofReal (2 * T ^ 2 * Real.exp L * p₁ * lam) ∧
    ENNReal.ofReal (C * T ^ 2 * p₀ * Real.exp (ξ * u) * lam) ≤
      ENNReal.ofReal (C * T ^ 2 * Real.exp L * p₁ * lam) ∧
    ENNReal.ofReal (Clam * T * lam * p₀ * Real.exp (ξ * u)) ≤
      ENNReal.ofReal (Clam * T ^ 2 * lam * Real.exp L * p₁) := by
  dsimp
  have hw := pt_dist_point_field_weighted_factor ξ Q ζ L β u k hξ hβ hfield
  have hT0 : 0 ≤ T := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 * T ^ 2)) hlam
    calc
      _ = (2 * T ^ 2) *
        ((2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * u)) *
          lam := by ring
      _ ≤ (2 * T ^ 2) *
        (Real.exp L * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))) *
          lam := h
      _ = _ := by ring
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C * T ^ 2)) hlam
    calc
      _ = (C * T ^ 2) *
        ((2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * u)) *
          lam := by ring
      _ ≤ (C * T ^ 2) *
        (Real.exp L * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))) *
          lam := h
      _ = _ := by ring
  · apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left hw
      (by positivity : 0 ≤ Clam * T * lam)
    calc
      _ = (Clam * T * lam) *
        ((2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * u)) :=
          by ring
      _ ≤ Clam * T * lam *
        (Real.exp L * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))) := h
      _ ≤ Clam * T ^ 2 * lam * Real.exp L *
        (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ)) := by
          have hm := mul_le_mul_of_nonneg_right hT2
            (by positivity : 0 ≤ Clam * lam * Real.exp L *
              (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ)))
          nlinarith

end SupercriticalLQGUniqueness.B2.DG20Pt
