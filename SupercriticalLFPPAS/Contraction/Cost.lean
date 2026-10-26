import Mathlib

/-! Deterministic cost estimate in the proof of Lemma 4.1. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS.Contraction

/-- The affine comparison constant in the contraction step. -/
def d4CostFactor (C K lam d₀ : ℝ) : ℝ :=
  (1 - lam) * max C K + (lam + 3 * d₀) * K

/-- The total cost of the good pieces, the old-comparison pieces, and the joins is bounded by
the factor from (4.1). The split is at `C = (1 + d₀)K`, where the coefficient of `G`
changes sign. -/
theorem d4_joining_cost_bound {C K lam d₀ ℓ G : ℝ}
    (hK : 0 ≤ K) (hlam' : lam ≤ 1)
    (hd₀ : 0 ≤ d₀) (hℓ : 0 ≤ ℓ)
    (hGℓ : G ≤ ℓ) (hGfrac : lam * ℓ ≤ G) :
    C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ ≤
      d4CostFactor C K lam d₀ * ℓ := by
  by_cases hlarge : (1 + d₀) * K ≤ C
  · have hKC : K ≤ C := by nlinarith [mul_nonneg hd₀ hK]
    have hcoeff : (1 + d₀) * K - C ≤ 0 := by linarith
    have hGterm : ((1 + d₀) * K - C) * G ≤
        ((1 + d₀) * K - C) * (lam * ℓ) :=
      mul_le_mul_of_nonpos_left hGfrac hcoeff
    have hcoeffBound : C + ((1 + d₀) * K - C) * lam + 2 * d₀ * K ≤
        (1 - lam) * C + (lam + 3 * d₀) * K := by
      have hidentity :
          ((1 - lam) * C + (lam + 3 * d₀) * K) -
            (C + ((1 + d₀) * K - C) * lam + 2 * d₀ * K) =
              d₀ * K * (1 - lam) := by ring
      have hnonneg : 0 ≤ d₀ * K * (1 - lam) :=
        mul_nonneg (mul_nonneg hd₀ hK) (by linarith [hlam'])
      linarith
    have hcost :
        C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ ≤
          (C + ((1 + d₀) * K - C) * lam + 2 * d₀ * K) * ℓ := by
      calc
        C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ =
            C * ℓ + ((1 + d₀) * K - C) * G + 2 * d₀ * K * ℓ := by ring
        _ ≤
            C * ℓ + ((1 + d₀) * K - C) * (lam * ℓ) + 2 * d₀ * K * ℓ := by
          gcongr
        _ = (C + ((1 + d₀) * K - C) * lam + 2 * d₀ * K) * ℓ := by ring
    have hmax : max C K = C := max_eq_left hKC
    rw [d4CostFactor, hmax]
    exact hcost.trans (mul_le_mul_of_nonneg_right hcoeffBound hℓ)
  · have hcoeff : 0 ≤ (1 + d₀) * K - C := by linarith
    have hGterm : ((1 + d₀) * K - C) * G ≤
        ((1 + d₀) * K - C) * ℓ :=
      mul_le_mul_of_nonneg_left hGℓ hcoeff
    have hcost :
        C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ ≤
          (1 + 3 * d₀) * K * ℓ := by
      have hrewrite :
          C * ℓ + ((1 + d₀) * K - C) * ℓ + 2 * d₀ * K * ℓ =
            (1 + 3 * d₀) * K * ℓ := by ring
      calc
        C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ =
            C * ℓ + ((1 + d₀) * K - C) * G + 2 * d₀ * K * ℓ := by ring
        _ ≤ C * ℓ + ((1 + d₀) * K - C) * ℓ + 2 * d₀ * K * ℓ := by
          gcongr
        _ = (1 + 3 * d₀) * K * ℓ := hrewrite
    by_cases hCK : C ≤ K
    · have hmax : max C K = K := max_eq_right hCK
      have hfactor : d4CostFactor C K lam d₀ = (1 + 3 * d₀) * K := by
        simp [d4CostFactor, hmax]
        ring
      rw [hfactor]
      exact hcost
    · have hKC : K ≤ C := le_of_not_ge hCK
      have hmax : max C K = C := max_eq_left hKC
      have hfactor : (1 + 3 * d₀) * K ≤ d4CostFactor C K lam d₀ := by
        rw [d4CostFactor, hmax]
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam') (sub_nonneg.mpr hKC)]
      exact hcost.trans (mul_le_mul_of_nonneg_right hfactor hℓ)

end SupercriticalLFPPAS.Contraction
