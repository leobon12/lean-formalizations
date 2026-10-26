import SupercriticalLFPPAS.Contraction.Cost
import SupercriticalLFPPAS.Contraction.CoveringArithmetic

/-! The final affine-cost estimate for Lemma 4.1. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS.Contraction

/-- Once the covering and joining construction has produced the displayed path cost, the
correct two-case algebra gives the bound in (4.1). -/
theorem d4_final_cost_bound {C K lam d₀ ℓ G L : ℝ}
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1)
    (hd₀ : 0 ≤ d₀) (hℓ : 0 ≤ ℓ) (hL : ℓ ≤ L)
    (hGℓ : G ≤ ℓ) (hGfrac : lam * ℓ ≤ G) :
    C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ ≤
      d4CostFactor C K lam d₀ * L := by
  have hfactor_nonneg : 0 ≤ d4CostFactor C K lam d₀ := by
    unfold d4CostFactor
    positivity
  calc
    C * (ℓ - G) + (1 + d₀) * K * G + 2 * d₀ * K * ℓ ≤
        d4CostFactor C K lam d₀ * ℓ :=
      d4_joining_cost_bound hK hlam' hd₀ hℓ hGℓ hGfrac
    _ ≤ d4CostFactor C K lam d₀ * L :=
      mul_le_mul_of_nonneg_left hL hfactor_nonneg

end SupercriticalLFPPAS.Contraction
