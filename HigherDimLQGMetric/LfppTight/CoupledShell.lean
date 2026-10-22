import HigherDimLQGMetric.LfppTight.CoupledHolderTail
import HigherDimLQGMetric.DGZ.Crossing

/-! The local shell comparison needed for nondegeneracy of coupled LFPP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_coupled_shell_lower {d : ℕ} (ξ c C L : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    {x : Rd d} {r₁ r₂ : ℝ} (hr : r₂ < r₁)
    (hC : |c| ≤ C) (hL : ∀ z ∈ closedBall x r₁, |Ψ z| ≤ L) :
    DGZ.lfppSetDist ξ H univ (sphere x r₂) (sphere x r₁) ≤
      Real.exp (|ξ| * (C + L)) *
        DGZ.lfppSetDist ξ (fun z => H z - c + Ψ z) univ
          (sphere x r₂) (sphere x r₁) := by
  apply DGZ.lfppSetDist_sphere_le_mul_of_exp_le hH
    ((hH.sub continuous_const).add hΨ) hr (Real.exp_pos _).le
  intro z hz
  apply HigherDimLFPP.exp_mul_le_exp_abs_mul
  have hdiff : H z - (H z - c + Ψ z) = c - Ψ z := by ring
  change |H z - (H z - c + Ψ z)| ≤ C + L
  rw [hdiff]
  calc
    |c - Ψ z| ≤ |c| + |Ψ z| := abs_sub _ _
    _ ≤ C + L := add_le_add hC (hL z hz.1)

end HigherDimLQGMetric
