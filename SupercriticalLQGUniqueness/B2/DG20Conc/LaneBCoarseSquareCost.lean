import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSourceIdxVisited
import LQGMetric.Papers.DDDF.S6P21Path

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneB_coarse_square_cost
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (Q : PsiParams) (ξ : ℝ) (K : ℕ) (ω : Ω)
    {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (M : ℝ)
    (hosc : ∀ b ∈ T20.coarseBlocks K γ, ∀ x ∈ T20D.hatBox K b,
      |psiMN Q W P 0 K x ω - phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M) :
    rectLen ξ (fun z => psiMN Q W P 0 K z ω) (rectAB 1 1) ≤
      ENNReal.ofReal
        (4 * (2 : ℝ)⁻¹ ^ K *
          ∑ b ∈ T20.coarseBlocks K γ,
            Real.exp (|ξ| * M) *
              Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) := by
  apply S6.rectLen_le_coarse hγ
  intro b hb x hx
  have h := hosc b hb x hx
  let d : ℝ := psiMN Q W P 0 K x ω - phiMN W P 0 K (T20.dyCenter K b) ω
  have hprod : ξ * d ≤ |ξ| * M := by
    calc
      ξ * d ≤ |ξ * d| := le_abs_self _
      _ = |ξ| * |d| := abs_mul _ _
      _ ≤ |ξ| * M := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  calc
    Real.exp (ξ * psiMN Q W P 0 K x ω) =
        Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω) *
          Real.exp (ξ * d) := by
      rw [← Real.exp_add]
      dsimp [d]
      congr 1
      ring
    _ ≤ Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω) *
          Real.exp (|ξ| * M) := by
      gcongr
    _ = Real.exp (|ξ| * M) *
          Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω) := mul_comm _ _

end SupercriticalLQGUniqueness.B2.DG20Conc
