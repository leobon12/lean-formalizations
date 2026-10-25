import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCoarseFineIndep
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1DistanceMoment

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneC_around_eq_coarse_exp_mul_weighted
    (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (b : ℤ × ℤ) (ω : Ω) :
    (lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z ω)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) =
    ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 K
      (T20.dyCenter K b) ω)) *
      laneCJ1WeightedAround Qψ ξ P W hW n K m b ω := by
  let t : ℝ := ξ * phiMN W P 0 K (T20.dyCenter K b) ω
  unfold laneCJ1WeightedAround
  have ht : -ξ * phiMN W P 0 K (T20.dyCenter K b) ω = -t := by
    dsimp [t]
    ring
  rw [ht]
  change _ = ENNReal.ofReal (Real.exp t) *
    (ENNReal.ofReal (Real.exp (-t)) * _)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  norm_num

theorem laneC_around_rpow_eq_coarse_exp_mul_weighted
    (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (b : ℤ × ℤ) (ω : Ω) (p : ℝ) (hp : 0 ≤ p) :
    ((lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z ω)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b)) ^ p =
    ENNReal.ofReal (Real.exp ((p * ξ) * phiMN W P 0 K
      (T20.dyCenter K b) ω)) *
      (laneCJ1WeightedAround Qψ ξ P W hW n K m b ω) ^ p := by
  rw [laneC_around_eq_coarse_exp_mul_weighted Qψ ξ P W hW n K m b ω,
    ENNReal.mul_rpow_of_nonneg _ _ hp,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp,
    ← Real.exp_mul]
  congr 2
  ring_nf

end SupercriticalLQGUniqueness.B2.DG20Conc
