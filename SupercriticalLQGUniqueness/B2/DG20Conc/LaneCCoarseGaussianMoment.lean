import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxCondAll
import LQGMetric.Papers.DDDF.P18Straight
import LQGMetric.Papers.DDDF.L9Tail

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneC_coarse_phi_exp_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (K : ℕ) (b : ℤ × ℤ) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (a * phiMN W P 0 K (T20.dyCenter K b) ω)) ∂P ≤
        ENNReal.ofReal
          (Real.exp (((K : ℝ) * Real.log 2) * a ^ 2 / 2)) := by
  obtain ⟨v, hv, hX⟩ := hasLaw_phiMN hW K (T20.dyCenter K b)
  have hV : 0 ≤ (K : ℝ) * Real.log 2 := by positivity
  have hv' : (v : ℝ) ≤ (Real.sqrt ((K : ℝ) * Real.log 2)) ^ 2 := by
    rw [Real.sq_sqrt hV]
    exact hv.le
  convert lintegral_exp_gauss_le hX hv' a using 1
  rw [Real.sq_sqrt hV]

end SupercriticalLQGUniqueness.B2.DG20Conc
