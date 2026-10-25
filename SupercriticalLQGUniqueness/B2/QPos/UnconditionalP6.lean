import SupercriticalLQGUniqueness.B2.QPos.MedianWindowAdapter
import SupercriticalLQGUniqueness.B2.QPos.UpperPowerWindow
import SupercriticalLQGUniqueness.B2.QPos.QuantileUpperWindow

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem upper_annulus_power_window_proved
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      P {ω | (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal ≤
        (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε) * (n : ℝ))})
      atTop (𝓝 1) :=
  upper_annulus_power_window whiteNoiseMedianPowerWindow_proved hW ξ Q hQ hε

 

theorem upper_annulus_quantile_window_proved
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {p ε : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      P {ω | (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) *
          LambdaN (ξ : ℝ) W P n (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P n (ENNReal.ofReal p) <
        (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal})
      atTop (𝓝 0) :=
  upper_annulus_quantile_window whiteNoiseMedianPowerWindow_proved
    hW ξ Q hQ hp hph hε

end SupercriticalLQGUniqueness.B2.QPos
