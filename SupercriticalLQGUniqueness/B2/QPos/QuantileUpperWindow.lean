import SupercriticalLQGUniqueness.B2.QPos.MedianRatio
import SupercriticalLQGUniqueness.B2.QPos.ProbabilityComplement

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem upper_annulus_quantile_window
    (hmedian : Inputs.WhiteNoiseMedianPowerWindow)
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
      atTop (𝓝 0) := by
  let _ := hW.isProbabilityMeasure
  have he6 : 0 < ε / 6 := by positivity
  have he12 : 0 < ε / 12 := by positivity
  have hgood := upper_annulus_power_window hmedian hW ξ Q hQ he6
  have hφmeas : ∀ n : ℕ, Measurable (fun ω =>
      (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal) := by
    intro n
    have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    exact (measurable_crossLenIn upperAnnulus_isCompact hφ.cont hφ.meas).ennreal_toReal
  have hsmall := upper_tail_zero_of_lower_event_one P
    (fun n ω => (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x ω)
      upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal)
    hφmeas (fun n => (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε / 6) * (n : ℝ))) hgood
  have hmed := hmedian ξ Q hQ P W hW (ε / 12) he12
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε / 6) * (n : ℝ)) ≤
        (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) *
          LambdaN (ξ : ℝ) W P n (ENNReal.ofReal p) *
          ellN (ξ : ℝ) W P n (ENNReal.ofReal p) := by
    filter_upwards [hmed] with n hn
    have hpow : (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ε / 6) * (n : ℝ)) ≤
        (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) *
          (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ε / 12) * (n : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith only [mul_nonneg hε.le (Nat.cast_nonneg n)]
    have hratio := median_le_quantile_product hW (ξ : ℝ) hp hph n
    calc
      _ ≤ (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) *
          (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ε / 12) * (n : ℝ)) := hpow
      _ ≤ (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) * lambdaN (ξ : ℝ) W P n :=
        mul_le_mul_of_nonneg_left hn.1 (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hratio
            (show 0 ≤ (2 : ℝ) ^ ((ε / 3) * (n : ℝ)) by positivity))
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hsmall
    (Filter.Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hthreshold] with n hn
  apply measure_mono
  intro ω hω
  exact lt_of_le_of_lt hn hω

end SupercriticalLQGUniqueness.B2.QPos
