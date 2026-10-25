import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLogRate
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTailMoment

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_exp_moment_of_half_log_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : AEMeasurable X P)
    {l N C c a xMin : ℝ} (hl : 0 < l) (hN : 0 ≤ N)
    (hC : 0 < C) (hc : 0 < c) (ha : 0 < a)
    (hMin : 2 ≤ xMin)
    (htail : ∀ t, xMin < t → P {ω | t ≤ X ω} ≤
      ENNReal.ofReal (N * C * Real.exp
        (-(c * (t / 2) ^ 2 / (a * Real.log (t / 2)))))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X ω)) ∂P ≤
      ENNReal.ofReal (Real.exp
        (l * max xMin (LQGMetric.DDDF.T20B.tailX0 l N C (c / (4 * a)))) + 1) := by
  have hc' : 0 < c / (4 * a) := div_pos hc (by positivity)
  apply laneC_lintegral_exp_le_of_tail_logsq_above hX0 hXm hl hN hC hc' (by linarith)
  intro t ht
  have hbound : P {ω | t ≤ X ω} ≤
      ENNReal.ofReal (N * C * Real.exp
        (-((c / (4 * a)) * t ^ 2 / Real.log t))) := by
    calc
    P {ω | t ≤ X ω} ≤
        ENNReal.ofReal (N * C * Real.exp
          (-(c * (t / 2) ^ 2 / (a * Real.log (t / 2))))) := htail t ht
    _ ≤ ENNReal.ofReal (N * C * Real.exp
        (-((c / (4 * a)) * t ^ 2 / Real.log t))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (laneC_half_logsq_rate_le ha hc (hMin.trans_lt ht))
        (mul_nonneg hN hC.le)
  simpa only [neg_mul, neg_div] using hbound

end SupercriticalLQGUniqueness.B2.DG20Conc
