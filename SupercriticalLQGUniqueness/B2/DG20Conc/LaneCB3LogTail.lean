import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

 

theorem laneC_negative_log_tail_of_B3_tail
    {L : Ω → ℝ} (hL : ∀ ω, 0 < L ω)
    {scale Tmin N C c a : ℝ} (hscale : 0 < scale)
    (htail : ∀ T, Tmin < T →
      P {ω | L ω < T⁻¹ * scale} ≤
        ENNReal.ofReal (N * C * Real.exp
          (-c * (Real.log T) ^ 2 / (a * Real.log (Real.log T)))))
    {t : ℝ} (ht : 0 < t) (hT : Tmin < Real.exp (t / 2)) :
    P {ω | t ≤ Real.log (max 1 (scale / L ω))} ≤
      ENNReal.ofReal (N * C * Real.exp
        (-c * (t / 2) ^ 2 / (a * Real.log (t / 2)))) := by
  have hsub : {ω | t ≤ Real.log (max 1 (scale / L ω))} ⊆
      {ω | L ω < (Real.exp (t / 2))⁻¹ * scale} := by
    intro ω hω
    have hmaxpos : 0 < max 1 (scale / L ω) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hexp : Real.exp t ≤ max 1 (scale / L ω) := by
      rw [← Real.exp_log hmaxpos]
      exact Real.exp_le_exp.mpr hω
    have hmaxgt : 1 < max 1 (scale / L ω) :=
      (Real.one_lt_exp_iff.mpr ht).trans_le hexp
    have hratio : 1 ≤ scale / L ω := by
      rcases le_total (scale / L ω) 1 with h | h
      · simp only [max_eq_left h] at hmaxgt
        exact False.elim (lt_irrefl _ hmaxgt)
      · exact h
    rw [max_eq_right hratio] at hexp
    have hfirst : L ω ≤ scale * Real.exp (-t) := by
      have hmul : Real.exp t * L ω ≤ scale :=
        (le_div_iff₀ (hL ω)).mp hexp
      calc
        L ω = L ω * (Real.exp t * Real.exp (-t)) := by
          rw [← Real.exp_add]
          simp
        _ = (Real.exp t * L ω) * Real.exp (-t) := by ring
        _ ≤ scale * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos (-t)).le
    have hsecond : scale * Real.exp (-t) < scale * Real.exp (-(t / 2)) := by
      apply mul_lt_mul_of_pos_left _ hscale
      apply Real.exp_lt_exp.mpr
      linarith
    have htarget := hfirst.trans_lt hsecond
    change L ω < (Real.exp (t / 2))⁻¹ * scale
    simpa only [Real.exp_neg, mul_comm] using htarget
  exact (measure_mono hsub).trans (by
    simpa only [Real.log_exp] using htail (Real.exp (t / 2)) hT)

end SupercriticalLQGUniqueness.B2.DG20Conc
