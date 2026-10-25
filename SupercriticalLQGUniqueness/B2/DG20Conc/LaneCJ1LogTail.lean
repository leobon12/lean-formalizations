import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3LogTail

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

theorem laneC_positive_log_tail_of_J1_tail
    {Y : Ω → ℝ} {scale Tmin N C c a : ℝ} (hscale : 0 < scale)
    (htail : ∀ T, Tmin < T →
      P {ω | T * scale < Y ω} ≤
        ENNReal.ofReal (N * C * Real.exp
          (-c * (Real.log T) ^ 2 / (a * Real.log (Real.log T)))))
    {t : ℝ} (ht : 0 < t) (hT : Tmin < Real.exp (t / 2)) :
    P {ω | t ≤ Real.log (max 1 (Y ω / scale))} ≤
      ENNReal.ofReal (N * C * Real.exp
        (-c * (t / 2) ^ 2 / (a * Real.log (t / 2)))) := by
  have hsub : {ω | t ≤ Real.log (max 1 (Y ω / scale))} ⊆
      {ω | Real.exp (t / 2) * scale < Y ω} := by
    intro ω hω
    have hmaxpos : 0 < max 1 (Y ω / scale) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hexp : Real.exp t ≤ max 1 (Y ω / scale) := by
      rw [← Real.exp_log hmaxpos]
      exact Real.exp_le_exp.mpr hω
    have hmaxgt : 1 < max 1 (Y ω / scale) :=
      (Real.one_lt_exp_iff.mpr ht).trans_le hexp
    have hratio : 1 ≤ Y ω / scale := by
      rcases le_total (Y ω / scale) 1 with h | h
      · simp only [max_eq_left h] at hmaxgt
        exact False.elim (lt_irrefl _ hmaxgt)
      · exact h
    rw [max_eq_right hratio] at hexp
    have hfirst : scale * Real.exp t ≤ Y ω := by
      simpa only [mul_comm] using (le_div_iff₀ hscale).mp hexp
    have hsecond : scale * Real.exp (t / 2) < scale * Real.exp t := by
      apply mul_lt_mul_of_pos_left _ hscale
      apply Real.exp_lt_exp.mpr
      linarith
    change Real.exp (t / 2) * scale < Y ω
    nlinarith [hfirst, hsecond]
  exact (measure_mono hsub).trans (by
    simpa only [Real.log_exp] using htail (Real.exp (t / 2)) hT)

end SupercriticalLQGUniqueness.B2.DG20Conc
