import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTailMoment

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem laneC_ae_finite_of_logsq_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ≥0∞) {scale xMin N C c : ℝ}
    (hN : 0 ≤ N) (hC : 0 < C) (hc : 0 < c)
    (htail : ∀ t, xMin < t →
      P {ω | ENNReal.ofReal (scale * Real.exp t) < Y ω} ≤
        ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t))) :
    ∀ᵐ ω ∂P, Y ω < ⊤ := by
  let E : Set Ω := {ω | Y ω = ⊤}
  have hE : P E = 0 := by
    apply le_antisymm ?_ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    let t : ℝ := max xMin (T20B.tailX0 1 N C c) +
      |Real.log (ε : ℝ)| + 1
    have htmin : xMin < t := by
      dsimp [t]
      linarith [le_max_left xMin (T20B.tailX0 1 N C c), abs_nonneg (Real.log (ε : ℝ))]
    have htcut : T20B.tailX0 1 N C c ≤ t := by
      dsimp [t]
      linarith [le_max_right xMin (T20B.tailX0 1 N C c), abs_nonneg (Real.log (ε : ℝ))]
    have ht0 : 0 < t := by
      have : 3 ≤ T20B.tailX0 1 N C c := le_max_left _ _
      linarith
    have hrate := T20B.tail_ineq (l := 1) (N := N) (C := C) (c := c)
      (by norm_num) hN hC hc htcut
    have hcost : N * C * Real.exp (-c * t ^ 2 / Real.log t) ≤
        Real.exp (-t) := by
      have hNC : N * C ≤ Real.exp (Real.log (N * C + 1)) := by
        rw [Real.exp_log (by positivity)]
        linarith
      calc
        N * C * Real.exp (-c * t ^ 2 / Real.log t)
            ≤ Real.exp (Real.log (N * C + 1)) *
                Real.exp (-c * t ^ 2 / Real.log t) :=
              mul_le_mul_of_nonneg_right hNC (Real.exp_pos _).le
        _ = Real.exp (Real.log (N * C + 1) - c * t ^ 2 / Real.log t) := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by
              have hrate' : Real.log (N * C + 1) + 2 * t ≤
                  c * t ^ 2 / Real.log t := by
                convert hrate using 1 <;> ring
              linarith)
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hsmall : Real.exp (-t) ≤ (ε : ℝ) := by
      rw [← Real.exp_log hεreal]
      apply Real.exp_le_exp.mpr
      dsimp [t]
      have htail0 : 0 ≤ max xMin (T20B.tailX0 1 N C c) :=
        (by norm_num : (0 : ℝ) ≤ 3).trans
          ((le_max_left _ _).trans (le_max_right _ _))
      linarith [neg_le_abs (Real.log (ε : ℝ))]
    have hsub : E ⊆ {ω | ENNReal.ofReal (scale * Real.exp t) < Y ω} := by
      intro ω hω
      change Y ω = ⊤ at hω
      change ENNReal.ofReal (scale * Real.exp t) < Y ω
      rw [hω]
      exact ENNReal.ofReal_lt_top
    have hle : P E ≤ ENNReal.ofReal (Real.exp (-t)) := by
      calc
        P E ≤ P {ω | ENNReal.ofReal (scale * Real.exp t) < Y ω} := measure_mono hsub
        _ ≤ ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t)) :=
          htail t htmin
        _ ≤ ENNReal.ofReal (Real.exp (-t)) := ENNReal.ofReal_le_ofReal hcost
    have hεle : ENNReal.ofReal (Real.exp (-t)) ≤ ε := by
      simpa using ENNReal.ofReal_le_ofReal hsmall
    simpa only [zero_add] using hle.trans hεle
  have hfin : ∀ᵐ ω ∂P, Y ω ≠ ⊤ := by
    apply ae_iff.mpr
    simpa only [not_ne_iff, E] using hE
  exact hfin.mono fun ω hω => lt_top_iff_ne_top.mpr hω

end SupercriticalLQGUniqueness.B2.DG20Conc
