import LQGMetric.Papers.DDDF.T20BMom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

 


theorem laneC_lintegral_exp_le_of_tail_logsq_above
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : AEMeasurable X P)
    {l N C c xMin : ℝ} (hl : 0 < l) (hN : 0 ≤ N)
    (hC : 0 < C) (hc : 0 < c) (hMin : 0 ≤ xMin)
    (htail : ∀ t, xMin < t → P {ω | t ≤ X ω} ≤
      ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X ω)) ∂P ≤
      ENNReal.ofReal
        (Real.exp (l * max xMin (T20B.tailX0 l N C c)) + 1) := by
  let x₀ := max xMin (T20B.tailX0 l N C c)
  have hx₀ : 0 ≤ x₀ := hMin.trans (le_max_left _ _)
  have hx3 : 3 ≤ x₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h := lintegral_exp_le_of_tail (P := P) hX0 hXm
    (x₀ := x₀) (B := 1) (κ := 1) hl hx₀ one_pos zero_le_one
    (fun t ht => by
      have hMinT : xMin < t := (le_max_left _ _).trans_lt ht
      have hCut : T20B.tailX0 l N C c ≤ t :=
        (le_max_right _ _).trans ht.le
      have hP : P.real {ω | t ≤ X ω} ≤
          N * C * Real.exp (-c * t ^ 2 / Real.log t) := by
        have hP' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail t hMinT)
        rwa [ENNReal.toReal_ofReal (by positivity)] at hP'
      have hkey := T20B.tail_ineq hl hN hC hc hCut
      have hlNC : l * N * C ≤ Real.exp (Real.log (l * N * C + 1)) := by
        rw [Real.exp_log (by positivity)]
        linarith
      calc l * Real.exp (l * t) * P.real {ω | t ≤ X ω}
          ≤ l * Real.exp (l * t) *
              (N * C * Real.exp (-c * t ^ 2 / Real.log t)) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
        _ = (l * N * C) * Real.exp (l * t + -c * t ^ 2 / Real.log t) := by
            rw [Real.exp_add]
            ring
        _ ≤ Real.exp (Real.log (l * N * C + 1)) *
              Real.exp (l * t + -c * t ^ 2 / Real.log t) :=
            mul_le_mul_of_nonneg_right hlNC (Real.exp_pos _).le
        _ = Real.exp (Real.log (l * N * C + 1) +
              (l * t + -c * t ^ 2 / Real.log t)) :=
            (Real.exp_add _ _).symm
        _ ≤ 1 * Real.exp (-1 * t) := by
            rw [one_mul]
            refine Real.exp_le_exp.2 ?_
            have e : -c * t ^ 2 / Real.log t =
                -(c * t ^ 2 / Real.log t) := by ring
            rw [e]
            linarith)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsmall : Real.exp (-1 * x₀) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  dsimp only [x₀]
  simpa only [one_mul, div_one] using
    (add_le_add_right hsmall (Real.exp (l * max xMin (T20B.tailX0 l N C c))))

end SupercriticalLQGUniqueness.B2.DG20Conc
