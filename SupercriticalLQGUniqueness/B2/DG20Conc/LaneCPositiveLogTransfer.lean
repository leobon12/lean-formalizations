import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1ActualMoment

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_rpow_le_exp_positive_log
    {Y : ℝ≥0∞} (hY : Y ≠ ⊤) {A p : ℝ}
    (hA : 0 < A) (hp : 0 ≤ p) :
    Y ^ p ≤ ENNReal.ofReal (A ^ p) *
      ENNReal.ofReal (Real.exp
        (p * Real.log (max 1 (Y.toReal / A)))) := by
  let X := Real.log (max 1 (Y.toReal / A))
  have hZ : 0 < max 1 (Y.toReal / A) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdiv : Y.toReal / A ≤ max 1 (Y.toReal / A) := le_max_right _ _
  have hbase : Y.toReal ≤ A * max 1 (Y.toReal / A) := by
    simpa only [mul_comm] using (div_le_iff₀ hA).mp hdiv
  have hbound : Y.toReal ≤ A * Real.exp X := by
    simpa only [X, Real.exp_log hZ] using hbase
  have hpow : Y.toReal ^ p ≤ A ^ p * Real.exp (p * X) := by
    calc
      Y.toReal ^ p ≤ (A * Real.exp X) ^ p :=
        Real.rpow_le_rpow ENNReal.toReal_nonneg hbound hp
      _ = A ^ p * Real.exp (p * X) := by
        rw [Real.mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul]
        rw [mul_comm X p]
  have hYpow : Y ^ p = ENNReal.ofReal (Y.toReal ^ p) := by
    calc
      Y ^ p = (ENNReal.ofReal Y.toReal) ^ p := by rw [ENNReal.ofReal_toReal hY]
      _ = ENNReal.ofReal (Y.toReal ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp
  rw [hYpow, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]
  exact ENNReal.ofReal_le_ofReal hpow

 

theorem laneC_lintegral_rpow_le_exp_positive_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Y : Ω → ℝ≥0∞} (hY : ∀ᵐ ω ∂P, Y ω ≠ ⊤)
    {A p : ℝ} (hA : 0 < A) (hp : 0 ≤ p) :
    ∫⁻ ω, Y ω ^ p ∂P ≤
      ENNReal.ofReal (A ^ p) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          (p * Real.log (max 1 ((Y ω).toReal / A)))) ∂P := by
  have hpoint : ∀ᵐ ω ∂P,
      Y ω ^ p ≤ ENNReal.ofReal (A ^ p) *
        ENNReal.ofReal (Real.exp
          (p * Real.log (max 1 ((Y ω).toReal / A)))) := by
    filter_upwards [hY] with ω hω
    exact laneC_rpow_le_exp_positive_log hω hA hp
  calc
    ∫⁻ ω, Y ω ^ p ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (A ^ p) *
            ENNReal.ofReal (Real.exp
              (p * Real.log (max 1 ((Y ω).toReal / A)))) ∂P :=
          lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (A ^ p) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp
            (p * Real.log (max 1 ((Y ω).toReal / A)))) ∂P := by
          exact lintegral_const_mul' _ _
            (ENNReal.ofReal_ne_top)

end SupercriticalLQGUniqueness.B2.DG20Conc
