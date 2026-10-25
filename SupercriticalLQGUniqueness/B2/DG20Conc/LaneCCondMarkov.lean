import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_conditional_event_markov_of_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : Ω → ℝ≥0∞) (hq : AEMeasurable q P)
    {E : Set Ω} (hmean : ∫⁻ ω, q ω ∂P = P E)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (haTop : a ≠ ⊤) :
    P {ω | a < q ω} ≤ P E / a := by
  calc
    P {ω | a < q ω} ≤ P {ω | a ≤ q ω} :=
      measure_mono (fun ω hω => by
        change a < q ω at hω
        exact hω.le)
    _ ≤ (∫⁻ ω, q ω ∂P) / a :=
      meas_ge_le_lintegral_div hq ha0 haTop
    _ = P E / a := by rw [hmean]

end SupercriticalLQGUniqueness.B2.DG20Conc
