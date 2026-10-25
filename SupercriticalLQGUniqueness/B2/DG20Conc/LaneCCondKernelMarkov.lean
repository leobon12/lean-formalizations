import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondMarkov
import Mathlib.Probability.Kernel.Condexp

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_conditional_event_markov_of_kernel
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ)
    {E : Set Ω} (hE : @MeasurableSet Ω mΩ E)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (haTop : a ≠ ⊤) :
    P {ω | a < (condExpKernel P m ω) E} ≤ P E / a := by
  let κ := condExpKernel P m
  have hq : Measurable[m] (fun ω => (κ ω) E) := Kernel.measurable_coe κ hE
  have hmean : ∫⁻ ω, (κ ω) E ∂P = P E := by
    calc
      ∫⁻ ω, (κ ω) E ∂P = ∫⁻ ω, (κ ω) E ∂(P.trim hm) :=
        (lintegral_trim hm hq).symm
      _ = (κ ∘ₘ P.trim hm) E := by
        exact (Measure.bind_apply hE (Kernel.aemeasurable κ)).symm
      _ = P E := by rw [show κ ∘ₘ P.trim hm = P from condExpKernel_comp_trim hm]
  exact laneC_conditional_event_markov_of_mean P (fun ω => (κ ω) E)
    (hq.mono hm le_rfl).aemeasurable hmean ha0 haTop

end SupercriticalLQGUniqueness.B2.DG20Conc
