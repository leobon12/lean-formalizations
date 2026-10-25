import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelMarkov
import Mathlib.Probability.Kernel.MeasurableIntegral

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_conditional_moment_markov_of_kernel
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (haTop : a ≠ ⊤) :
    P {ω | a < ∫⁻ x, f x ∂(condExpKernel P m ω)} ≤
      (∫⁻ x, f x ∂P) / a := by
  let κ := condExpKernel P m
  have hq : Measurable[m] fun ω => ∫⁻ x, f x ∂(κ ω) :=
    hf.lintegral_kernel
  have hmean : ∫⁻ ω, (∫⁻ x, f x ∂(κ ω)) ∂P =
      ∫⁻ x, f x ∂P := by
    calc
      ∫⁻ ω, (∫⁻ x, f x ∂(κ ω)) ∂P =
          ∫⁻ ω, (∫⁻ x, f x ∂(κ ω)) ∂(P.trim hm) :=
            (lintegral_trim hm hq).symm
      _ = ∫⁻ x, f x ∂(κ ∘ₘ P.trim hm) := by
            exact (Measure.lintegral_bind (Kernel.aemeasurable κ) hf.aemeasurable).symm
      _ = ∫⁻ x, f x ∂P := by
            rw [show κ ∘ₘ P.trim hm = P from condExpKernel_comp_trim hm]
  calc
    P {ω | a < ∫⁻ x, f x ∂(κ ω)}
        ≤ P {ω | a ≤ ∫⁻ x, f x ∂(κ ω)} :=
          measure_mono (by
            intro ω h
            change a < ∫⁻ x, f x ∂(κ ω) at h
            change a ≤ ∫⁻ x, f x ∂(κ ω)
            exact h.le)
    _ ≤ (∫⁻ ω, ∫⁻ x, f x ∂(κ ω) ∂P) / a :=
          meas_ge_le_lintegral_div
            (hq.mono hm le_rfl).aemeasurable ha0 haTop
    _ = (∫⁻ x, f x ∂P) / a := by rw [hmean]

end SupercriticalLQGUniqueness.B2.DG20Conc
