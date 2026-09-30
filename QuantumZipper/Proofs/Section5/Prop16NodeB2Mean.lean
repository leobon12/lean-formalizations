import QuantumZipper.Proofs.Section5.Prop16NodeB2Law
import QuantumZipper.Proofs.Section5.Prop16NodeB2Reg

/-!
# Proposition 1.6, Palm node B′: the mean boundary measure on a window has density `ρ`

`palm_formula_prop16_window_mean`: the window Palm formula of `Prop16NodeB2Reg.lean` together with
the identification of the mean measure `palmMean` (the unnormalized Palm point law of
`Prop16NodeB2Law.lean`) on the window:
`∫_{(a',b')} f d(E ν) = ∫_{(a',b')} exp(γ h0(x)/2 + γ² k(x,x)/8) f(x) dx`,
the case `G((y, x)) = f(x)` of the Palm formula. Hence the right side of the window Palm formula
can be written against `palmMean`, the form used by `Prop16PalmWinMaskStmt`.

Source: Duplantier–Sheffield, arXiv:0808.1560, §3.3 (p. 22) (the Palm formula with a test function
of the point only gives the intensity). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

theorem setLIntegral_palmMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Ω → Measure ℝ} {a b a' b' : ℝ} (hν : AEMeasurable ν P) (ha : a ≤ a') (hb : b' ≤ b)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioo a' b', f x ∂palmMean P ν a b = ∫⁻ ω, ∫⁻ x in Ioo a' b', f x ∂(ν ω) ∂P := by
  rw [← lintegral_indicator measurableSet_Ioo, palmMean,
    Measure.lintegral_bind (aemeasurable_restrict_of_aemeasurable hν measurableSet_Ioo)
      (hf.indicator measurableSet_Ioo).aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 (Ioo_subset_Ioo ha hb)]

end Prop16Asm

end QuantumZipper
