import QuantumZipper.Proofs.Thm18.G1RegRepMeas

/-!
# G1-REGREP, part 5: the random rescaling inside `canonical` (RC2)

`wedgeRep γ X A = canonical γ w₀ = rescale w₀ Q s` with `w₀ = wedgeField (lateralPart X) A Q`
and the random scale `s = scaleParam γ w₀`. Pulling back by a fixed `ψ`, the raw values of
`coordChange (rescale w₀ Q s) ψ Q` at a probability measure `μ` agree with those of
`coordChange w₀ (s ψ) Q` as soon as the regularization of `w₀` is **scale consistent** at
`ψ_* μ` (`ScaleConsistentAt`, G1Rescale.lean) and `log |ψ'|` is integrable with `ψ' ≠ 0` a.e.
(`coordChange_rescale_apply`). Since RC2 only reads the raw values at the folded dyadic circles,
RC2 for the canonical representative pulled back by `ψ` is equivalent to RC2 for the unscaled
field pulled back by `s ψ` (`isRegularSample_coordChange_rescale_iff`), given scale consistency
at the countably many measures `ψ_* fc(d, 2^{-k})`.

Scale consistency at a fixed measure for **all** `s > 0` at once follows from a continuum limit
of the circle smoothing (`G1.scaleConsistentAt_of_continuum`, G1Pair.lean); that continuum limit
for `w₀` is a remaining probabilistic input (see the report of G1-REGREP).

Own elementary argument (chain rule for the dilation).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Meas

theorem integral_log_deriv_const_mul {ψ : ℂ → ℂ} {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (hd : ∀ᵐ z ∂μ, deriv ψ z ≠ 0)
    (hi : Integrable (fun z => Real.log ‖deriv ψ z‖) μ) :
    ∫ z, Real.log ‖deriv (fun z => (s : ℂ) * ψ z) z‖ ∂μ =
      Real.log s + ∫ z, Real.log ‖deriv ψ z‖ ∂μ := by
  have e : (fun z => Real.log ‖deriv (fun z => (s : ℂ) * ψ z) z‖) =ᵐ[μ]
      fun z => Real.log s + Real.log ‖deriv ψ z‖ := by
    filter_upwards [hd] with z hz
    rw [deriv_const_mul_field', norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le,
      Real.log_mul hs.ne' (norm_ne_zero_iff.2 hz)]
  rw [integral_congr_ae e, integral_add (integrable_const _) hi, integral_const, probReal_univ,
    one_smul]

/-- **Raw values of the pulled-back canonical field** at a probability measure. -/
theorem coordChange_rescale_apply (w₀ : FieldSample) {ψ : ℂ → ℂ} (hψ : Measurable ψ) (Q : ℝ)
    {s : ℝ} (hs : 0 < s) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hsc : G1.ScaleConsistentAt w₀ Q s (μ.map ψ)) (hd : ∀ᵐ z ∂μ, deriv ψ z ≠ 0)
    (hi : Integrable (fun z => Real.log ‖deriv ψ z‖) μ) :
    coordChange (rescale w₀ Q s) ψ Q μ = coordChange w₀ (fun z => (s : ℂ) * ψ z) Q μ := by
  unfold coordChange
  unfold G1.ScaleConsistentAt at hsc
  rw [hsc, Measure.map_map (measurable_const_mul _) hψ, integral_log_deriv_const_mul hs hd hi]
  have h1 : (μ.map ψ).real univ = 1 := by
    rw [measureReal_def, Measure.map_apply hψ MeasurableSet.univ, preimage_univ, measure_univ,
      ENNReal.toReal_one]
  rw [h1]
  show _ = evalReg w₀ (μ.map ((fun z : ℂ => (s : ℂ) * z) ∘ ψ)) + _
  ring

end G1Meas
end Thm18Asm
end QuantumZipper
