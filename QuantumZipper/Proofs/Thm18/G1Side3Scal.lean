import QuantumZipper.Proofs.Thm18.G1Side3Dich
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (19): the area identity behind the scaling argument

For a good field `h`, a constant `C` and the canonical scale `λ = scaleParam γ (h + C)`, the area of
a set `λ⁻¹ D` for the recanonicalized field `canonical γ (h + C)` is `e^{γC}` times the area of
`D` for `h` (`qAreaMeasure_canonical_addConst_apply`): adding `C` multiplies the area measure by
`e^{γC}` (DS11 (5.1)), and the rescaling by `λ` moves area and domain together
(`GoodTransforms.qAreaMeasure_rescale`). With SLE scale invariance (`D(W(λ²·)/λ) = λ⁻¹ D(W)`) and
the law invariance of the wedge under add-constant-and-recanonicalize, this gives
`law(μ_h(D)) = law(e^{γC} μ_h(D))`, and `G1Side.ae_zero_or_top_of_scaleInv` then gives
`μ_h(D) ∈ {0, ∞}` (Sheffield, arXiv:1012.4797, §1.6). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuantumZipper
namespace G1Side

/-- **Area after adding a constant and recanonicalizing.** -/
theorem qAreaMeasure_canonical_addConst_apply {γ : ℝ} (hγ : 0 < γ) {h : FieldSample}
    (hh : IsLQGGood γ h) (C : ℝ) (hsp : 0 < scaleParam γ (addConst h C)) {E : Set ℂ}
    (hE : MeasurableSet E) :
    qAreaMeasure γ (canonical γ (addConst h C)) E =
      ENNReal.ofReal (Real.exp (γ * C)) *
        qAreaMeasure γ h ((fun z : ℂ => z / (scaleParam γ (addConst h C) : ℂ)) ⁻¹' E) := by
  have hmeas : Measurable fun z : ℂ => z / (scaleParam γ (addConst h C) : ℂ) :=
    measurable_id.div_const _
  unfold canonical
  rw [GoodTransforms.qAreaMeasure_rescale (hh.addConst C) hγ hsp, Measure.map_apply hmeas hE,
    GoodSample.qAreaMeasure_addConst hh C, Measure.smul_apply, smul_eq_mul]

end G1Side
end QuantumZipper
