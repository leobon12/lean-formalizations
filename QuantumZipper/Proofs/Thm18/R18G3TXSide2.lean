import QuantumZipper.Proofs.Thm18.R18G3TXSide
import QuantumZipper.Proofs.Thm18.R18G3TArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (R-b): the area input of scheme `B`

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 (near the Palm point the zoomed quantum
area of a fixed half-ball is `≥ 1` with probability `→ 1`). For scheme `B` (profile
`g3wCut γ η`, continuous) the shifted field is `h + g3wCut γ η` with `h = normField γ X₀`
area-good a.s. (`ae_isAreaGood_normField`); adding a continuous function keeps goodness
(`IsLQGGood.add_ofFun`) and multiplies the area measure by the positive density `e^{γ g}`
(`GoodSample.qAreaMeasure_add_ofFun`). The Palm/zoom part is `R18G3TArea`'s, which is stated
for every profile (`ae_g3pPalmLaw_of_ae_field`, `eventually_measureReal_zoomPalm_lt_g3p`).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LQGMeas LocalRule Factorization CoordsFull GoodSample

/-- Adding a continuous function keeps area-goodness. -/
theorem isAreaGood_add_ofFun {γ : ℝ} {x : FieldSample} (hx : IsAreaGood γ x) {φ : ℂ → ℝ}
    (hφ : Continuous φ) : IsAreaGood γ (x + ofFun φ) := by
  refine ⟨hx.1.add_ofFun hφ.continuousOn, fun V hV hVH hne => ?_⟩
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (γ * φ z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hφ.measurable))
  refine pos_iff_ne_zero.2 ?_
  rw [qAreaMeasure_add_ofFun hx.1 hφ.continuousOn, Ne, withDensity_apply_eq_zero hmeas]
  have hV' : {z : ℂ | ENNReal.ofReal (Real.exp (γ * φ z)) ≠ 0} ∩ V = V :=
    inter_eq_right.2 fun z _ => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [hV']
  exact (hx.2 V hV hVH hne).ne'

theorem ae_isAreaGood_g3pBField {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂gffBase.P, IsAreaGood γ (g3pField γ (g3wCut γ η) ω) :=
  (ae_isAreaGood_normField gffBase.gff hγ hγ2).mono fun _ h =>
    isAreaGood_add_ofFun h (contDiff_g3wCut γ η hη).continuous

end R18
end QuantumZipper
