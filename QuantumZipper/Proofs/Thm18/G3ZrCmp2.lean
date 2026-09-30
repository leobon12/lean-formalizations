import QuantumZipper.Proofs.Thm18.G3ZrWire
import QuantumZipper.Proofs.Thm18.G3ZrMain
import QuantumZipper.Proofs.Thm18.G3ZrDil2
import QuantumZipper.Proofs.Thm18.G1Side3Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (12): `CmpRegA` for the unscaled wedge, from the side package of the canonical wedge

For the unscaled field `W` with `b = scaleParam γ W > 0` and the canonical field
`rescale W Q b`, the side field of `W` at the target-dilated map `b Ψ` has the same raw
folded-circle values as the side field of `rescale W Q b` at `Ψ` (`raw_rescale_side`: the
dilated field is exact at pushed circles where `W` has a continuum limit after the dilation,
`evalReg_rescale_eq_of_contData`, and `log |(bΨ)'| = log b + log |Ψ'|`). So the side package of the
canonical wedge (core, area limit, continuum limits; supplied a.s. for a.e. path in `G3ZrRep`)
transfers to `W` at `b Ψ`, and **`cmpRegA_of_rep`** gives `CmpRegA` at every point `x` and every
dilation constant `c > 0` (via `choiceRegularA_translate`, `regShift_translate_shift`,
`dilRegCore_of_contData`, `dilReg_g1zLocMap`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Raw values of the side field of `W` at `b ψ` and of `rescale W Q b` at `ψ`.** -/
theorem raw_rescale_side {γ : ℝ} {W : FieldSample} (hW : IsRegularSample W) {b : ℝ} (hb : 0 < b)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0)
    (d : ℂ) {r : ℝ} (hr : 0 < r)
    (hint : Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hc : F1.ContData W ((foldedCircle d r).map fun u => (b : ℂ) * ψ u)) :
    coordChange W (fun u => (b : ℂ) * ψ u) (Qc γ) (foldedCircle d r) =
      coordChange (rescale W (Qc γ) b) ψ (Qc γ) (foldedCircle d r) := by
  have hmH : ∀ᵐ u ∂((foldedCircle d r).map ψ), u ∈ Hbar :=
    ae_map_mem_Hbar hψm ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw =>
      H_subset_Hbar (hψH hw))
  have hc' : F1.ContData W (((foldedCircle d r).map ψ).map fun u => (b : ℂ) * u) := by
    rw [Measure.map_map (measurable_const_mul _) hψm]; exact hc
  have hR := evalReg_rescale_eq_of_contData hW (Qc γ) hb hmH hc'
  have hlog : ∫ z, Real.log ‖deriv (fun u => (b : ℂ) * ψ u) z‖ ∂foldedCircle d r =
      Real.log b + ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r := by
    have hae : (fun z => Real.log ‖deriv (fun u => (b : ℂ) * ψ u) z‖) =ᵐ[foldedCircle d r]
        fun z => Real.log b + Real.log ‖deriv ψ z‖ :=
      (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => by
        simp only [deriv_const_mul_field, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hb]
        exact Real.log_mul hb.ne' (norm_ne_zero_iff.2 (hψ0 z hz))
    rw [integral_congr_ae hae, integral_add (integrable_const _) hint, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  unfold coordChange
  rw [hR]
  show evalReg W ((foldedCircle d r).map fun u => (b : ℂ) * ψ u) + _ =
    (evalReg W (((foldedCircle d r).map ψ).map fun u => (b : ℂ) * u) +
      Qc γ * ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂((foldedCircle d r).map ψ)) + _
  rw [Measure.map_map (measurable_const_mul _) hψm, RegClosure.integral_log_deriv_mul hb, hlog]
  simp only [Function.comp_def]
  ring

end G3Zr
end Thm18Asm
end QuantumZipper
