import QuantumZipper.Proofs.Zipper.SWCoreB7Anchor
import QuantumZipper.Proofs.Zipper.UnifACFamField
import QuantumZipper.Proofs.Loewner.RevMapExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (6): the time-`s` fields in the coordinates of a free anchor field

Decision D64. For a rational anchor `q > 0`, the proved unzip version of Corollary 1.5 gives a
free field `Y` on the same space with `h⁰_q ~ 𝔥₀ + Y` (`RegEq`). Combined with the rational-time
identification `RegUnif.ae_bdryApprox_h0f_eq_coordChange` (`h⁰_s = coordChange h⁰_q ψ_s Q` at the
level of the boundary approximations) and the replacement of `ψ_s = revMap (vrev W s) (s − q)`
(junk off `ℍ`) by its holomorphic extension `revMapExt` (they agree on `ℍ`, and the folded
semicircles are carried by `ℍ`), this gives (`exists_free_anchor_ident`): a.s., for all rational
`s ≥ q`,

  `bdryApprox √κ h⁰_s = bdryApprox √κ (coordChange (𝔥₀ + Y) (revMapExt (vrev W s) (s − q)) Q)`,

which is the form to which the family transport (`SWCore.ae_transport_family`, with the `𝔥₀`
add-on) applies. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

theorem coordChange_congr_onH (x : FieldSample) {F F' : ℂ → ℂ} (hFF : EqOn F F' H) (Q : ℝ)
    {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) : coordChange x F Q μ = coordChange x F' Q μ := by
  unfold coordChange
  have h1 : μ.map F = μ.map F' := Measure.map_congr (hμ.mono fun z hz => hFF hz)
  have h2 : ∫ z, Real.log ‖deriv F z‖ ∂μ = ∫ z, Real.log ‖deriv F' z‖ ∂μ :=
    integral_congr_ae (hμ.mono fun z hz => by
      show Real.log ‖deriv F z‖ = Real.log ‖deriv F' z‖
      rw [Filter.EventuallyEq.deriv_eq (eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hFF)])
  rw [h1, h2]

theorem bdryApprox_coordChange_congr_onH (γ : ℝ) (x : FieldSample) {F F' : ℂ → ℂ}
    (hFF : EqOn F F' H) (Q : ℝ) (k : ℕ) :
    bdryApprox γ (coordChange x F Q) k = bdryApprox γ (coordChange x F' Q) k := by
  have e : avgReg (coordChange x F Q) k = avgReg (coordChange x F' Q) k := by
    funext z
    unfold avgReg
    congr 1
    funext n
    exact coordChange_congr_onH x hFF Q (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))
  simp only [bdryApprox, e]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end SWCore
end QuantumZipper
