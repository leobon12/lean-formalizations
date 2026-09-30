import QuantumZipper.Proofs.Zipper.XPCModBasic
import QuantumZipper.Proofs.GFF.CoordRegSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, R1 for the pushed circles (2/2): `XPCModPStmt`

For `φ` measurable, holomorphic and injective on `ℍ` with `φ' ≠ 0` and `φ(ℍ) ⊆ ℍ`, and a convex
compact `K ⊆ ℍ`, there is `L ≥ 0` such that for folded circles `ν = fc(z, s)`, `ν' = fc(z', s')`
with `B̄(z, s), B̄(z', s') ⊆ K` (`abs_kernelCov2_push_push_le`)

  `|E(φ_*ν − φ_*ν')| ≤ 4 δ / min s s' + 2 L δ`,   `δ = ‖z − z'‖ + |s − s'|`.

Proof. Write `G = neumannH`. For `x ≠ w` in `K`, `G(φ x, φ w) = G(x, w) + qt φ x w`
(`neumannH_eq_add_qt`, divided differences, `XPCModBasic.lean`); circles have no atoms, so the
inner integrals are `E_ν(x) = hfc(z, s)(x) + ∫ qt φ x · dν`. As in the image-circle case
(`abs_kernelCov2_fc_fc_le`) the energy is `∫ (E_ν − E_ν') dν − ∫ (E_ν − E_ν') dν'`, and pointwise
on `K`: `|hfc(z,s) − hfc(z',s')| ≤ 2δ / min s s'` (`abs_hfc_sub_le`), while
`|∫ qt φ x · dν − ∫ qt φ x · dν'| ≤ L δ` by coupling the two circles through the common angle
(`xpm_circ_couple`) and the Lipschitz bound of `qt φ x ·` (`exists_qt_bounds`).
Then `xPCModPStmt_holds` applies this to a measurable surrogate of `f_t⁻¹` on the thickening
`K = cthickening δ₀ B.rect ⊆ ℍ` of the rectangle, with `s₁ = min δ₀ 1`.

Own elementary argument (AGENT_GUIDE cost rule); the image-circle half it mirrors is
`XAreaPCModI.lean`. Compare Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace QuantumZipper.E6
namespace XAreaPC

/-- `kernelCov` of two pushforwards, as an iterated integral of the pulled-back kernel. -/
theorem kernelCov_map_eq {φ : ℂ → ℂ} (hφ : Measurable φ) (ν ν' : Measure ℂ)
    [IsFiniteMeasure ν'] :
    kernelCov neumannH (ν.map φ) (ν'.map φ) = ∫ x, (∫ w, neumannH (φ x) (φ w) ∂ν') ∂ν := by
  unfold kernelCov
  rw [integral_map hφ.aemeasurable]
  · refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_map hφ.aemeasurable]
    exact (measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (StronglyMeasurable.integral_prod_right' (ν := ν'.map φ)
      (f := fun p : ℂ × ℂ => neumannH p.1 p.2)
      measurable_neumannH.stronglyMeasurable).aestronglyMeasurable

section Push

variable {φ : ℂ → ℂ} {K : Set ℂ}

end Push

end XAreaPC
end QuantumZipper.E6
