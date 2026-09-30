import QuantumZipper.Proofs.Thm18.G3Pl4Good
import QuantumZipper.Proofs.Thm18.G3Pl3Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the unscaled comparison from one-field wedge inputs

`g3pl4_unscaled_of_inputs`: the conclusion of `G3PlPhiUnscaledStmt` for one wedge sample space,
from four facts about the unscaled wedge field `Z = g3plUW γ X A` alone (no Palm, zoom or coupling
content):

* (I1) its capped Palm functionals are a.e.-measurable (`g3pl4_aemeasurable_phiCap_Z`);
* (I2) it is a.s. area-good (good, with positive area on open subsets of `ℍ`);
* (I3) for every `η > 0` there is `δ ≤ 1/4` such that, off a measurable event of probability
  `≤ η`, `ν_Z[−δ, 0] < ν_Z[−1/2, 0]` and `ν_Z[−δ, 0] ≤ ν_Z[0, 1/4]`;
* (I4) for every `δ ∈ (0, 1/4]`, `η > 0` there is `U₀` with `P(ν_Z[−δ, 0] < U) ≤ η` for `U ≤ U₀`
  (measurable event).

Route (Sheffield, arXiv:1012.4797, pp. 71–72, Remark 5.7): the wedge window vs the capped window
(`g3pl4_phi_le_phiCap`, cost `U · P(ν_Z[−δ, 0] < U)`); the coupling of `Z` with the normalized free
field `V + (γ − 2/γ)(−log|·|)` on the unit disc (`g3pl4_wedge_fcAgree_norm`, same space); averaged
locality of the zooms at large level (`g3pl4_expect_cap_le`, both directions); law transfer
`E[Φcap(V + log)] = g3plHonX` (`g3pl4_lintegral_phiCap_V_eq`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

theorem g3pl4_inv_mul_le {u a b c : ℝ≥0∞} (hu0 : u ≠ 0) (hut : u ≠ ⊤) (h : a ≤ b + u * c) :
    u⁻¹ * a ≤ u⁻¹ * b + c := by
  calc u⁻¹ * a ≤ u⁻¹ * (b + u * c) := by gcongr
    _ = u⁻¹ * b + c := by
      rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hu0 hut, one_mul]

theorem g3pl4_fcAgree_symm {W : Set ℂ} {y y' : FieldSample} (h : FcAgree W y y') :
    FcAgree W y' y := fun d hd r hr hs => (h d hd r hr hs).symm

/-- A measurable subset of full measure inside an a.s. event. -/
theorem g3pl4_exists_measurable_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Q : Ω → Prop} (hQ : ∀ᵐ ω ∂P, Q ω) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ ω ∈ S, Q ω) ∧ P Sᶜ = 0 := by
  refine ⟨(toMeasurable P {ω | ¬Q ω})ᶜ, (measurableSet_toMeasurable _ _).compl,
    fun ω hω => ?_, ?_⟩
  · by_contra h
    exact hω (subset_toMeasurable _ _ h)
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hQ

end R18
end QuantumZipper
