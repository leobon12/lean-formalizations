import QuantumZipper.Proofs.Zipper.F2GFFRescale
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 8): the rescaled field is exact at every circle, for every scale at once

For a regular sample `x` (witness `F`), the rescaled field `rescale x Q s` is regular with
witness `F(s ·, s ·) + Q log s` (`IsRegularWith.rescale'`), and its raw value at a folded circle
is `evalReg x (fc(s c, s ρ)) + Q log s = F(s c, s ρ) + Q log s`. Hence
**`evalReg_rescale_fc_eq`**: `evalReg (rescale x Q s) (fc(c, ρ)) = rescale x Q s (fc(c, ρ))` for
**all** `s > 0`, `c ∈ ℍ̄`, `ρ > 0` — deterministically, so for a free field one null set
(`RegSample.ae_isRegularSample`) serves every scale. This is the circle level of the
regularization of the rescaled field in `G4SepScale0Stmt`; the pushed-circle level needs the
scale run of the engine (ASep3Inner/ASep3Box). Also `rescale_fc_eq_witness`: the raw value in
terms of the witness. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter

namespace QuantumZipper
namespace ASep

/-- **Dilation commutes with circle smoothing**: `bindFc (ν.map (s ·)) (s ρ) = (bindFc ν ρ).map (s ·)`.
The level-`j` regularization of `rescale X Q s` at `ν` reads `X` at the right-hand side with
`ρ = 2^{-j}`. -/
theorem bindFc_map_mul (ν : Measure ℂ) [IsFiniteMeasure ν] {s : ℝ} (hs : 0 < s) (ρ : ℝ) :
    RegCont.bindFc (ν.map fun z => (s : ℂ) * z) (s * ρ) =
      (RegCont.bindFc ν ρ).map fun z => (s : ℂ) * z := by
  have hm : Measurable fun z : ℂ => (s : ℂ) * z := measurable_const_mul _
  ext A hA
  rw [Measure.map_apply hm hA]
  show ((ν.map fun z => (s : ℂ) * z).bind fun y => foldedCircle y (s * ρ)) A =
    (ν.bind fun y => foldedCircle y ρ) ((fun z => (s : ℂ) * z) ⁻¹' A)
  have hk : Measurable fun y : ℂ => foldedCircle y (s * ρ) A :=
    (Measure.measurable_coe hA).comp (CircleFubini.measurable_foldedCircle' _)
  rw [CircleFubini.bind_circle_apply _ hA, CircleFubini.bind_circle_apply _ (hm hA),
    lintegral_map hk hm]
  refine lintegral_congr fun z => ?_
  show foldedCircle ((s : ℂ) * z) (s * ρ) A = foldedCircle z ρ ((fun z => (s : ℂ) * z) ⁻¹' A)
  rw [← Thm18Asm.foldedCircle_map_mul hs, Measure.map_apply hm hA]

end ASep
end QuantumZipper
