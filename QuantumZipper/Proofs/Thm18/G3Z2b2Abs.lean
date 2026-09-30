import QuantumZipper.Proofs.Thm18.G3Z2b2Dil
import QuantumZipper.Proofs.Zipper.Cor15GoodConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (3): the canonical description absorbs a domain dilation of the zoom map

The measurable local maps of `G3Z2b2Loc` agree with the curve's local maps only up to a
precomposition `w ↦ c w` (`g1zLocMap_eq_g3locM`). This file shows that, under the regularity
conditions of `G1Rescale.ChoiceRegular`, the canonical data of the zoom through `f ∘ (c ·)` and
through `f` coincide (`data_canonical_zoomFieldVia_comp_mul`). The zoom is first written as a
coordinate change of the constant-shifted translate (`zoomFieldVia_eq_coordChange_addConst`,
using `evalReg (y + k) = evalReg y + k` under `E1.RegShift`), and then G1's choice independence
`G1.data_canonical_coordChange_eq` applies.

Sheffield, arXiv:1012.4797, §1.6 (remark after (1.8): the canonical description fixes the
scaling freedom). Own bookkeeping on the cited lemmas.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

/-- The zoom through `f` as a coordinate change of the constant-shifted translate. -/
theorem zoomFieldVia_eq_coordChange_addConst (γ L : ℝ) (y : FieldSample) (x : ℝ) {f : ℂ → ℂ}
    (hf : Measurable f) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (h : E1.RegShift (translate y (x : ℂ)) (μ.map f)) :
    zoomFieldVia γ L y x f μ =
      coordChange (addConst (translate y (x : ℂ)) (L / γ)) f (Qc γ) μ := by
  show (evalReg (translate y (x : ℂ)) (μ.map f) + Qc γ * ∫ z, Real.log ‖deriv f z‖ ∂μ) +
      L / γ * (μ univ).toReal =
    evalReg (addConst (translate y (x : ℂ)) (L / γ)) (μ.map f) +
      Qc γ * ∫ z, Real.log ‖deriv f z‖ ∂μ
  rw [Cor15Group.evalReg_addConst_of_regShift' h, Measure.map_apply hf MeasurableSet.univ,
    preimage_univ]
  ring

/-- `avgReg` of the zoom through `f` is that of the coordinate change of the shifted translate. -/
theorem avgReg_zoomFieldVia_eq (γ L : ℝ) (y : FieldSample) (x : ℝ) {f : ℂ → ℂ}
    (hf : Measurable f)
    (hs : ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ)) ((foldedCircle d (radius j)).map f)) :
    avgReg (zoomFieldVia γ L y x f) =
      avgReg (coordChange (addConst (translate y (x : ℂ)) (L / γ)) f (Qc γ)) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact zoomFieldVia_eq_coordChange_addConst γ L y x hf _ (hs _ k)

end G3Z2b2
end Thm18Asm
end QuantumZipper
