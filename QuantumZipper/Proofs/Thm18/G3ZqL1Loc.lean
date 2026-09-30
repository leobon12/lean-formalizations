import QuantumZipper.Proofs.Thm18.G3ZqNodes
import QuantumZipper.Proofs.Thm18.G3ZpExt
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord
import QuantumZipper.Proofs.Thm18.G1ProfileConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (1): zoom locality through the local maps, area-only deterministic core

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66: the zoom at the root only sees the field
in a vanishing neighbourhood of the root, so adding a bump away from it does not change the zoom
for large `C`. The map version of the deterministic core is `G3Zp.g3zoomLawM_bump_iff`; it asks
`IsLQGGood` of the pulled-back field, which contains a boundary-length clause (D89/D93). Only the
area part is used (the constant shift multiplies the area by `e^{γc}`), so we prove the area-only
variants:

* `areaProxy_addConst_of_areaReg`, `eventually_one_le_areaProxy_addConst_of_areaReg`;
* `g3zoomLawM_eventually_iffA`, `g3zoomLawM_eventually_iff_ballA`, `g3zoomLawM_bump_iffA`.

Own elementary bookkeeping copied from the originals (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open Prop16Area.G Factorization G3Z2b2 G3Zp LQGMeas LocalRule

/-- Area-only regularity of a sample: regular, with an area limit on `ℍ`. -/
def AreaReg (γ : ℝ) (u : FieldSample) : Prop :=
  IsRegularSample u ∧ ∃ μ : Measure ℂ, HasAreaLimit γ u μ

/-- An area-regular sample has a vague area limit on `ℍ`. -/
theorem isVagueLimitOn_H_of_areaReg {γ : ℝ} {u : FieldSample} (hu : AreaReg γ u) :
    ∃ μ, IsVagueLimitOn H (areaApprox γ u) μ := by
  obtain ⟨⟨F, hF⟩, μ, hμ⟩ := hu
  exact ⟨μ, hμ.1, hμ.2.1, fun f hf hfc hfU =>
    ((hμ.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]⟩

end G3ZqL
end Thm18Asm
end QuantumZipper
