import QuantumZipper.Proofs.Thm18.G1Z3Wedge
import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Proofs.LQG.CoordChangeAvg
import QuantumZipper.Proofs.LQG.WedgeBoundary
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Zipper.BdryAllMapsMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z3 (D58): the fixed-map boundary rule for the (unscaled) wedge field, almost surely

For a free field `X` and an independent wedge radial process `A`, and a FIXED map `ψ`
holomorphic near `[a,b]`, real and increasing there with `ψ' ≠ 0` and `ψ([a,b]) ∌ 0`, almost
surely the boundary approximations of the pulled-back wedge field
`wedgeField (lateralPart X) A Q ∘ ψ + Q log|ψ'|` converge vaguely on `(a,b)` to the transport of
the wedge boundary measure. Ingredients: M4-T4 (`CoordChange.ae_isVagueLimitOnR_coordChange`),
the pushed-convergence hypotheses (`G1Z3.ae_addFun_hyps`), the regular version of the free field
(`WedgeTK.exists_isRegVersion`, `WedgeCan.ae_raw_dyadic`), continuity of `A`, and the per-sample
transfer `G1Z3.isVagueLimitOnR_wedgeField_fixedMap_own` (Duplantier–Sheffield 2011, (5.1),
Prop. 2.1). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z3

/-- An offset-uniform boundary limit of a regular sample is a vague limit of the dyadic
approximations (copy of `F1.isVagueLimitR_of_hasBdryLimit`). -/
theorem isVagueLimitR_of_good_z3 {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x) := by
  obtain ⟨F, hF⟩ := hx.1
  have hν := hx.qBoundaryMeasure_spec
  refine ⟨hν.1, fun f hf hfc => ?_⟩
  refine ((hν.2 f hf hfc).comp GoodSample.tendsto_one_goodFilter).congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF]

end G1Z3
end Thm18Asm
end QuantumZipper
