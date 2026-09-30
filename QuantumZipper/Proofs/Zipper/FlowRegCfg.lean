import QuantumZipper.Proofs.Zipper.FlowRegSide
import QuantumZipper.Proofs.Zipper.F1LenInRefl
import QuantumZipper.Proofs.Zipper.F1LenInCanon
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.LQG.Measurability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, F1 flow regularity: `CfgFlowRegStmt` from the Y-GOODALL boundary node

The unzipped `Γ⁰` field is literally the field `F2.unzY` of the Y-GOODALL nodes
(`F2.h0rev_add_eq`: `h⁰ + X = (X + α₀(−log|·|)) + γ log|·|`). An offset-uniform boundary limit
(`HasBdryLimit`, along `goodFilter`) of a regular sample restricts to the unit offset, which is the
vague convergence of the dyadic boundary approximations (`GoodSample.tendsto_one_goodFilter`,
`GoodSample.bdryR_radius`). Hence `CfgBdryLimAllStmt` follows from
`WedgeUnzip.YBdryLimAllStmt` and the proved regularity `RegUnif.ae_forall_isRegularSample`, and
`CfgFlowRegStmt` follows from `YBdryLimAllStmt` alone (`cfgFlowRegStmt_of_yBdry`).

Own elementary bookkeeping (Sheffield, arXiv:1012.4797, §1.4: quantum boundary length along the
unzipping, Duplantier–Sheffield boundary measure).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- An offset-uniform boundary limit of a regular sample is a vague limit of the dyadic boundary
approximations. -/
theorem isVagueLimitR_of_hasBdryLimit {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {ν : Measure ℝ} (hν : HasBdryLimit γ x ν) : IsVagueLimitR (bdryApprox γ x) ν := by
  obtain ⟨F, hF⟩ := hx
  refine ⟨hν.1, fun f hf hfc => ?_⟩
  refine ((hν.2 f hf hfc).comp GoodSample.tendsto_one_goodFilter).congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF]

end F1
end QuantumZipper
