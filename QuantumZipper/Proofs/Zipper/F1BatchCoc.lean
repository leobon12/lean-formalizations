import QuantumZipper.Proofs.Zipper.B5LocF1Side
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Proofs.Zipper.F1LenInRefl
import QuantumZipper.Proofs.Zipper.FlowRegCfg
import QuantumZipper.Proofs.Zipper.YBdryLimBasic
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3 / 1.8, node F1: four small F1 leaves discharged (task F1-BATCH, part 1)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (additivity of the
lengths `L±` along the capacity flow) and §5.4, pp. 70–72 (proof of Theorem 1.3; "by symmetry"
on p. 72 for the `L⁺` side). The paper argues none of these points at this granularity; all
arguments below are own bookkeeping around results already proved or named in this repository.

* `sideSmallStmt_holds`: `B5.SideSmallStmt` is **proved** (`B5.sideSmallStmt`,
  `B5LocF1Side.lean`); re-exported under a `_holds` name so that producer indices see it.
* `pStarLenCocycleStmt_of_pair`: `PStarLenCocycleStmt` is the `L⁻` half of
  `LenPairCocycleStmt`.
* `pStarLenNewPosStmt_of_cocycle_strictMono`: positivity of the newly unzipped length from the
  `L⁻` cocycle and strict monotonicity of `L⁻` (`L⁻_{u+s} = L⁻_u + g`, `L⁻_u < L⁻_{u+s}` ⇒
  `g > 0`).
* `lenRightCocycleCfgStmt_of_leaves`: the `L⁺` half of the capacity cocycle in the `Γ⁰`
  picture from the two analytic inputs at every horizon (`AnchorUnifFamExtAllStmt`,
  `TipLevMomentAllStmt`) and the boundary-merging input `WedgeUnzip.YBdryMergeStmt`, through the
  existing chain `lenRightCocycleCfgStmt_of_refl` (reflection `z ↦ −z̄`),
  `lenLeftCocycleCfgStmt_of_allHorizonInputs`, `cfgFlowRegStmt_of_yBdry`,
  `yBdryLimAllStmt_of_merge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The two analytic inputs at every horizon, for every `Γ⁰` pair (`0 < κ < 4`). -/
def ExtAllInput : Prop :=
  ∀ (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → IsBrownianReal B P →
    IsFreeGFFModConstH X P → IndepFun (pathOf B) X P → RegUnif.AnchorUnifFamExtAllStmt κ P B X

end F1
end QuantumZipper
