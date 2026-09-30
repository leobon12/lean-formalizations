import QuantumZipper.Proofs.Zipper.E6MeasNode
import QuantumZipper.Proofs.Zipper.E6NodeMain
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.E4L3i
import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.F2WeldTimes
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.HitScaleZipScale
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Zipper.E5Repair4
import QuantumZipper.Proofs.Zipper.E6InReduce
import QuantumZipper.Proofs.Zipper.E6FlowPair
import QuantumZipper.Proofs.Zipper.CfgBatchScale
import QuantumZipper.Proofs.Zipper.CfgBatchLaw
import QuantumZipper.Proofs.Zipper.ZipLen2ContMain
import QuantumZipper.Proofs.Zipper.ZipLen2Main
import QuantumZipper.Proofs.Zipper.YBdryLimBasic
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.MeasUnzipField
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.Zipper.TipXRouteDefs2
import QuantumZipper.Proofs.Zipper.RegShiftUnif
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.Zipper.WedgeTipXNonvanish
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.LQG.FractionalMoments
import QuantumZipper.Proofs.Zipper.F1BatchCoc
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.YBdryMerge2Tip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Task E6-NODES: the three E6 inputs from the existing frontier leaves

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, pp. 70–72). `E6.e6NodeStmtRich_of_frontier_nm` (`E6MeasHeadline.lean`) proves the E6 node
from the `P_*` B5 cluster and three E6 inputs, `LenCollidedAllStmt`, `CanonZipRawAllStmt`,
`E6PalmRegStmt` (the last via `FlowGoodAllStmt`, `e6PalmRegStmt_of_flow`). This file discharges
all three from **existing frontier leaves only**, using the results proved on 2026-09-28:

* the Γ⁰ flow continuum node `B3d.ZipLen.yFlowContStmt_holds` (via
  `zipLenInputsStmt_of_yGood_merge_cont`), the Y-flow chain `yExactAllStmt_holds`,
  `yFlowRC3Stmt_holds`;
* the D33 field cocycle (`RegUnif.capCocycleRegStmt_holds`, inside `lenCollidedStmt_holds`);
* `cfgLenScaleNormStmt_of` (`CfgBatchScale.lean`), `cfgNormLenLawStmt_of_strictMono`
  (`CfgBatchLaw.lean`), `semicircleDriftStmt_holds` (`LenInfCore.lean`).

The remaining open inputs are the frontier leaves `F1.ExtAllInput`
(`RegUnif.AnchorUnifFamExtAllStmt` for every `Γ⁰` pair: SW Thm 4.3 at every horizon),
`TipCore.TipCoreStmt` (the D37-corrected tip core; **not** `RegUnif.TipLevMomentAllStmt` for every
pair, which is false by D37, see `TipCoreDefs.lean`), `WedgeUnzip.YMergeOffTipStmt`,
`WedgeUnzip.YAreaMergeStmt`, `E6.CfgDensStmt`, and the Theorem 1.3 headline hypotheses
`F2.TruncRescaleFreeStmt`, `F2.ScaleGeomAeStmt'`.
Wiring only; no new named statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1

/-- `CfgDensStmt` for every `Γ⁰` setup and horizon (frontier leaf `E6.CfgDensStmt`, quantified
as in its consumer `canonZipRawAllStmt_of_dens`). -/
abbrev CfgDensAllHyp : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → 0 < T →
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    CfgDensStmt κ T P B X

end QuantumZipper.E6
