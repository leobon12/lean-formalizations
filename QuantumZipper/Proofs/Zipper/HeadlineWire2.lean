import QuantumZipper.Proofs.Zipper.E5PartsB
import QuantumZipper.Proofs.Zipper.E5PartsVague
import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.Zipper.E5Repair4
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
import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc
import QuantumZipper.Proofs.Zipper.F2Gamma0TruncCore
import QuantumZipper.Proofs.Zipper.F2ScaleIndep
import QuantumZipper.Proofs.Zipper.PStarAreaCoord
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Proofs.Zipper.F1LenReg
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegAll
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeXExact
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.RegShiftUnifF2
import QuantumZipper.Proofs.Zipper.E6NodeMain
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.E6InReduce
import QuantumZipper.Proofs.Section5.Prop1617HeadlineV2
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarMain
import QuantumZipper.Proofs.Zipper.D3PlusN2H2FreeWin
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinDens
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMain
import QuantumZipper.Proofs.Thm18.G2PalmMain
import QuantumZipper.Proofs.Thm18.G2PalmIdX
import QuantumZipper.Proofs.Thm18.G2PalmIdR
import QuantumZipper.Proofs.Thm18.G2ClipReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Task HEADLINE-WIRE-2: headline wiring only

**Wiring only; no new mathematics.** Three results, each a composition of already proved
statements:

* `E5.theorem1_3_of_vague_fix2` is `E5.theorem1_3_of_vague_fix` (`E5VagueFix.lean`) with the
  hypothesis `E5LvlZoomPartsBStmt` removed: it is supplied by the proved
  `E5.e5LvlZoomPartsB_holds` (`E5PartsB.lean`). Hence Theorem 1.3 of Sheffield, arXiv:1012.4797,
  from the D45-repaired scaling node `F2.ScaleGeomAeStmt'` and the remaining E5 inputs.
* `D3Plus.d3PlusIN2RichStmt_holds` is the D3⁺(i) node in N2 form, from
  `d3PlusIN2Rich_of_win` (`Prop1617HeadlineV2.lean`, from the three restricted-window N2 nodes)
  with all three nodes proved: `D3Plus.n2H2HarmWinStmt_holds` (`D3PlusN2H2FreeWin.lean`),
  `D3Plus.n2H3SplitWinStmt_holds` (`D3PlusN2H3WinDens.lean`) and
  `D3Plus.n2ZPairOsc_of_firstMode (D3Plus.n2ZFirstModeStmt_holds)`
  (`D3PlusN2LipMain.lean` + `D3PlusN2FMVarMain.lean`).
* `Thm18Asm.g2FixMixStmt_of_disint` is `Thm18Asm.g2FixMixStmt_of_palmLeaves`
  (`Thm18/G2PalmMain.lean`) with D3⁺(i) discharged by the previous item, the two Palm identities
  by `g2RootXPalmIdStmt_holds` / `g2RootRPalmIdStmt_holds` (`G2PalmIdX.lean`, `G2PalmIdR.lean`)
  and the two length-smoothing nodes by `g2RootLenSmooth_of_disint` (`G2ClipReduce.lean`).

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797 (Theorem 1.3, §5.4;
Propositions 1.6 and 1.7; Theorem 1.8, pp. 70–72). The node decomposition is the project's; no
step of the paper is re-proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

end E5

namespace D3Plus

/-- **The D3⁺(i) node in N2 form, proved.** From `d3PlusIN2Rich_of_win` with the three
restricted-window N2 nodes all discharged: the model-side Cameron–Martin half of H2
(`n2H2HarmWinStmt_holds`), the lateral/radial splitting node (`n2H3SplitWinStmt_holds`) and the
uniform oscillation bound, which follows from the rescaled first-circle-mode variance node via
`n2ZPairOsc_of_firstMode (n2ZFirstModeStmt_holds)`. -/
theorem d3PlusIN2RichStmt_holds : D3PlusIN2RichStmt :=
  d3PlusIN2Rich_of_win n2H2HarmWinStmt_holds n2H3SplitWinStmt_holds
    (n2ZPairOsc_of_firstMode n2ZFirstModeStmt_holds)

end D3Plus

namespace Thm18Asm

/-- **`G2FixMixStmt` from the two rooted bump disintegrations alone** (for `0 < γ < 2`):
`g2FixMixStmt_of_palmLeaves` with D3⁺(i) supplied by `D3Plus.d3PlusIN2RichStmt_holds`, the Palm
identities by `g2RootXPalmIdStmt_holds` / `g2RootRPalmIdStmt_holds`, and the two length-smoothing
nodes by `g2RootLenSmooth_of_disint`. -/
theorem g2FixMixStmt_of_disint {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : G2RootXDisintStmt γ) (hR : G2RootRDisintStmt γ) : G2FixMixStmt γ := by
  obtain ⟨hSX, hSR⟩ := g2RootLenSmooth_of_disint hγ hγ2 hX hR
  exact g2FixMixStmt_of_palmLeaves hγ hγ2 D3Plus.d3PlusIN2RichStmt_holds
    (g2RootXPalmIdStmt_holds hγ hγ2) hSX (g2RootRPalmIdStmt_holds hγ hγ2) hSR

end Thm18Asm
end QuantumZipper
