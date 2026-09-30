import QuantumZipper.Proofs.Zipper.LocLenR5cScale
import QuantumZipper.Proofs.Zipper.LocLenR5cReadTime
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): wiring of `HitScaleZipArcStmt`, `LocalAbsRichArcStmt`, `UnzipMeasArcStmt`

With `WedgeUnzip.YMergeOffTipStmt` proved (`SWCore.yMergeOffTipStmt_holds`) and the fixed-time
reading `LenReadTimeArcStmt` proved (`lenReadTimeArc_of_pStarGoodOff`), the open inputs of the
E6 locality chain are: `LenStrictMonoArcStmt` (R6f), `LenFiniteArcStmt` (X1, `P_*` form, R6g)
and the area node `E6.PStarAreaAllStmt` (unchanged by D75).
-/

noncomputable section

namespace QuantumZipper
namespace LocLen
namespace R5c

/-- **`LenReadTimeArcStmt` holds.** -/
theorem lenReadTimeArc_holds : LenReadTimeArcStmt :=
  lenReadTimeArc_of_pStarGoodOff (pStarGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds)

/-- **`HitScaleZipArcStmt` from its remaining open inputs.** -/
theorem hitScaleZipArcStmt_of_nodes (hM : LenStrictMonoArcStmt) (hF : LenFiniteArcStmt)
    (hA : E6.PStarAreaAllStmt) : HitScaleZipArcStmt :=
  hitScaleZipArcStmt_of_frontier SWCore.yMergeOffTipStmt_holds lenReadTimeArc_holds hM hF hA

end R5c
end LocLen
end QuantumZipper

