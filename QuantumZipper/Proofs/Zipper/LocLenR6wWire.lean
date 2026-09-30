import QuantumZipper.Proofs.Zipper.LocLenR6wMain
import QuantumZipper.Proofs.Zipper.LocLenR6fMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6w (3): the R6f capstones with the weight input discharged

With `logShiftLenWeightArc_of_yMergeOffTip`, the open-arc capacity cocycles (unscaled wedge and
`P_*`) follow from `YMergeOffTipStmt` alone, and strict monotonicity of `L⁻` from
`YMergeOffTipStmt` and X1. Own bookkeeping.
-/

namespace QuantumZipper
namespace LocLen

/-- **R6g's wedge cocycle input from `YMergeOffTipStmt`.** -/
theorem wedgePairCocycleArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    WedgePairCocycleArcStmt :=
  wedgePairCocycleArc_of_weight (logShiftLenWeightArc_of_yMergeOffTip hYO)

/-- **`LenPairCocycleArcStmt` from `YMergeOffTipStmt`.** -/
theorem lenPairCocycleArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    LenPairCocycleArcStmt :=
  lenPairCocycleArc_of_weight hYO (logShiftLenWeightArc_of_yMergeOffTip hYO)

/-- **`LenStrictMonoArcStmt` from `YMergeOffTipStmt` and X1.** -/
theorem lenStrictMonoArc_of_yMergeOffTip_x1 (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) : LenStrictMonoArcStmt :=
  lenStrictMonoArc_of_weight_baseFinite hYO (logShiftLenWeightArc_of_yMergeOffTip hYO) hX1

end LocLen
end QuantumZipper
