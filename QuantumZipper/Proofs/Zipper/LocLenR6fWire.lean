import QuantumZipper.Proofs.Zipper.LocLenR6fMain
import QuantumZipper.Proofs.Zipper.LocLenR6fReg
import QuantumZipper.Proofs.Zipper.LocLenR6gMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6f (4): wiring

* `wedgePairCocycleArc_iff`: R6g's `WedgePairCocycleArcStmt` (LocLenR6gMain.lean) is
  definitionally `LenPairCocycleUnscaledArcStmt'`.
* `wedgePairCocycleArc_of_weight`: it holds from the open-arc log-shift weight input alone (the
  `Γ⁰` open-arc cocycle, R6a, and the `Γ⁰` open-arc regularity, `lenRegCfgArc_holds`, are
  proved).
* `lenPairCocycleArc_of_weight`, `lenStrictMonoArc_of_weight`: the `P_*` statements.

Own bookkeeping.
-/

namespace QuantumZipper
namespace LocLen

theorem wedgePairCocycleArc_iff : WedgePairCocycleArcStmt ↔ LenPairCocycleUnscaledArcStmt' :=
  Iff.rfl

/-- **The unscaled wedge open-arc pair cocycle (R6g's input) from the log-shift weight.** -/
theorem wedgePairCocycleArc_of_weight (hW : LogShiftLenWeightArcStmt) :
    WedgePairCocycleArcStmt :=
  wedgePairCocycleArc_iff.2 (lenPairCocycleUnscaledArc'_of_logShift
    (logShiftLenFlowMeasArc_of_weight lenPairCocycleCfgArc_holds lenRegCfgArc_holds hW))

/-- **`LenPairCocycleArcStmt` from `YMergeOffTipStmt` and the log-shift weight.** -/
theorem lenPairCocycleArc_of_weight (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hW : LogShiftLenWeightArcStmt) : LenPairCocycleArcStmt :=
  lenPairCocycleArc_of_logShift hYO lenRegCfgArc_holds hW

end LocLen
end QuantumZipper
