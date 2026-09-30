import QuantumZipper.Proofs.Zipper.BaseFin2Cov
import QuantumZipper.Proofs.Zipper.BaseFin2Sum
import QuantumZipper.Proofs.Zipper.BaseFin2Unit
import QuantumZipper.Proofs.Zipper.BaseFin2Scale
import QuantumZipper.Proofs.Zipper.BaseFin2ULMain
import QuantumZipper.Proofs.Zipper.BaseFin2ULConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (D75): assembly of the capacity-piece route

`BaseFiniteStmt` (X1: finite open-arc lengths next to the root of the curve at a fixed time) and
`BaseWeightStmt` from the remaining leaves:
* `WedgeUnzip.YMergeOffTipStmt` (Sheffield–Wang merging off the tip; already a leaf of the
  Theorem 1.3 headline `E5.theorem1_3_of_frontier_v11`),
* `SLEBaseTailStmt` (the trace comes within `ε` of its root during `[1/16, 4]` with probability
  `≤ C ε^b`; Lawler 2005, Prop. 6.12, p. 128, qualitatively; route in handoff/TIP-CORE.md §3),
* `BaseUnitLenMomStmt` (a small moment of the `Γ⁰` open-arc lengths of `η[0,1]`).
Proved inputs: `baseCovStmt_holds`, `baseSum_of_scale_unit`, `baseUnitMom_of_tail_len`,
`baseScale_of_yMergeOffTip`, `BaseFin.baseFinite_of_baseWeight`. Own elementary bookkeeping.
-/

namespace QuantumZipper
namespace BaseFin2

/-- **`BaseWeightStmt` from the three leaves.** -/
theorem baseWeight_of_leaves (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hS : SLEBaseTailStmt) (hUL : BaseUnitLenMomStmt) : BaseFin.BaseWeightStmt :=
  baseWeight_of_cov_sum baseCovStmt_holds
    (baseSum_of_scale_unit (baseScale_of_yMergeOffTip hYO) (baseUnitMom_of_tail_len hS hUL))

/-- **X1 (`BaseFiniteStmt`) from the three leaves.** -/
theorem baseFinite_of_leaves (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hS : SLEBaseTailStmt) (hUL : BaseUnitLenMomStmt) : BaseFin.BaseFiniteStmt :=
  BaseFin.baseFinite_of_baseWeight (baseWeight_of_leaves hYO hS hUL)

/-- **`BaseUnitLenMomStmt` holds** (constant: `baseULConstStmt_holds`; first moments:
`baseULGamma0MomStmt_holds`; radius tail: `baseULRadStmt_holds`). -/
theorem baseUnitLenMomStmt_holds : BaseUnitLenMomStmt :=
  baseUnitLenMom_of_const baseULConstStmt_holds

/-- **X1 (`BaseFiniteStmt`) from `YMergeOffTipStmt` (a leaf of the Theorem 1.3 headline) and the
single SLE estimate `SLEBaseTailStmt`.** -/
theorem baseFinite_of_yMerge_tail (hYO : WedgeUnzip.YMergeOffTipStmt) (hS : SLEBaseTailStmt) :
    BaseFin.BaseFiniteStmt :=
  baseFinite_of_leaves hYO hS baseUnitLenMomStmt_holds

end BaseFin2
end QuantumZipper
