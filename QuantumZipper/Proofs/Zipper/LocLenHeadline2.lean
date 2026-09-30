import QuantumZipper.Proofs.Zipper.LocLenHeadline
import QuantumZipper.Proofs.Zipper.LocLenStep3Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3 skeleton, version 2 (wiring)

`LocLen.theorem1_3_of_arcNodes` with step (3) of F2 discharged by
`LocLen.step3Arc_of_yMergeOffTip` (needs the base-finiteness fact X1, `BaseFin.BaseFiniteStmt`,
which the paper uses without proof: Berestycki–Powell arXiv:2404.16642 p. 285). The F2 node is
now closed modulo the SW leaf `YMergeOffTipStmt` and X1. Wiring only.
-/

namespace QuantumZipper
namespace LocLen

/-- **Theorem 1.3, open-arc skeleton v2.** Leaves: `YMergeOffTipStmt` (SW), `BaseFiniteStmt`
(X1), and the campaign nodes `E6NodeStmtRichArc` (R5b), `UnzipMeasArcStmt` (R5c),
`F1NodeArcStmt` (R6e). -/
theorem theorem1_3_of_arcNodes_v2 (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) (h6 : E6NodeStmtRichArc) (hmeas : UnzipMeasArcStmt)
    (hF1 : F1NodeArcStmt) : theorem1_3 :=
  theorem1_3_of_arcNodes hYO (step3Arc_of_yMergeOffTip hYO hX1) h6 hmeas hF1

end LocLen
end QuantumZipper
