import QuantumZipper.Proofs.Zipper.LocLenHeadline2
import QuantumZipper.Proofs.Zipper.LocLenE6NodeMain
import QuantumZipper.Proofs.Zipper.LocLenR5cPStar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3 skeleton, version 3 (wiring)

`LocLen.theorem1_3_of_arcNodes_v2` with the E6 node discharged by
`LocLen.e6NodeStmtRichArc_of_nodes` (R5b) and the measurability node by
`LocLen.unzipMeasArc_of_hitScaleZip` (R5c). Remaining leaves: the SW input `YMergeOffTipStmt`,
X1 `BaseFin.BaseFiniteStmt`, and the campaign nodes `HitScaleZipArcStmt` (R5c),
`LenCollidedAllArcStmt`, `CanonZipRawAllArcStmt`, `E6PalmRegArcStmt` (R5a), `F1NodeArcStmt`
(R6e). No TipCore / TIP-X input. Wiring only (Sheffield arXiv:1012.4797 §5.4 pp. 69–72).
-/

namespace QuantumZipper
namespace LocLen
open R5c

/-- **Theorem 1.3, open-arc skeleton v3.** -/
theorem theorem1_3_of_arcNodes_v3 (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) (hSZ : HitScaleZipArcStmt) (hLC : LenCollidedAllArcStmt)
    (hCZ : CanonZipRawAllArcStmt) (hPR : E6PalmRegArcStmt) (hF1 : F1NodeArcStmt) :
    theorem1_3 :=
  theorem1_3_of_arcNodes_v2 hYO hX1 (e6NodeStmtRichArc_of_nodes hSZ hLC hCZ hPR)
    (unzipMeasArc_of_hitScaleZip hSZ) hF1

end LocLen
end QuantumZipper
