import QuantumZipper.Proofs.Zipper.LocLenF2Node
import QuantumZipper.Proofs.Zipper.Thm13HeadlineV9
import QuantumZipper.Proofs.Zipper.SWCoreA9Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3 skeleton with open-arc lengths (wiring)

Theorem 1.3 (statement `theorem1_3`, unchanged) from the open-arc backbone: E4 and E5 exactly as
in the current headline (they read no length; `E4Grid.e4_unconditional`, `E5.e5Rich_of_repr'`
with the proved D3⁺ and representation inputs of `E5.theorem1_3_of_vague_fix3` /
`E5.theorem1_3_of_frontier_v7`), the F2 node `LocLen.f2NodeArc_of_step3`, and the three open
open-arc nodes `E6NodeStmtRichArc`, `UnzipMeasArcStmt`, `F1NodeArcStmt` plus step (3)
`Step3ArcStmt`. None of TipCore, TipXUnitPieceMom, TipXUnitTipMom appears. Wiring only
(Sheffield arXiv:1012.4797 §5.4 pp. 69–72).
-/

namespace QuantumZipper
namespace LocLen

/-- **Theorem 1.3, open-arc skeleton.** Leaves: the SW input `YMergeOffTipStmt` and the campaign
nodes `Step3ArcStmt` (R7a), `E6NodeStmtRichArc` (R5b), `UnzipMeasArcStmt` (R5c),
`F1NodeArcStmt` (R6e). -/
theorem theorem1_3_of_arcNodes (hYO : WedgeUnzip.YMergeOffTipStmt) (h3 : Step3ArcStmt)
    (h6 : E6NodeStmtRichArc) (hmeas : UnzipMeasArcStmt) (hF1 : F1NodeArcStmt) : theorem1_3 :=
  theorem1_3_of_nodes_richArc E4Grid.e4_unconditional
    (E5.e5Rich_of_repr' (D3Plus.d3PlusIRich_of_N2 D3Plus.d3PlusIN2RichStmt_holds)
      (D3Plus.d3PlusIIRich_of_tWin (D3Plus.lsccTWinInd_of_hitPath D3Plus.hitPathIndStmt_holds)
        D3Plus.hitLevSpreadStmt_holds)
      (E5.e5ReprG'_of_parts3 (E5.e5LvlZoomParts3Stmt_of_partsB E5.e5LvlZoomPartsB_holds)
        E5.zoomModelNonempty_holds))
    h6 hmeas hF1 (f2NodeArc_of_step3 hYO h3)

end LocLen
end QuantumZipper
