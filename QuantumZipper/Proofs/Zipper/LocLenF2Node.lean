import QuantumZipper.Proofs.Zipper.LocLenF2Unscaled
import QuantumZipper.Proofs.Zipper.LocLenF2Weld
import QuantumZipper.Proofs.Zipper.LocLenStep2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): the F2 node with open-arc lengths, wiring

`F2NodeArcStmt` (= `F1StmtArc → Thm13Asm.Thm13LenStmt`, clause 2 of Theorem 1.3 verbatim) from
the SW leaf `WedgeUnzip.YMergeOffTipStmt` and step (3) `Step3ArcStmt`: step (1)
`f2WeldLenArc_holds`, step (2a) `f2UnscaledArc_of_B3d` + `unscaledB3dLoc_of_yMergeOffTip`,
step (2b) `step2bArc_holds`, step (4) `step4Arc_of_yMergeOffTip`. Sheffield arXiv:1012.4797
§5.4 pp. 70–72. Wiring only.
-/

namespace QuantumZipper
namespace LocLen

/-- **F2 node with open arcs** from `YMergeOffTipStmt` and step (3). -/
theorem f2NodeArc_of_step3 (hYO : WedgeUnzip.YMergeOffTipStmt) (h3 : Step3ArcStmt) :
    F2NodeArcStmt :=
  f2NodeArc_of_inputs f2WeldLenArc_holds (f2UnscaledArc_of_B3d (unscaledB3dLoc_of_yMergeOffTip hYO))
    (f2LocalArc_of_steps step2bArc_holds h3 (step4Arc_of_yMergeOffTip hYO))

end LocLen
end QuantumZipper
