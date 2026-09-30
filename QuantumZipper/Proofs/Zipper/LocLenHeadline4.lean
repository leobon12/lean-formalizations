import QuantumZipper.Proofs.Zipper.LocLenHeadline3
import QuantumZipper.Proofs.Zipper.LocLenF1NodeMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3 skeleton, version 4 (wiring)

`LocLen.theorem1_3_of_arcNodes_v3` with the F1 node discharged by `LocLen.f1NodeArc_of_inputs`
(R6e) and `UnzipMeasArcStmt` by `LocLen.unzipMeasArc_of_hitScaleZip` (R5c). Remaining leaves:
the SW input `YMergeOffTipStmt`, X1 `BaseFin.BaseFiniteStmt`, and the open campaign nodes
`HitScaleZipArcStmt` (R5c), `LenCollidedAllArcStmt`, `CanonZipRawAllArcStmt`,
`E6PalmRegArcStmt` (R5a), `LenStrictMonoArcStmt`, `LenPairCocycleArcStmt` (R6f),
`LenLeftRegArcStmt`, `LenLeftUnbddArcStmt`, `LenRegArcStmt`, `LenReadRegArcStmt` (R6c/R6h),
`LenFiniteArcStmt` (R6g, X1 in `P_*` form). No TipCore / TIP-X input. Wiring only.
-/

namespace QuantumZipper
namespace LocLen
open R5c

/-- **Theorem 1.3, open-arc skeleton v4.** -/
theorem theorem1_3_of_arcNodes_v4 (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) (hSZ : HitScaleZipArcStmt) (hLC : LenCollidedAllArcStmt)
    (hCZ : CanonZipRawAllArcStmt) (hPR : E6PalmRegArcStmt)
    (hsm : LenStrictMonoArcStmt) (hC : LenPairCocycleArcStmt) (hLR : LenLeftRegArcStmt)
    (hLU : LenLeftUnbddArcStmt) (hF : LenFiniteArcStmt) (hreg : LenRegArcStmt)
    (hrr : LenReadRegArcStmt) : theorem1_3 :=
  theorem1_3_of_arcNodes_v3 hYO hX1 hSZ hLC hCZ hPR
    (f1NodeArc_of_inputs hYO hsm hC hLR hLU hF hreg hrr (unzipMeasArc_of_hitScaleZip hSZ))

end LocLen
end QuantumZipper
