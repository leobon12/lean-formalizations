import QuantumZipper.Proofs.Zipper.LocLenHeadline4
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll
import QuantumZipper.Proofs.Zipper.LocLenR5aLen
import QuantumZipper.Proofs.Zipper.LocLenR5aZip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3 skeleton, version 5 (wiring)

`LocLen.theorem1_3_of_arcNodes_v4` with the SW leaf `YMergeOffTipStmt` discharged
(`SWCore.yMergeOffTipStmt_holds`), and `LenCollidedAllArcStmt`, `CanonZipRawAllArcStmt` by the
proved `lenCollidedAllArcStmt_holds`, `canonZipRawAllArcStmt_holds` (R5a). Wiring only.
-/

namespace QuantumZipper
namespace LocLen

open R5c

/-- **Theorem 1.3, open-arc skeleton v5.** Leaves: X1 and the open Arc nodes of R5a/R5c/R6. -/
theorem theorem1_3_of_arcNodes_v5 (hX1 : BaseFin.BaseFiniteStmt) (hSZ : HitScaleZipArcStmt)
    (hPR : E6PalmRegArcStmt) (hsm : LenStrictMonoArcStmt) (hC : LenPairCocycleArcStmt)
    (hLR : LenLeftRegArcStmt) (hLU : LenLeftUnbddArcStmt) (hF : LenFiniteArcStmt)
    (hreg : LenRegArcStmt) (hrr : LenReadRegArcStmt) : theorem1_3 :=
  theorem1_3_of_arcNodes_v4 SWCore.yMergeOffTipStmt_holds hX1 hSZ lenCollidedAllArcStmt_holds
    canonZipRawAllArcStmt_holds hPR hsm hC hLR hLU hF hreg hrr

end LocLen
end QuantumZipper
