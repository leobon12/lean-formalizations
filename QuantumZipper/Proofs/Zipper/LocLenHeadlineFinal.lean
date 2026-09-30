import QuantumZipper.Proofs.Zipper.LocLenHeadline5
import QuantumZipper.Proofs.Zipper.LocLenR6wWire
import QuantumZipper.Proofs.Zipper.LocLenR6gMain
import QuantumZipper.Proofs.Zipper.LocLenR6cReg
import QuantumZipper.Proofs.Zipper.LocLenR6cMono
import QuantumZipper.Proofs.Zipper.LocLenR2bReg
import QuantumZipper.Proofs.Zipper.LocLenR5cFinal
import QuantumZipper.Proofs.Zipper.LocLenR5cScale
import QuantumZipper.Proofs.Zipper.LocLenPStarArea
import QuantumZipper.Proofs.Zipper.LocLenR5aLaw
import QuantumZipper.Proofs.Zipper.LocLenPosMain
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.WedgeRC3All2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): Theorem 1.3, final wiring (R9-final)

`LocLen.theorem1_3_of_arcNodes_v5` with every Arc node replaced by its proved producer:

* `LenPairCocycleArcStmt`: `lenPairCocycleArc_of_yMergeOffTip` (R6f/R6w);
* `LenFiniteArcStmt`: `lenFiniteArc_of_baseFinite` from X1 and the wedge cocycle (R6g);
* `LenStrictMonoArcStmt`, `LenLeftRegArcStmt`, `LenRegArcStmt`, `LenReadRegArcStmt`: the R6c
  `_of_yMergeOffTip` producers (the last with R2b's `lenReadRegMeasArc_of_yMergeOffTip`);
* `LenLeftUnbddArcStmt`: `lenLeftUnbddArc_of_pStarLenInf` with `PStarLenInfArcStmt` from scale
  invariance (`R5c.pStarLenInfArc_of`, copy of `E6.pStarLenInfStmt_of`);
* `R5c.HitScaleZipArcStmt`: `R5c.hitScaleZipArcStmt_of_nodes` with `pStarAreaAll_of_yMergeOffTip`;
* `E6PalmRegArcStmt`: `e6PalmRegArc_holds` (R5a, universal law of the total open-arc length).

The only remaining hypothesis is X1 (`BaseFin.BaseFiniteStmt`). Wiring only.
-/

namespace QuantumZipper
namespace LocLen

/-- **Theorem 1.3 from X1** (D75 open-arc route, all Arc nodes proved). -/
theorem theorem1_3_of_arcNodes_final (hX1 : BaseFin.BaseFiniteStmt) : theorem1_3 := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  have hI : R5c.PStarLenInfArcStmt :=
    R5c.pStarLenInfArc_of (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
      (pStarZipLenInputsLoc_of_yMergeOffTip hYO) R5c.lenReadTimeArc_holds hsm
      (pStarGoodOffAll_of_yMergeOffTip hYO) (unzipBdryPosArc_of_yMergeOffTip hYO) hF
  have hLU : LenLeftUnbddArcStmt := lenLeftUnbddArc_of_pStarLenInf hI
  exact theorem1_3_of_arcNodes_v5 hX1
    (R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO))
    e6PalmRegArc_holds hsm hC (lenLeftRegArc_of_yMergeOffTip hYO hC hF) hLU hF
    (lenRegArc_of_yMergeOffTip hYO hC hF hLU)
    (lenReadRegArc_of_yMergeOffTip hYO hC hF (lenReadRegMeasArc_of_yMergeOffTip hYO))

end LocLen
end QuantumZipper
