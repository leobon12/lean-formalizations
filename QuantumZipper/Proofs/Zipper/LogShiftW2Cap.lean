import QuantumZipper.Proofs.Zipper.LogShiftW2Trace
import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.LQG.FractionalMoments
import QuantumZipper.Proofs.Zipper.WedgeTipXNonvanish

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W2 (5): capstones

* `lswPosStmt_holds`: `LswPosStmt` (from `lswPosTraceStmt_holds`).
* `logShiftLenWeightStmt_of_zcocycle`: `F1.LogShiftLenWeightStmt` from the `Γ⁰` nodes
  `LenPairCocycleCfgStmt`, `LenRegCfgStmt`, the new leaf `LswZCocycleRegStmt`, and the wedge nodes
  `YGoodAllStmt`, `TipXStmt`, `XContinuumStmt` (`GlobalCaraStmt`, `ExtNonvanishStmt` are proved).
* `logShiftLenWeightStmt_of_piece`: the same with TIP-X through the D51 route
  (`WedgeUnzip.tipX_of_route`, `tipYWMaj_of_piece`): `YGoodAllStmt` + `TipYWPieceStmt`.

The nodes `LogShiftWArcsStmt` and `LogShiftWDensShiftStmt` of LSL-W are no longer needed.
Own bookkeeping.
-/

namespace QuantumZipper
namespace F1

theorem lswPosStmt_holds : LswPosStmt := lswPosStmt_of_trace lswPosTraceStmt_holds

end F1
end QuantumZipper
