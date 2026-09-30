import QuantumZipper.Proofs.Thm18.ZqR2Palm
import QuantumZipper.Proofs.Thm18.G3ZqL20TypQ
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqSTop
import QuantumZipper.Proofs.Thm18.G3ZqS2Top
import QuantumZipper.Proofs.Thm18.G3ZqO7CoreD
import QuantumZipper.Proofs.Thm18.G3ZqL14RegU
import QuantumZipper.Proofs.Thm18.ZqT10Top
import QuantumZipper.Proofs.Thm18.ZqCS3
import QuantumZipper.Proofs.Thm18.A1RS3MeasB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 (paper form, R18 layer) with no hypotheses

Wiring only. The body of `ZqR.theorem1_8PaperMO_of_coreD_noPalm` (ZqR3Top) with its
`G3ZqPathSmallUStmt` step taken from the ZQ-TYP route (`ZqT.g3ZqPathSmallUStmt_of_typF`, as in
`ZqT.theorem1_8PaperMO_of_coreD_typ`, ZqT9Top): the zoom-locality input is the proved
`ZqR.g3ZqLZoomLocAEMapStmt_holds` (in place of `g3ZqLZoomLocAEMapStmt_of_palmReg`), and the
typical-point goodness input is the proved `ZqT.g3ZqTMapTypFStmt_holds` (D94, in place of
`G3ZqLMapTypQAEStmt`). The remaining inputs are the proved leaves
`R18.A1RS.a1rfSmearContStmt_holds` and `ZqC.g3ZqO6CoreDStmt_holds`.
-/

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797; paper form, D87), R18 layer, with no
hypotheses. -/
theorem theorem1_8PaperMO_proved : R18.theorem1_8PaperMO :=
  R18.theorem1_8PaperMO_of_open4Z A1RS.a1rfSmearContStmt_holds
    (G3ZqO.g1WedgePalmLimStmt_of_coreD
      (G3ZqL.g3ZqL1ResclIdStmt_of_reg G3ZqL.g3ZqL1ResclRegStmt_holds)
      ZqC.g3ZqO6CoreDStmt_holds)
    G3ZqS.g3ZqResclRegStmt_holds
    (ZqT.g3ZqPathSmallUStmt_of_typF ZqR.g3ZqLZoomLocAEMapStmt_holds
      ZqT.g3ZqTMapTypFStmt_holds)

end R18
end QuantumZipper
