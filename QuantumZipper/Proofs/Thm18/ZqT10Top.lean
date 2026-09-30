import QuantumZipper.Proofs.Thm18.ZqTB1Palm
import QuantumZipper.Proofs.Thm18.ZqTA7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (10): headline with the `V + logSing` clause closed

`G3ZqTVPalmStmt` is proved (`ZqT.ZqTB.g3ZqTVPalmStmt_holds`), so the typical-point goodness leaf
of `G3ZqL.theorem1_8PaperMO_of_coreD` reduces to the scheme clause `G3ZqTSchemeSideStmt`.
Own bookkeeping.
-/

noncomputable section

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G3ZqL G3ZqO

/-- **`G3ZqTMapTypFStmt` holds** (all three clauses: wedge ZqT3/ZqT4, scheme ZqTA7,
`V + logSing` ZqTB1 + ZqT8). -/
theorem g3ZqTMapTypFStmt_holds : G3ZqTMapTypFStmt :=
  g3ZqTMapTypFStmt_of (g3ZqTSchemeStmt_of_side g3ZqTSchemeSideStmt_holds)
    (g3ZqTVStmt_of_side (g3ZqTVSideStmt_of ZqTB.g3ZqTVPalmStmt_holds g3ZqTVPartnerStmt_holds))

end ZqT
end Thm18Asm
end QuantumZipper
