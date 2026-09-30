import QuantumZipper.Proofs.Thm18.G1RestUnif
import QuantumZipper.Proofs.Thm18.G1RestUnifProf
import QuantumZipper.Proofs.Thm18.G1RestUnifAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF: `G1RestUnifStmt` holds

`g1RestUnifStmt_of` (G1RestUnif.lean) with the two deterministic inputs proved in
G1RestUnifProf.lean (`G1RC.unifProfStmt_holds`) and G1RestUnifAvg.lean
(`G1RC.avgRegPsiStmt_holds`). Source for the probabilistic step: Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1 (through `G1RC.ae_unif_pushed`).
-/

namespace QuantumZipper
namespace Thm18Asm

/-- **The uniform Cauchy input `G1RestUnifStmt` holds.** -/
theorem g1RestUnifStmt_holds : G1RestUnifStmt :=
  G1Rest.g1RestUnifStmt_of G1RC.unifProfStmt_holds G1RC.avgRegPsiStmt_holds

end Thm18Asm
end QuantumZipper
