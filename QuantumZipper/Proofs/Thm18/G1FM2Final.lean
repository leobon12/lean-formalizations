import QuantumZipper.Proofs.Thm18.G1FM2Energy
import QuantumZipper.Proofs.Thm18.G1FM2PotMain
import QuantumZipper.Proofs.Thm18.G1FM2Repr
import QuantumZipper.Proofs.Thm18.G1FMFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2: the first-mode node and `G1RegRepRestStmt` hold

`G1FMReprStmt` (`G1FM2.g1FMReprStmt_holds`, stochastic Fubini) and `G1FMEnergyStmt`
(`G1FM2.g1FMEnergyStmt_of_pushPotLip` with `G1FM2.pushPotLip_holds`) close the reduction
`g1RegRepRestStmt_of_repr_energy`. Bookkeeping only.
-/

namespace QuantumZipper
namespace Thm18Asm

/-- **Node G1-FM-ENERGY holds.** -/
theorem g1FMEnergyStmt_holds : G1FMEnergyStmt :=
  G1FM2.g1FMEnergyStmt_of_pushPotLip G1FM2.pushPotLip_holds

/-- **`G1RegRepRestStmt` holds.** -/
theorem g1RegRepRestStmt_holds : G1RegRepRestStmt :=
  g1RegRepRestStmt_of_repr_energy G1FM2.g1FMReprStmt_holds g1FMEnergyStmt_holds

end Thm18Asm
end QuantumZipper
