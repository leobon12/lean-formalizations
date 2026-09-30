import QuantumZipper.Proofs.Zipper.FlowRegAlive
import QuantumZipper.Proofs.Thm18.G4CapLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: `G4ShiftAliveStmt` holds

`Thm18Asm.G4ShiftAliveStmt` (no real point is swallowed by the SLE_κ flow restarted at any time,
`κ < 4`) is `F1.ae_shift_alive_all` (`FlowRegAlive.lean`: Rohde–Schramm, *Basic properties of
SLE*, Lemma 6.2, at rational restart times by the Markov property, and an own elementary
flow-composition argument for all real restart times).
-/

namespace QuantumZipper
namespace Thm18Asm

/-- **`G4ShiftAliveStmt` holds.** -/
theorem g4ShiftAliveStmt_holds : G4ShiftAliveStmt := fun κ hκ hκ4 _ _ P _ B hB =>
  F1.ae_shift_alive_all κ hκ hκ4.le P B hB

end Thm18Asm
end QuantumZipper
