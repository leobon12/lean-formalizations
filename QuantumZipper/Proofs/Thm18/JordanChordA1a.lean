import QuantumZipper.Proofs.Thm18.JordanChord
import QuantumZipper.Proofs.Thm18.G1ZA1a2Beta

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JORDAN-CHORD: closing G1Z-A1a

* `chordSidesDisjointStmt_holds : ChordSidesDisjointStmt` (from `JordanChord.chordSides_disjoint`).
* `g1RerootAffineStmt_holds : G1RerootAffineStmt` (A1a), via `g1RerootAffineStmt_of_disjoint`.
-/

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

/-- **Separation of the two sides of a simple chord** (proved). -/
theorem chordSidesDisjointStmt_holds : ChordSidesDisjointStmt :=
  fun _η hη => JordanChord.chordSides_disjoint hη

/-- **A1a** (`G1RerootAffineStmt`), unconditionally. -/
theorem g1RerootAffineStmt_holds : G1RerootAffineStmt :=
  g1RerootAffineStmt_of_disjoint chordSidesDisjointStmt_holds

end G1ZA1a
end Thm18Asm
end QuantumZipper
