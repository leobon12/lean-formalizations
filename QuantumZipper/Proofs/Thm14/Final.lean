import QuantumZipper.Proofs.Wire2
import QuantumZipper.Proofs.Thm14.WeldRead
import QuantumZipper.Proofs.Thm14.SemiApprox

/-!
# Theorem 1.4 from Theorem 1.3

Sheffield, arXiv:1012.4797, Theorem 1.4 (pp. 16–17). Both parts are now proved conditionally on
Theorem 1.3 alone:
* (a) `Wire2.theorem1_4a_of_theorem1_3` (Rohde–Schramm simplicity, Carathéodory and the
  boundary-measure regularity are proved and plugged in);
* (b) `Wire2.theorem1_4b_of_theorem1_3_pairing` with `WeldRPairingReadable` supplied by
  `Thm14WDG.weldRPairingReadable_of Thm14WDG.fcRPairingLimit`.
-/

namespace QuantumZipper.Thm14Final

/-- Theorem 1.4(b), conditional only on Theorem 1.3. -/
theorem theorem1_4b_of_theorem1_3 (h13 : theorem1_3) : theorem1_4b :=
  Wire2.theorem1_4b_of_theorem1_3_pairing h13
    (Thm14WDG.weldRPairingReadable_of Thm14WDG.fcRPairingLimit)

/-- **Theorem 1.4**, conditional only on Theorem 1.3. -/
theorem theorem1_4_of_theorem1_3 (h13 : theorem1_3) : theorem1_4 :=
  ⟨Wire2.theorem1_4a_of_theorem1_3 h13, theorem1_4b_of_theorem1_3 h13⟩

end QuantumZipper.Thm14Final
