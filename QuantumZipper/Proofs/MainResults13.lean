import QuantumZipper.Proofs.Zipper.FieldLawler4Final
import QuantumZipper.Proofs.Thm14.Final
import QuantumZipper.Proofs.Zipper.Cor15FieldGood2Headline

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorems 1.3, 1.4 and Corollary 1.5 of Sheffield, arXiv:1012.4797 — proved

`theorem1_3_proved` (Zipper/FieldLawler4Final.lean) closes Theorem 1.3 along Sheffield's own
route (D75: open-arc lengths, goodness away from the tip), with the one fact the paper uses
without proof (finite length near the root, X1) proved via Field–Lawler, EJP 20 (2015), Thm 1.1.
Theorem 1.4 and Corollary 1.5 follow from Theorem 1.3 by the proved reductions
`Thm14Final.theorem1_4_of_theorem1_3` and `Cor15Group.theorem1_5_of_theorem1_3'`.
-/

namespace QuantumZipper

/-- **Theorem 1.4** (Sheffield, arXiv:1012.4797). -/
theorem theorem1_4_proved : theorem1_4 :=
  Thm14Final.theorem1_4_of_theorem1_3 theorem1_3_proved

/-- **Corollary 1.5** (Sheffield, arXiv:1012.4797). -/
theorem theorem1_5_proved : theorem1_5 :=
  Cor15Group.theorem1_5_of_theorem1_3' theorem1_3_proved

end QuantumZipper
