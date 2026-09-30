import QuantumZipper.Proofs.Thm11.AddendumAssembly
import QuantumZipper.Proofs.Thm11.AddendumMart
import QuantumZipper.Proofs.Thm11.ExtMeasFinal

/-!
# Theorem 1.1 (with its addendum), unconditional

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, Theorem 1.1 and the addendum (p. 12).

The main part is `Thm11MainFull.theorem1_1_main_proof`. The addendum is
`Thm11Asm.theorem1_1_addendum_of_nodes`, whose three inputs are now proved:
`extMeasStmt` (joint measurability of the extended field), `extIntStmt_of_meas` and
`extMartStmt_of_meas` (AD-4 + MF-5).
-/

namespace QuantumZipper.Thm11Asm

/-- **Theorem 1.1** (main part and addendum), with no hypotheses. -/
theorem theorem1_1_proved : theorem1_1 :=
  theorem1_1_of_nodes (extIntStmt_of_meas extMeasStmt)
    (extMartStmt_of_meas extMeasStmt) extMeasStmt

end QuantumZipper.Thm11Asm
