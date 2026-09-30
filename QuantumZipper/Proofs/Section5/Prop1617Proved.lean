import QuantumZipper.Proofs.Section5.Prop1617HeadlineFinal
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Propositions 1.6 and 1.7, proved

Sheffield, arXiv:1012.4797, Propositions 1.6 and 1.7. The headline
`Prop1617HeadlineFinal.lean` derives both from the single node
`D3Plus.N2ZFirstModeVarStmt` (Gaussian variance bounds for the rescaled first circle mode),
which is proved in `D3PlusN2FMVarMain.lean` (`D3Plus.n2ZFirstModeVarStmt_holds`).
-/

namespace QuantumZipper

/-- **Proposition 1.7** of Sheffield, arXiv:1012.4797. -/
theorem theorem1_7_proved : theorem1_7 :=
  theorem1_7_of_firstModeVar D3Plus.n2ZFirstModeVarStmt_holds

/-- **Proposition 1.6** of Sheffield, arXiv:1012.4797. -/
theorem theorem1_6_proved : theorem1_6 :=
  theorem1_6_of_firstModeVar D3Plus.n2ZFirstModeVarStmt_holds

end QuantumZipper
