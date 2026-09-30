import QuantumZipper.Proofs.Zipper.XFlowEnergyE1
import QuantumZipper.Proofs.Zipper.XFlowEnergyE2
import QuantumZipper.Proofs.Zipper.XFlowEnergyE3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY: `FlowEnergyStmt` holds

Assembly (`flowEnergyStmt_of`, `XFlowEnergyAsm.lean`) of admissibility (`flowAdmStmt_holds_E1`), the
uniform radius modulus (`flowE1Stmt_holds`), the uniform time modulus (`flowE2Stmt_of_E1`) and the
circle modulus (`flowE3Stmt_of_E1`).
-/

namespace QuantumZipper
namespace F1

/-- **`FlowEnergyStmt` holds.** -/
theorem flowEnergyStmt_holds : FlowEnergyStmt :=
  flowEnergyStmt_of flowAdmStmt_holds_E1 flowE1Stmt_holds
    (flowE2Stmt_of_E1 flowAdmStmt_holds_E1 flowE1Stmt_holds)
    (flowE3Stmt_of_E1 flowAdmStmt_holds_E1 flowE1Stmt_holds)

end F1
end QuantumZipper
