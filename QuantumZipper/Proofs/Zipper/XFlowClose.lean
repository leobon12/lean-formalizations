import QuantumZipper.Proofs.Zipper.XFlowEnergyMain
import QuantumZipper.Proofs.Zipper.XFlowMechAdm
import QuantumZipper.Proofs.Zipper.XFlowMechIdent
import QuantumZipper.Proofs.Zipper.XFlowMechDet
import QuantumZipper.Proofs.Zipper.XFlowUCFixMain
import QuantumZipper.Proofs.Zipper.XFlowUCLog
import QuantumZipper.Proofs.Zipper.XFlowRC3Phi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The free-field flow nodes, closed

Wiring only: `XFlowUCStmt` from the proved nodes `flowEnergyStmt_holds` (XFlowEnergyMain),
`flowAdmStmt_holds`, `flowIdentStmt_holds`, `flowDetStmt_holds` (XFlowMech*) and
`xFlowLogUCStmt_holds` (XFlowUCLog); hence `XFlowRC3Stmt` and the wedge-core node
`WedgeUnzip.XExactAllStmt` (XFlowRC3Phi).
-/

namespace QuantumZipper
namespace F1

theorem xFlowUCStmt_holds : XFlowUCStmt :=
  xFlowUCStmt_of_nodes flowEnergyStmt_holds flowAdmStmt_holds flowIdentStmt_holds
    flowDetStmt_holds xFlowLogUCStmt_holds

theorem xFlowRC3Stmt_holds : XFlowRC3Stmt :=
  xFlowRC3Stmt_of_flowUC xFlowUCStmt_holds

theorem xExactAllStmt_holds : WedgeUnzip.XExactAllStmt :=
  xExactAll_of_flowUC xFlowUCStmt_holds

end F1
end QuantumZipper
