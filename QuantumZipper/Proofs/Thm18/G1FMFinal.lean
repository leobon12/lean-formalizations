import QuantumZipper.Proofs.Thm18.G1FMVarKolm
import QuantumZipper.Proofs.Thm18.G1FMAdm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE (5): final reduction

`G1FMAdmStmt` holds (`G1FM.isAdmissibleH_pushFm`), so the first-mode node of the G1 rest chain,
and with it `G1RegRepRestStmt`, reduce to the two remaining nodes for the free field pushed by
the selected inverse uniformizer:

* `G1FMReprStmt`: stochastic Fubini for a continuous modification `V` of the pushed circle
  pairings along the first-mode arc measures;
* `G1FMEnergyStmt`: Neumann energies of the pushed first-mode pairs `≤ c`, of their increments
  `≤ c (‖Δw‖ + |Δτ| + |Δs| + |ΔS|)/τ`.

Main results: `g1FMAdmStmt_holds`, `g1RestFirstMode_of_repr_energy`,
`g1RegRepRestStmt_of_repr_energy`. Bookkeeping only.
-/

namespace QuantumZipper
namespace Thm18Asm

/-- **Node G1-FM-ADM holds.** -/
theorem g1FMAdmStmt_holds : G1FMAdmStmt :=
  fun _ hψ _ _ _ _ hs hv hvw hS => G1FM.isAdmissibleH_pushFm hψ hs hv hvw hS

/-- **G1-REST-FIRSTMODE from the representation and energy nodes.** -/
theorem g1RestFirstMode_of_repr_energy (hR : G1FMReprStmt) (hE : G1FMEnergyStmt) :
    G1RestFirstModeStmt :=
  g1RestFirstMode_of_pushVar (g1FMPushVar_of_nodes hR g1FMAdmStmt_holds hE)

/-- **`G1RegRepRestStmt` from the representation and energy nodes.** -/
theorem g1RegRepRestStmt_of_repr_energy (hR : G1FMReprStmt) (hE : G1FMEnergyStmt) :
    G1RegRepRestStmt :=
  g1RegRepRestStmt_of_firstMode (g1RestFirstMode_of_repr_energy hR hE)

end Thm18Asm
end QuantumZipper
