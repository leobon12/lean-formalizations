import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarKolm
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarEnergy
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarRepr
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPot
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPsi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR: assembly

Task N2Z-FMVAR. The variance node `N2ZFirstModeVarStmt` (hence `N2ZFirstModeStmt`) from the
Lipschitz bound `FMPotLipStmt` of the first-mode Neumann potential: parts F (`fmReprStmt_holds`),
admissibility (`fmAdmStmt_holds`), E (`n2ZFMEnergy_of_potLip`) and K
(`n2ZFirstModeVar_of_nodes`); `FMPotLipStmt` from `FMPsiStmt` (`fmPotLip_of_psi`) and
`fmPsiStmt_holds` close it: `n2ZFirstModeVarStmt_holds`, `n2ZFirstModeStmt_holds`.
-/

namespace QuantumZipper
namespace D3Plus

/-- **N2Z-FIRSTMODE-VAR from the potential bound.** -/
theorem n2ZFirstModeVar_of_potLip (hP : FMPotLipStmt) : N2ZFirstModeVarStmt :=
  n2ZFirstModeVar_of_nodes fmReprStmt_holds fmAdmStmt_holds (n2ZFMEnergy_of_potLip hP)

/-- **Node N2Z-FIRSTMODE-VAR, proved** (`FMPotLipStmt` from `FMPsiStmt`, both proved). -/
theorem n2ZFirstModeVarStmt_holds : N2ZFirstModeVarStmt :=
  n2ZFirstModeVar_of_potLip (fmPotLip_of_psi fmPsiStmt_holds)

/-- **Node N2Z-FIRSTMODE, proved.** -/
theorem n2ZFirstModeStmt_holds : N2ZFirstModeStmt :=
  n2ZFirstMode_of_var n2ZFirstModeVarStmt_holds

end D3Plus
end QuantumZipper
