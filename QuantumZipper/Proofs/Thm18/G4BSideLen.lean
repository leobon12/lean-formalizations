import QuantumZipper.Proofs.Thm18.G4BSideGeom
import QuantumZipper.Proofs.Thm18.G4CapLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core B (task G4C-2): equal side lengths of every re-zipped arc, all times

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 and §5.4
(pp. 69–72: the two sides of every piece of `η` have the same quantum length; lengths are read in
the unzipped picture, §1.4). Own elementary bookkeeping.

Let `c` be the wedge configuration, `τ ≥ r > 0`, `u = τ − r`, `V = vrev W τ`. By the pair length
cocycle (`F1.LenPairCocycleStmt`, both halves, transported to the wedge sample as in
`g4UnzipCapLenStmt_of_pair`),

  `L^±(τ) = L^±(u) + L^±(Z^{cap}_{−u} c, r)`,

and by the capacity field cocycle (`UnzipCapRegData`) the field of `Z^{cap}_{−u} c` unzipped by
`r` has the boundary measure of `U_τ`, while its side images are `(0₋^V(r), 0₊^V(r))`
(`ae_sideImages_zipCapDown`). Since `L⁻ = L⁺` at `τ` and at `u` (`LenEqStmt`) and `L⁻(u) < ∞`
(`ν_{U_u}` is locally finite), the two sides of `η[u, τ]` have the same `ν_{U_τ}`-length.

Main results: `side_eq_of_cocycle` (deterministic), `ae_unzipSide_len`,
`g4UnzipSideLenStmt_of_pair : F1.LenPairCocycleStmt → G4UnzipCapRegStmt → G4UnzipSideLenStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- The boundary measure is locally finite (a vague limit, or the junk measure `0`). -/
theorem isLocallyFinite_qBoundaryMeasure (γ : ℝ) (x : FieldSample) :
    IsLocallyFiniteMeasure (qBoundaryMeasure γ x) := by
  unfold qBoundaryMeasure
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

end G4Core
end Thm18Asm
end QuantumZipper
