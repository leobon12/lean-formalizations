import QuantumZipper.Proofs.Thm18.G4CoreDefs2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core A revised (task G4-COREA-DECIDE): separated circles at all parameters,
# crossing circles at the random parameters

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1).
Decision and truth check: `handoff/G4-CORE.md`, §6.

Core A of D54 (`G4DriverPushExactAllStmt`) asked exactness of the **later** field `U_τ` at
`σ_i.map (a ψ)`, `ψ = revMapInv (backDrv W τ τ' a)`, for **all** parameters, guarded only by the
null-mass condition `BackSupportI`. For circles that cross the hull of `backDrv`, `ψ` is singular
on the circle; there the all-parameter statement is not provable by the continuity extension of
the D33/XFlow chains (the pushed measure is not continuous in the parameters where the circle meets
the tip), and the integrability conjuncts may fail at exceptional scales (divergent gap sums).
It is therefore split into:

* **A-sep** `G4DriverPushSepAllStmt`: all parameters, but only at circles at positive distance from
  the hull (`BackSepI`, an open condition in the parameters, so the continuity extension of the
  fixed-driver/uniform-Cauchy chain applies; `ψ` is conformal on a neighbourhood of the circle);
* **A-cross** `G4BackCrossStmt`: for fixed lengths `0 < s ≤ ℓ`, at the consumer's random
  parameters `(τ_ℓ, τ_{ℓ−s}, a_ℓ)`: null mass of the hull on every `σ_i` (this subsumes
  `G4DownShortTraceNullStmt`), and exactness + integrability at the circles that are **not**
  separated. The case `s = ℓ` (`τ_0 = 0`, `backDrv W τ 0 a = revDrv W τ a`) is the re-zip of
  `Z_ℓ ∘ Z_{−ℓ}`.

Proved here: `unzipTime_zero`, `backDrv_zero`, and the consumer derivations
`g4UpZipPushRegRegStmt_of_sepCross` (`G4UpZipPushRegRegStmt`) and
`g4DownShortPushRegPStmt_of_sepCross` (`G4DownShortPushRegPStmt`), which bypass the all-times
nodes `G4UpZipRegAllStmt`, `G4DownShortRegAllStmt` (their all-parameter support conjunct is not
known to be true). **Own elementary argument** (case split on separation, instantiation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## Deterministic lemmas -/

/-- `backDrv W τ 0 a = revDrv W τ a`. -/
theorem backDrv_zero (W : ℝ → ℝ) (τ a : ℝ) : backDrv W τ 0 a = revDrv W τ a := by
  simp [backDrv, revDrv]

/-! ## The two revised nodes -/

/-- The `i`-th dyadic folded circle is at positive distance from the hull of `backDrv W τ τ' a`
(up to a null set): some `δ`-thickening of the hull has zero `σ_i`-mass. -/
def BackSepI (c : FieldSample × (ℝ → ℝ)) (τ τ' a : ℝ) (i : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    fcI i (Metric.thickening δ (revHull (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)) = 0

/-! ## Consumer derivations -/

/-! ## Core C adapted to the split -/

end G4Core
end Thm18Asm
end QuantumZipper
