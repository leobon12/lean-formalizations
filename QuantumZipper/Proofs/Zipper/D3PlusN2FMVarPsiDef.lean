import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part E: the first Fourier mode of the logarithmic kernel on the unit circle

`fmPsi y = ∫_0^{2π} cos θ · (−log |y − e^{iθ}|) dθ`, classically `π Re y` for `|y| ≤ 1` and
`π Re y / |y|²` for `|y| ≥ 1` (expand `log |1 − z| = −Re Σ z^k / k`). The node `FMPsiStmt`
records the two consequences used by the energy estimates: `|fmPsi| ≤ π` and `fmPsi` is
`π`-Lipschitz.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-- First Fourier mode of `−log |y − ·|` on the unit circle. -/
def fmPsi (y : ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ * -Real.log ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖

/-- **Node FM-PSI.** `|fmPsi| ≤ π` and `fmPsi` is `π`-Lipschitz. -/
def FMPsiStmt : Prop :=
  (∀ y : ℂ, |fmPsi y| ≤ π) ∧ ∀ y y' : ℂ, |fmPsi y - fmPsi y'| ≤ π * ‖y - y'‖

end D3Plus
end QuantumZipper
