import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPsiDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part E: the Neumann potential of a first-mode pair

`fmPot w v s x = ∫ neumannH x y d(fmMeas w v s)(y) − ∫ neumannH x y d(fmMeas w (−v) s)(y)`.
With `v = τ u`, `‖u‖ = 1`, `s ≤ τ`, `3τ ≤ Im w` and `x ∈ Hbar` it equals
`avg_φ fmPsi(ū (x + s e^{iφ} − w)/τ) + fmPsi(ū (x̄ − w)/τ)` (circle-average identity
`−log max(s, |z − x|) = avg_φ (−log |x + s e^{iφ} − z|)`, the reflected term is harmonic, and the
`−log τ` constant is killed by `∫ cos = 0`), hence it is `2π/τ`-Lipschitz on `Hbar` by
`FMPsiStmt`. The node `FMPotLipStmt` records this Lipschitz bound.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-- Neumann potential of the first-mode pair `(fmMeas w v s, fmMeas w (−v) s)`. -/
def fmPot (w v : ℂ) (s : ℝ) (x : ℂ) : ℝ :=
  (∫ y, neumannH x y ∂fmMeas w v s) - ∫ y, neumannH x y ∂fmMeas w (-v) s

/-- **Node FM-POTLIP.** The first-mode potential is `2π/τ`-Lipschitz on `Hbar`. -/
def FMPotLipStmt : Prop :=
  ∀ (u w : ℂ) (τ s : ℝ), ‖u‖ = 1 → 0 < τ → 0 ≤ s → s ≤ τ → 3 * τ ≤ w.im →
    ∀ x ∈ Hbar, ∀ x' ∈ Hbar,
      |fmPot w ((τ : ℂ) * u) s x - fmPot w ((τ : ℂ) * u) s x'| ≤ 2 * π / τ * ‖x - x'‖

end D3Plus
end QuantumZipper
