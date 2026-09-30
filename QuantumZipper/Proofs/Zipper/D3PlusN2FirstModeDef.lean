import QuantumZipper.Proofs.LQG.WedgeToolkit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE: statement of the first-circle-mode node (probabilistic half of N2Z-PAIRLIP)

Task N2Z-FIRSTMODE. The node `N2ZPairLipStmt` (`D3PlusN2OscEquiv.lean`) is split into

* (P) the probabilistic node `N2ZFirstModeStmt` stated here: almost surely, uniformly for centres
  `w` in a compact `K ⊆ H`, radii `τ ∈ (0, τ₀)` and smoothing radii `s ∈ (0, τ)`, the first
  Fourier mode on the circle `∂B(w, τ)` of the `s`-circle-averaged field is `O(τ^{-1/2})`;
* (D) the deterministic implication `N2ZFirstModeStmt → N2ZPairLipStmt` (another file).

The first mode kills the additive constant of the field modulo constants and has variance `O(1)`
at every scale, so its true a.s. size is `O(√log(1/τ))` (Hu–Miller–Peres, *Thick points of the
Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1 for the analogous circle-average modulus);
the bound `C/√τ` is deliberately weaker.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-- **Node N2Z-FIRSTMODE.** For a free field modulo constants there is a regular version `G`
such that almost surely, for every compact `K ⊆ H` there are `C` and `τ₀ > 0` with
`‖∫_0^{2π} G(w + τ e^{iθ}, s) e^{iθ} dθ‖ ≤ C / √τ` for all `w ∈ K`, `τ ∈ (0, τ₀)`, `s ∈ (0, τ)`. -/
def N2ZFirstModeStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
          ‖∫ θ in (0 : ℝ)..(2 * π),
              ((G ω (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), s) : ℝ) : ℂ) *
                Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ

end D3Plus
end QuantumZipper
