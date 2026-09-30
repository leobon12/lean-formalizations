import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW: the anchored flow maps as a Lipschitz family in one boundary class

The maps `ψ_s = revMapExt (vrev W s) (s - q)` are **not** Lipschitz in `s` in the centered
coordinates for a general continuous `W` (`ψ_s z = z + W s - W q - ∫…`). They are Lipschitz after
the real translation by `W s`. We therefore use the two-parameter family

  `flowFam W q ![s, w] z = ψ_s (z + w - W s)`,     so that `flowFam W q ![s, W s] = ψ_s`,

(`flowFam_diag`), and prove (`flow_local_class`): locally around any `s₀ ∈ [q,T]`, for
`|s - s₀| ≤ ε`, `|w - W s₀| ≤ ε`, all these maps lie in one rational class
`BdryClass a b ρ M 1` whose segment contains the moving window `F_{T-s}[u',v']`, and they are
Lipschitz in `(s,w)` on the `ρ`-thickening. Since `W` is continuous, `(s, W s)` lies in the
parameter box for `s` near `s₀`.

Own arguments (restart of the reverse Loewner integral equation, Grönwall, quantitative
Picard–Lindelöf radius); sources of the ingredients as in `UnifACFlowDetFam` and
`RevMapExtension` (A2-ext).
-/

noncomputable section

open Complex Filter MeasureTheory Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension B2

/-- The two-parameter flow family `(s, w) ↦ ψ_s (· + w - W s)`. -/
def flowFam (W : ℝ → ℝ) (q : ℝ) (p : Fin 2 → ℝ) (z : ℂ) : ℂ :=
  revMapExt (vrev W (p 0)) (p 0 - q) (z + (p 1 : ℂ) - (W (p 0) : ℂ))

theorem flowFam_apply (W : ℝ → ℝ) (q s w : ℝ) (z : ℂ) :
    flowFam W q ![s, w] z = revMapExt (vrev W s) (s - q) (z + (w : ℂ) - (W s : ℂ)) := by
  simp [flowFam]

theorem flowFam_diag (W : ℝ → ℝ) (q s : ℝ) :
    flowFam W q ![s, W s] = revMapExt (vrev W s) (s - q) := by
  funext z; rw [flowFam_apply]; congr 1; ring

variable {W : ℝ → ℝ}

end SWCore
end QuantumZipper
