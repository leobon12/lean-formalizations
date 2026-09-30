import QuantumZipper.Proofs.Zipper.E5Main6

/-!
# E5-MODEL, part 1: the approximate identification input and its representation form

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**, steps (1)–(3); Sheffield,
arXiv:1012.4797, §5.4 (pp. 66–72), proof of Lemma 5.6.

## Why an approximate form

`E5Main5.E5ModelStmtG` asks for **one** zoom model `M` (with a *deterministic* radius `M.r`)
whose functional is TV-near E5's left side. In the intended construction (blueprint step (1)) the
correction is `g = −(√κ/2)·k_{ϖ_τ} + const`, which is harmonic (after folding) only on the ball
around `0` avoiding `supp ϖ_τ = revMap V τ (supp ϖ)`; its radius `ρ(ω) > 0` is random and has no
deterministic lower bound. With a fixed `r`, the model can only match the true field on
`{ρ ≥ r}`, an event of probability `< 1` that does not depend on `C`; so a single model gives
an error that does not vanish as `C → ∞`. (The single-model statement is still *true* — any
zoom model is TV-near the target by `ZoomModel.tvNear` — but it cannot be reached along the
blueprint route without E5 itself.) The fix: for every `ε > 0` a model `M_ε` (radius `r_ε` with
`Q(ρ < r_ε) ≤ ε`) that is `ε`-close to E5's left side eventually in `C`
(`E5ModelApproxG`). This is enough: `e5G_of_approx` closes E5 through `TVNear.of_approx`, and
`e5ModelApprox_of_model` shows the approximate form is implied by the old one.

## Representation form

`E5ReprG` splits off the TV bookkeeping: a model `M`, a representation
`lhs C Γ = p · E_Q Γ(Z C)` of E5's left side on the model space (E4 + Palm normalization), and
agreement of `Z C` with the model data off bad events of eventual `Q`-probability `≤ ε`
(L2 + switch `canonical ↔ canonicalOn`). `e5ModelApprox_of_repr : E5ReprG fr → E5ModelApproxG fr`.

Own bookkeeping (no published proof of these reductions; they are TV-distance triangle
inequalities).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus B2 E1

/-! ## Representation form -/

/-- The model data `(zLoc, drvWin (rescale …))` of a zoom model at level `C`. -/
def ZoomModel.data {F : Type} [MeasurableSpace F] {fr : ℕ → FieldSample → F} {κ : ℝ} {R : ℕ}
    {W : Measure (ℝ≥0 → ℝ)} (M : ZoomModel fr κ R W) (C : ℝ) (ω : M.Ω₁) :
    F × (ℝ≥0 → ℝ) :=
  (zLoc fr (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ R C (M.X' ω) (M.g ω),
    drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0)
      (zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ C (M.X' ω) (M.g ω)).toNNReal
      (M.D ω)))

theorem ZoomModel.fn_eq {F : Type} [MeasurableSpace F] {fr : ℕ → FieldSample → F} {κ : ℝ}
    {R : ℕ} {W : Measure (ℝ≥0 → ℝ)} (M : ZoomModel fr κ R W) (C : ℝ)
    (Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞) : M.fn C Γ = ∫⁻ ω, Γ (M.data C ω) ∂M.Q := rfl

end E5
end QuantumZipper
