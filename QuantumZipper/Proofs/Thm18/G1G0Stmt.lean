import QuantumZipper.Proofs.Section5.Prop16Assembly

/-!
# G0 (conformal invariance of zooms), exact statement (Theorem 1.8, node G0, internal to G1)

Blueprint `SECTION5_BLUEPRINT.md` §3.G, G0: let `ψ` be holomorphic and injective near `0`, real
on `ℝ`, `ψ 0 = 0`, `ψ'(0) > 0`. In the setting of D4 (Proposition 1.6, weighted Palm law
`prop16Q`), the canonical descriptions of `h(x + ψ(·)) + Q log|ψ'| + C/γ` and of
`h(x + ·) + C/γ` have the same TV-local limit as `C → ∞`. Sheffield §5.4 uses this implicitly
when uniformizing a component near the zoom point ("zooming … through a conformal map gives
the same wedge"). The statement below is in the TV-local form of D4⁺ (`Prop16TVStmt`): if the
straight zoom converges TV-locally to the law of `W`, so does the zoom through `ψ_x`.

The map may depend (measurably) on the Palm point `x` (in G1 it is the local uniformizer of the
component at the zipped-in point, conditionally on the independent curve). It is required to
be conformal on the disc `B(0, r₀)` (the Schwarz reflection of a map on the half-disc that is
real on `ℝ`), real on `(−r₀, r₀)`, with `ψ_x(0) = 0` and `ψ_x'(0) > 0`. The zoomed field
through `ψ_x` lives on `ψ_x⁻¹(D − x) ∩ halfDisc r₀`.

Status: statement only (proposed; no consumer in Lean yet — `G1CoreStmt` in `G1Reduce` is the
consumed form of G1).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open Prop16Asm TV

/-- The admissible local conformal maps of G0, on the disc of radius `r₀`. -/
def IsG0Map (r₀ : ℝ) (ψ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ ψ (Metric.ball 0 r₀) ∧ InjOn ψ (Metric.ball 0 r₀) ∧
    (∀ t : ℝ, |t| < r₀ → (ψ t).im = 0) ∧ ψ 0 = 0 ∧ (deriv ψ 0).im = 0 ∧ 0 < (deriv ψ 0).re

/-- The zoom of `h` at `x`, through `ψ`, at level `C`: `h(x + ψ(·)) + Q log|ψ'| + C/γ`. -/
def zoomFieldVia (γ C : ℝ) (h : FieldSample) (x : ℝ) (ψ : ℂ → ℂ) : FieldSample :=
  addConst (coordChange (translate h (x : ℂ)) ψ (Qc γ)) (C / γ)

end Thm18Asm
end QuantumZipper
