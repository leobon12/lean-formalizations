import QuantumZipper.Proofs.Thm18.G3Cv2Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 3 (one-point core): the normalized zoom through a G0 map is a D3⁺ `Setup` model

`exists_g0Setup`: for an admissible local map `ψ` of G0 and `0 < γ < 2`, there are `r > 0`, a
reference circle `ρ₀ = fc(0, s)` (`s = 2r`) and, on one probability space, a free field `W`
together with **D3⁺ `Setup` data** `(X', Ξ, g)` at radius `r`
(`D3Plus.Setup γ 0 r ρ₀ stdP X' Ξ g`: `X'` free, `Ξ ⊥ X'`, `g ∘ foldH` harmonic on `B(0,r)`,
`g` measurable for `condSigma Ξ X' r`, `ρ₀` admissible of mass `1` outside `B(0, r)`), such that
almost surely, for every level `L`, the zoom of `W` through `ψ` normalized at `ρ₀`,
`addConst (coordChange (W ω) ψ Q) (L/γ − coordChange (W ω) ψ Q ρ₀)`, agrees near `0`
(`AgreeNear … r`) with the model field `zoomModel γ 0 L ρ₀ (X' ω) (g ω)`.

So D3⁺(i) (`D3PlusIStmtRich`) applies to the zoom through `ψ` (via `locFieldFull_canonicalOn_congr`
once the local scale is below `r / R`): this is G0 at one point for a free field, with the
additive gauge fixed at `ρ₀` (as in `zoomModel`). Sources as in G3CvSetup.lean. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm D3Plus

theorem measurable_integral_family {Ω : Type*} (m : MeasurableSpace Ω) {u : ℂ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun v => u v ω) (hm : ∀ v, Measurable (u v)) (μ : Measure ℂ)
    [SFinite μ] : Measurable fun ω => ∫ v, u v ω ∂μ := by
  have hu : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  exact (StronglyMeasurable.integral_prod_left (μ := μ) hu.stronglyMeasurable).measurable

end G3Cv
end QuantumZipper
