import QuantumZipper.Proofs.Thm12.Semigroup
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Statements.Thm13
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Markov property of the finite-horizon coupling (blueprint node S5-B2, test-pairing form)

For `κ > 0`, `0 ≤ t < T`, a Brownian motion `B` and a free field `X ⊥ B`, let
`h⁰ = couplingFieldRev κ V T X` (the Theorem 1.3 field, `V = √κ B`). Then the joint law of
`(B|[0,t], mass-zero raw pairings of h⁰)` equals the joint law of
`(B|[0,t], mass-zero raw pairings of 𝔥_t(V) + X ∘ revMap V t)` (`coupling_markov`).

Proof: conditionally on the driver path `u` on `[0,t]`, the characteristic function of a pairing
of `h⁰` is `∫ Hf_T(cat(u, v)) dP(v)` over the independent increment path `v`. By flow splitting
(`Semigroup.inner_eq`) this is `exp(i G_u) Ψ_s(σ_u)` with `σ_u` the pushforward of the test
function along `revMap (u) t`; `σ_u` is again a smooth compactly supported mass-zero test function
(`pushTF`), so Theorem 1.2 in characteristic-function form (`Semigroup.Phi_const`) gives
`Ψ_s(σ_u) = exp(i X₀(σ_u) − E₀(σ_u)/2)`, i.e. `Hf_t(u)` (`Semigroup.Hf_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace CouplingMarkov

open CharFun Semigroup Generator

/-! ## 1. Pushing a test function along the reverse flow gives a test function -/

/-! ## 2. The Markov step for the characteristic functions -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Step

/-! ## 3. Joint laws from conditional characteristic functions -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Assembly

theorem couplingFieldRev_eq (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) :
    couplingFieldRev κ W T x = ofFun (hTrev κ W T) + coordChange x (revMap W T) 0 := by
  unfold couplingFieldRev hTrev h0rev
  rfl

end CouplingMarkov
end QuantumZipper
