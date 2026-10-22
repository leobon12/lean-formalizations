-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGContinuity.Frozen.EuclidDistC
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGContinuity.Frozen.SupDistLU
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.DistExp
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import HigherDimLQGContinuity.Assembly.Theorem11

/-!
# Frozen theorem: `theorem11`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N3, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): **Theorem 1.1**, l. 32–47, verbatim in `γ`:
(1.2) the γ-LQG metric (`0 < γ < √(2d)`; the strong assignment of [8] at the Weyl parameter `ξ` with
`Q(ξ) = d/γ + γ/2`, (1.5), l. 74–77, and l. 25–30) normalized by `med D^γ_h(0, e₁) = 1`; `D⁰_h(x, y) = |x − y|`
(l. 36); versions on the same field (one jointly measurable family `D : ℝ → 𝒟'(ℝ^d) → C(ℝ^d × ℝ^d, ℝ)` applied
to the same field; §5, l. 1163) such that, almost surely, `γ ↦ D^γ_h` is continuous on `[0, √(2d))` for locally
uniform convergence of distances ((1.3), in the explicit form (1.4), l. 40–44: on one event, for every `γ₀` and
every `R`). For every `d ≥ 3`, every normalized LGF (l. 17–18) on every probability space. The version clause
quantifies over every `ξ > 0` with `Q(ξ) = d/γ + γ/2` (no choice of `ξ`): `prop18` proves there is exactly one.
Closure condition C1 (ruling N4): this anchor counts as closed only once `prop18` and `medianOneStrong_exists`
are sealed.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly `by exact HigherDimLQGContinuity.theorem11_impl`,
provider `HigherDimLQGContinuity.Assembly.Theorem11`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Theorem 1.1.** For `d ≥ 3`, the γ-LQG metrics normalized by median one (`0 < γ < √(2d)`), together with
the Euclidean metric at `γ = 0`, admit versions on the same field (one jointly measurable family) such that,
on every normalized LGF, almost surely `γ ↦ D γ h` is continuous on `[0, √(2d))` for locally uniform
convergence of distances. -/
theorem theorem11 :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
          Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
            (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGContinuity.theorem11_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGContinuity
-- FROZEN_ANCHOR_SUFFIX_END
