-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGContinuity.Frozen.EuclidDistC
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGContinuity.Frozen.SupDistLU
import HigherDimLQGContinuity.Frozen.XiRange
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.DistExp
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import HigherDimLQGContinuity.Assembly.Theorem11Xi

/-!
# Frozen theorem: `theorem11Xi`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N3, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): Theorem 1.1, l. 32–47 ((1.2)–(1.4)), in the Weyl
parameter `ξ` of (1.5), l. 74–81, with the setting of l. 16–30 and the construction of §5, l. 1128–1309
("one field-measurable, locally uniformly continuous family", l. 1163). The `ξ`-parametrized core (ruling N4):
for `d ≥ 3` there is one jointly measurable family `D : ℝ → 𝒟'(ℝ^d) → C(ℝ^d × ℝ^d, ℝ)`, applied to the same
field, with `D 0 = |x − y|`, such that for every subcritical `ξ > 0` (`√(2d) < Q(ξ)`) and every strong
assignment at `(ξ, Q(ξ))` with median one ((1.2)), `D ξ` is a version of it on every normalized LGF on every
probability space, and almost surely `ξ ↦ D ξ h` is continuous on `xiRange d = {0} ∪ {ξ > 0 : √(2d) < Q(ξ)}` for
locally uniform convergence of distances ((1.3)–(1.4)). The paper's statement in `γ` is `theorem11`, through the
parametrization `prop18`. Closure condition C1 (ruling N4): this anchor counts as closed only once
`medianOneStrong_exists` is sealed.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly `by exact HigherDimLQGContinuity.theorem11Xi_impl`,
provider `HigherDimLQGContinuity.Assembly.Theorem11Xi`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Theorem 1.1, `ξ`-parametrized core.** For `d ≥ 3` there is a jointly measurable family of versions
`D ξ`, Euclidean at `ξ = 0`, of the median-one strong metrics at every subcritical `ξ > 0`, such that on every
normalized LGF, almost surely, `ξ ↦ D ξ h` is continuous on `xiRange d` for locally uniform convergence. -/
theorem theorem11Xi :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D ξ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R (D ξ (h ω)) (D ξ₀ (h ω))) (𝓝[xiRange d] ξ₀) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGContinuity.theorem11Xi_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGContinuity
-- FROZEN_ANCHOR_SUFFIX_END
