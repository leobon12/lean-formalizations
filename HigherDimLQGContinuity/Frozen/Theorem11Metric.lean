-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGContinuity.Frozen.EuclidDistC
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGContinuity.Frozen.SupDistLU
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.ContMetricIsLength
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import HigherDimLQGContinuity.Assembly.Theorem11Metric

/-!
# Frozen theorem: `theorem11_metric`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N4, N11).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): **Theorem 1.1**, l. 32–47, in `γ`, as in `theorem11`,
together with the nondegeneracy that [C] §§5.3–5.4 prove for the whole family on one event (l. 1129–1132: the final
nondegeneracy argument "is needed"; l. 1265–1267: "every member of the family is a genuine metric on one event";
l. 1287–1296: proper, Euclidean topology, geodesics, for every parameter): on the same almost-sure event as the
continuity, every member `D γ h` (`γ ∈ [0, √(2d))`) is the distance function of a continuous length metric inducing
the Euclidean topology (`ContMetric d` with `IsLength`). The clauses before the last are those of `theorem11`
(statement audit S1, finding M-1, fix (a); ruling N11). For every `d ≥ 3`, every normalized LGF (l. 17–18) on every
probability space. Closure: [C] Theorem 1.1 counts as proved only once this anchor is sealed (ruling N11), and C1 of
ruling N10 applies to it as to `theorem11`.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLQGContinuity.theorem11_metric_impl`, provider `HigherDimLQGContinuity.Assembly.Theorem11Metric`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Theorem 1.1, with genuine metrics.** For `d ≥ 3`, the γ-LQG metrics normalized by median one
(`0 < γ < √(2d)`), together with the Euclidean metric at `γ = 0`, admit versions on the same field (one jointly
measurable family) such that, on every normalized LGF, almost surely `γ ↦ D γ h` is continuous on `[0, √(2d))` for
locally uniform convergence of distances and every `D γ h` is a continuous length metric inducing the Euclidean
topology. -/
theorem theorem11_metric :
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
        ∀ᵐ ω ∂P, (∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
            Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
              (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0)) ∧
          ∀ γ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∃ M : ContMetric d, M.1 = D γ (h ω) ∧ M.IsLength :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGContinuity.theorem11_metric_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGContinuity
-- FROZEN_ANCHOR_SUFFIX_END
