-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Assembly.StrongUniqueness

/-!
# Frozen theorem: `strongUniqueness`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M5, M12, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Theorem 1.2, uniqueness clause (l. 82–84: "Any two such assignments at the same `(d, ξ, Q)` differ
almost surely by a deterministic positive constant, simultaneously on all endpoint pairs and after all
continuous perturbations of the field"), for every `d ≥ 3`, `ξ > 0`, `Q > √(2d)` (vacuous unless
`Q = Q(ξ)`, ruling M12). Phase A anchor (ruling M5); proof via Lemma 10.1 (l. 1494–1513) and
`theorem14Sharp`.

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.strongUniqueness_impl` (provider `HigherDimLQGMetric.Assembly.StrongUniqueness`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Phase A** (ruling M5): uniqueness of strong assignments at `(ξ, Q)` for every `ξ > 0`, `Q > √(2d)`. -/
theorem strongUniqueness :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.strongUniqueness_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
