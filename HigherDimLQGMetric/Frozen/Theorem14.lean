-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Assembly.Theorem14

/-!
# Frozen theorem: `theorem14`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M5, M7, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Theorem 1.4 (l. 111–112: "Any two assignments in this weak class with the same parameter `ξ` are
deterministic positive multiples of one another") with Definition 1.3 (l. 99–109) and the standing
hypotheses of l. 50 (`d ≥ 3`, `ξ > 0`, `Q(ξ) > √(2d)`); conclusion in the form proved at l. 1486–1488
(all points, every continuous perturbation, the same constant). Phase B anchor (rulings M1, M5).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.theorem14_impl` (provider `HigherDimLQGMetric.Assembly.Theorem14`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Theorem 1.4** (auxiliary uniqueness statement): any two assignments in the weak class with the same
parameter `ξ` (arbitrary normalizers) are deterministic positive multiples of one another. -/
theorem theorem14 :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ (D D' : DistRd d → ContMetric d) (c c' : ℝ → ℝ),
      IsWeakExpMetric d ξ D c → IsWeakExpMetric d ξ D' c' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.theorem14_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
