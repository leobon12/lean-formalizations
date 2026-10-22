-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Assembly.SharpWeakNonempty

/-!
# Frozen theorem: `sharpWeak_nonempty`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M5, M13, M14).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Lemma 10.1 (l. 1494–1513: strong candidates are weak with normalizers `r^{ξQ}`) and the existence half
of Theorem 1.2 (l. 1541–1545); rulings M5, M14. Non-vacuity anchor: for every `d ≥ 3` and subcritical
`ξ`, the sharp weak class at `Q = Q(ξ)` (hence the weak class) is nonempty, so `theorem14Sharp` (at
`Q(ξ)`) and `theorem14` are not vacuous, whatever the junk behaviour of `sphereAvg`, `TightOver` or any
other ingredient of `IsWeakExpMetric`.

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.sharpWeak_nonempty_impl` (provider `HigherDimLQGMetric.Assembly.SharpWeakNonempty`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Non-vacuity anchor: the weak class with sharp normalizers at `Q = Q(ξ)` is nonempty. -/
theorem sharpWeak_nonempty :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ D : DistRd d → ContMetric d, IsSharpWeakExpMetric d ξ (distExp d ξ) D :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.sharpWeak_nonempty_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
