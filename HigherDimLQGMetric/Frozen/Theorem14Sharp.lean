-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Assembly.Theorem14Sharp

/-!
# Frozen theorem: `theorem14Sharp`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M5, M13, M14).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Theorem 1.4 (l. 111–112) in the weak class with the sharp normalizers `c_r = r^{ξQ}` ((E2), l. 126;
the form in which §§2–9 prove it, MA0 finding P3), for every `d ≥ 3`, `ξ > 0`, `Q > √(2d)`; conclusion
as proved at l. 1486–1488 ("`D̃_h = c_* D_h` simultaneously for all points. Simultaneous Weyl scaling
extends it to every continuous perturbation with the same constant"). Phase A anchor (ruling M5).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.theorem14Sharp_impl` (provider `HigherDimLQGMetric.Assembly.Theorem14Sharp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Phase A** (ruling M5): uniqueness in the weak class with the sharp normalizers `c_r = r^{ξQ}`: any
two such assignments are deterministic positive multiples of one another, a.s. simultaneously for all
points and all continuous perturbations of every LGF-plus-continuous input. -/
theorem theorem14Sharp :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsSharpWeakExpMetric d ξ Q D → IsSharpWeakExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.theorem14Sharp_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
