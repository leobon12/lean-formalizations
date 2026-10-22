-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.SphereAvg
import HigherDimLQGMetric.Frozen.IsLGFPlusCont
import HigherDimLQGMetric.Assembly.SphereAvgSpec

/-!
# Frozen theorem: `sphereAvg_spec`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57–59 (spherical averages `h_r(z)`), [1] §1.2 (the spherical average process of an LGF plus a
continuous function). Characterization anchor for the `limUnder` in `sphereAvg`: for every LGF plus a
continuous function, at every fixed `r > 0` and `z`, the mollified sphere averages converge almost surely,
so `sphereAvg` is their limit and not the junk value (this is the meaning used in Definition 1.3's
normalization `e^{-ξ h_r(0)}` and in `h_1(0) = 0`; MA1 item 1, MA4 note 4).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.sphereAvg_spec_impl` (provider `HigherDimLQGMetric.Assembly.SphereAvgSpec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Characterization anchor: for an LGF plus a continuous function, the limit defining `h_r(z)` exists a.s. -/
theorem sphereAvg_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.sphereAvg_spec_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
