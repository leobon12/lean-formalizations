-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLQGMetric.Assembly.ConvMollifySpec

/-!
# Frozen theorem: `convMollify_spec`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] (1.2) (`h*_ε = h * K_ε`), [S] l. 85–90; MA1 erratum E-2 ("the limit must exist a.s. or the clause
becomes false"). Characterization anchor for the `limUnder` in `convMollify`: for every nonnegative
admissible kernel, every LGF plus a bounded continuous function and every `ε > 0`, almost surely the
truncated pairings converge at every point `z`, so the LFPP field `h*_ε` of Theorem 1.2 is the genuine
convolution and not the junk value.

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.convMollify_spec_impl` (provider `HigherDimLQGMetric.Assembly.ConvMollifySpec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Characterization anchor: for an LGF plus a bounded continuous function, `h * K_ε` exists a.s. everywhere. -/
theorem convMollify_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.convMollify_spec_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
