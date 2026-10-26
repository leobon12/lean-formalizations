-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLFPPAS.Implementation.ConvMollifySpecSeed

/-!
# Frozen theorem: `convMollify_spec_seed`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): l. 71 ("`h*_ε = h ∗ K_ε`"). Characterization
anchor of the sealed `HigherDimLQGMetric.convMollify` (a `limUnder`) on the signed carrier of `asConvergence`
(the sealed `convMollify_spec` covers only nonnegative seeds), verbatim with `IsAdmissibleSeed` for
`HigherDimLFPP.IsLFPPKernel`: for an LGF plus a bounded continuous function, `h * K_ε` exists a.s. everywhere.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.convMollify_spec_seed_impl`, provider
`HigherDimLFPPAS.Implementation.ConvMollifySpecSeed`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Characterization anchor: for every admissible seed and an LGF plus a bounded continuous function,
`h * K_ε` exists a.s. everywhere. -/
theorem convMollify_spec_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.convMollify_spec_seed_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
