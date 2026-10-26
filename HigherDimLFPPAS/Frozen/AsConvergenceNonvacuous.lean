-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLFPPAS.Implementation.AsConvergenceNonvacuous

/-!
# Frozen theorem: `asConvergence_nonvacuous`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L1, L6, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): the hypotheses of Theorem 1.2 (l. 118–125):
`d ≥ 3`, `ξ > 0` (l. 49), the normalized LGF (l. 49–55), the seed (l. 57–71) and Assumption 1.1 (l. 90–116).
One-statement closure witness (ruling L1: "the non-vacuity of Assumption 1.1"): for `d ≥ 3` there is `ξ₀ > 0` such
that for every `ξ ∈ (0, ξ₀)` all hypotheses of `asConvergence` hold simultaneously for some seed, assignment,
probability space and normalized LGF.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.asConvergence_nonvacuous_impl`, provider
`HigherDimLFPPAS.Implementation.AsConvergenceNonvacuous`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **The hypotheses of Theorem 1.2 are jointly satisfiable** for every `d ≥ 3` and all small `ξ > 0`. -/
theorem asConvergence_nonvacuous :
    ∀ d : ℕ, 3 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Set.Ioo (0 : ℝ) ξ₀,
      ∃ (κ : Rd d → ℝ) (D : DistRd d → ContMetric d) (Ω : Type) (_ : MeasurableSpace Ω)
        (P : Measure Ω) (h : Ω → DistRd d),
        IsAdmissibleSeed κ ∧ IsProbabilityMeasure P ∧ IsNormalizedLGF h P ∧ Assumption11 d ξ κ D P h :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.asConvergence_nonvacuous_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
