-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLFPPAS.Implementation.Assumption11Nonvacuous

/-!
# Frozen theorem: `assumption11_nonvacuous`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L1, L6, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): Assumption 1.1, l. 90–116, for the seeds of
l. 57–71 and the field of l. 49–55.
Non-vacuity anchor of `asConvergence` (ruling L1: "the non-vacuity of Assumption 1.1"): for `d ≥ 3` and every
subcritical `ξ > 0` there is one assignment `D` such that every nonnegative seed (`HigherDimLFPP.IsLFPPKernel`) is
an admissible seed and `D` satisfies Assumption 1.1 for it and for every normalized LGF on every probability space.
With the sealed `HigherDimLQGMetric.subcritical_nonempty` (the subcritical range contains `(0, ξ₀)`),
`HigherDimLFPP.field_exists` (nonnegative seeds exist) and `HigherDimLQGMetric.normLGFLaw_spec` (a normalized LGF
exists) every hypothesis of `asConvergence` is satisfiable. Assumption 1.1 for sign-changing seeds is not
asserted (no proof is available, ruling M6 of HigherDimLQGMetric).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.assumption11_nonvacuous_impl`, provider
`HigherDimLFPPAS.Implementation.Assumption11Nonvacuous`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Non-vacuity of Assumption 1.1** for nonnegative seeds, with one assignment for all seeds and fields. -/
theorem assumption11_nonvacuous :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      IsAdmissibleSeed κ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → Assumption11 d ξ κ D P h :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.assumption11_nonvacuous_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
