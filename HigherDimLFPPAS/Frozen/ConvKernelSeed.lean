-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLQGMetric.Frozen.ConvKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.CStarAlgebra.Classes
import HigherDimLFPPAS.Implementation.ConvKernelSeed

/-!
# Frozen theorem: `convKernel_seed`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): l. 57–71 ("The kernel `K` is real and radial,
has integral one, [...] It need not be nonnegative"). Sanity anchor for the sealed definitions
`HigherDimLQGMetric.convKernel` / `convTrunc` on the signed carrier of `asConvergence` (their sealed sanity anchor
`convKernel_smooth_integral` covers only nonnegative seeds): for every admissible seed, `K = 𝓕⁻¹ K̂` is real
(the `.re` in `convKernel` discards nothing), smooth (the junk branch of `convTrunc` is never taken) and has
integral one.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.convKernel_seed_impl`, provider
`HigherDimLFPPAS.Implementation.ConvKernelSeed`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped FourierTransform

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Sanity anchor: for every admissible seed, the kernel `K` of (1.2) is real, smooth, with `∫ K = 1`. -/
theorem convKernel_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      (∀ x : Rd d, (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x).im = 0) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.convKernel_seed_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
