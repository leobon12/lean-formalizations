-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.ConvKernel
import HigherDimLFPP.Frozen.IsLFPPKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import HigherDimLQGMetric.Assembly.ConvKernelSmoothIntegral

/-!
# Frozen theorem: `convKernel_smooth_integral`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] Remark 1.1 and Lemma 2.9 ("`K` is a radially symmetric, real-valued function with `∫ K = 1`"); [S] l.
89–90; rulings M6, M7. Sanity anchor (MA0 fidelity note 5): for every nonnegative admissible kernel, `K` is
smooth (so the `dite` in `convTrunc` takes its genuine branch) and has unit mass (so `𝓕⁻¹ K̂` is not the
junk value of a non-integrable symbol).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.convKernel_smooth_integral_impl` (provider `HigherDimLQGMetric.Assembly.ConvKernelSmoothIntegral`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Sanity anchor: the kernel `K` of [1, Remark 1.1] is smooth with `∫ K = 1`. -/
theorem convKernel_smooth_integral :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.convKernel_smooth_integral_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
