import HigherDimLQGMetric.Frozen.KernelSymbol
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Frozen definition: `convKernel`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 85–90, [1] Remark 1.1: `K = 𝓕⁻¹ K̂` (real part; `K̂` is real and even, so `K` is real). The
frozen sanity theorem `convKernel_smooth_integral` states that `K` is smooth with `∫ K = 1` for every
admissible kernel (no junk from a non-integrable symbol).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `K = 𝓕⁻¹ K̂` ([1, Remark 1.1]; real part). -/
def convKernel {d : ℕ} (κ : Rd d → ℝ) (x : Rd d) : ℝ :=
  (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x).re

end HigherDimLQGMetric
