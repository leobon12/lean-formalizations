import HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Frozen definition: `IsAdmissibleSeed`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): §1, l. 57–58 ("Choose a real, radial function
`κ ∈ C_c^∞(ℝ^d)` with `∫ κ² = 1`") and l. 70–71 ("It need not be nonnegative"). The seed of the convolution kernel
`K` of (1.2) (`HigherDimLQGMetric.convKernel κ`): `HigherDimLFPP.IsLFPPKernel` without its `nonneg` field.
Literal definition; `∫ κ² = 1` is a Bochner integral of a continuous compactly supported function (no junk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS

open HigherDimLFPP (Rd)

/-- The seeds `κ` of the kernel (1.2): real, `C^∞` (`((⊤ : ℕ∞) : WithTop ℕ∞)`, not analytic), compactly
supported, radial, with `∫ κ² = 1`; no sign condition. -/
structure IsAdmissibleSeed {d : ℕ} (κ : Rd d → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ
  hasCompactSupport : HasCompactSupport κ
  radial : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w
  integral_sq : ∫ z, κ z ^ 2 = 1

end HigherDimLFPPAS
