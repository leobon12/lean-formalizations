import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLFPP.Paths.DistOn

/-!
# Frozen definition: `lfppDist`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M10, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] (1.3), [S] l. 85–88: the LFPP metric `D^ε_h(z, w) = inf_P ∫_0^1 e^{ξ h*_ε(P(t))} |P'(t)| dt` over
piecewise continuously differentiable paths `P : [0,1] → ℝ^d` from `z` to `w`. Reuses HigherDimLFPP's
sealed `lfppDistOn` on `univ` (`HigherDimLFPP/Paths/DistOn.lean`: infimum over `IsPcwC1Path`, a
verbatim copy of the frozen `IsAdmissiblePath` without its endpoint/domain clauses, of the frozen
`lfppLength`), so that block B2's estimates apply to `D^ε` directly (ruling M10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `D^ε_h(z, w) = inf_P ∫_0^1 e^{ξ h*_ε(P(t))} |P'(t)| dt` over piecewise `C¹` paths in `ℝ^d`. -/
def lfppDist {d : ℕ} (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d) (p : Rd d × Rd d) : ℝ :=
  HigherDimLFPP.lfppDistOn ξ (convMollify κ ε h) univ p.1 p.2

end HigherDimLQGMetric
