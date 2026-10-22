import HigherDimLQGMetric.Frozen.ConvTrunc
import HigherDimLQGMetric.Frozen.DistRd

/-!
# Frozen definition: `convMollify`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] (1.2), [S] l. 85–90: `h*_ε(z) = (h * K_ε)(z) := lim_n ⟨h, K_ε(z - ·) χ_n(· - z)⟩` (`limUnder`; junk
value an unspecified constant when the limit does not exist). The frozen characterization
`convMollify_spec` states that for an LGF plus a bounded continuous function, for every `ε > 0`, a.s.
the limit exists simultaneously at every `z` (MA1 erratum E-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h*_ε(z) = (h * K_ε)(z) := lim_n ⟨h, K_ε(z - ·) χ_n(· - z)⟩` ([1] (1.2)). -/
def convMollify {d : ℕ} (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d) (z : Rd d) : ℝ :=
  limUnder atTop fun n : ℕ => h (convTrunc κ ε z n)

end HigherDimLQGMetric
