import HigherDimLFPP.Frozen.Rd
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Frozen definition: `supDistLU`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): (1.4), l. 40–44
(`sup_{x, y ∈ B_R} |D^γ_h(x, y) − D^{γ₀}_h(x, y)|`) and l. 88 (`‖F‖_R = sup_{x, y ∈ B_R} |F(x, y)|`).
The supremum over the closed ball `B̄_R × B̄_R` (the frozen `HigherDimLQGMetric.TendstoInProbLU` convention; for
continuous functions and every `R` this does not change the meaning of (1.4), which quantifies over all `R`)
of `|F − G|`, computed in `[0, ∞]` (`edist` on `ℝ`), where `⨆` is a complete-lattice supremum: no `sSup`
junk value on `ℝ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- `sup_{x, y ∈ B̄_R} |F(x, y) − G(x, y)|` in `[0, ∞]` (the quantity of [C] (1.4)). -/
def supDistLU (d : ℕ) (R : ℝ) (F G : C(Rd d × Rd d, ℝ)) : ℝ≥0∞ :=
  ⨆ p ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R, edist (F p) (G p)

end HigherDimLQGContinuity
