import HigherDimLQGMetric.Frozen.NormLGFLaw
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLFPP.Frozen.E1

/-!
# Frozen definition: `aEps`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 1572–1574 (Corollary 10.4: "normalize by `a_ε`, a median of `D^ε_h(0, e₁)` for `h_1(0) = 0`"),
[1] (1.5): `𝔞_ε`, the lower median `inf {m : P[D^ε_h(0, e₁) ≤ m] ≥ 1/2}` of `D^ε_h(0, e₁)` under the law
of the normalized LGF (the lower median is a median; any median is allowed by the source).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- `𝔞_ε`: the lower median of `D^ε_h(0, e₁)` under the law of the normalized LGF. -/
def aEps {d : ℕ} (κ : Rd d → ℝ) (ξ ε : ℝ) : ℝ :=
  sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ m}}

end HigherDimLQGMetric
