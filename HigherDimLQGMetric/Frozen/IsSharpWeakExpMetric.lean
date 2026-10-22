import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frozen definition: `IsSharpWeakExpMetric`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M5, M13, M14).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 126 ((E2): "the weak scale normalizers can be chosen as `c_r = r^{ξQ}`"), Lemma 10.1 (l. 1494–1513:
strong candidates are weak with normalizers `r^{ξQ}`); rulings M5, M14: the weak class with the sharp
normalizers `c_r = r^{ξQ}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The weak class with the sharp normalizers `c_r = r^{ξQ}`. -/
def IsSharpWeakExpMetric (d : ℕ) (ξ Q : ℝ) (D : DistRd d → ContMetric d) : Prop :=
  IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q))

end HigherDimLQGMetric
