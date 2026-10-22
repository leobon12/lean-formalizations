import HigherDimLQGMetric.Frozen.AddFun

/-!
# Frozen definition: `addConst`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 76–78 (Axiom (IV), `h(r·+z) + Q log r`): `h + c` for a constant `c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h + c` for a constant `c`. -/
def addConst {d : ℕ} (h : DistRd d) (c : ℝ) : DistRd d :=
  addFun h (ContinuousMap.const (Rd d) c)

end HigherDimLQGMetric
