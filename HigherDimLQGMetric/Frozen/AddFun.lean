import HigherDimLQGMetric.Frozen.OfCont

/-!
# Frozen definition: `addFun`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 64 ("LGF plus a ... continuous function"), l. 69–74 (Axiom (III), `D_{h+f}`): `h + f`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h + f` for a continuous function `f`. -/
def addFun {d : ℕ} (h : DistRd d) (f : C(Rd d, ℝ)) : DistRd d := h + ofCont f

end HigherDimLQGMetric
