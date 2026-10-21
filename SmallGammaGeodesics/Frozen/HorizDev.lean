import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.Basic

/-!
# Frozen definition: `horizDev`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, (1.11): `sup_{t ∈ [0,1]} |Re P_γ(t) − t| / γ^{2/3}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SmallGammaGeodesics

/-- `sup_{t ∈ [0,1]} |Re η(t) − t| / s` (source (1.11) with `s = γ^{2/3}`). -/
def horizDev (s : ℝ) (η : C(unitInterval, ℂ)) : ℝ :=
  ⨆ t : unitInterval, |(η t).re - (t : ℝ)| / s

end SmallGammaGeodesics
