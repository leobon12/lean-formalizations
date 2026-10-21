import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Frozen definition: `rescaledPath`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, (1.10): `X_γ(t) = (P_γ(t) − t)/γ^{2/3}`, as an element of `C([0,1], ℂ)` (ℂ ≅ ℝ²).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SmallGammaGeodesics

/-- `X(t) = (η(t) − t)/s` (source (1.10) with `s = γ^{2/3}`), a continuous path `[0,1] → ℂ`. -/
def rescaledPath (s : ℝ) (η : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  ⟨fun t => (η t - ((t : ℝ) : ℂ)) / (s : ℂ), by fun_prop⟩

end SmallGammaGeodesics
