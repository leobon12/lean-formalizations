import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.Basic

/-!
# Frozen definition: `maxDev`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, §1: `M_γ = max_{z ∈ P_γ} dist(z, [0,1])`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SmallGammaGeodesics

/-- `M(η) = max_{t ∈ [0,1]} dist(η(t), [0,1])` (source §1, `M_γ` for `η = P_γ`). The supremum of a
continuous function on the compact `[0,1]` is attained, so there is no junk value. -/
def maxDev (η : C(unitInterval, ℂ)) : ℝ :=
  ⨆ t : unitInterval, Metric.infDist (η t) (segment ℝ (0 : ℂ) 1)

end SmallGammaGeodesics
