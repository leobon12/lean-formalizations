import HigherDimLQGMetric.Frozen.DistRd
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Frozen definition: `ofCont`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 64, 69–74: a continuous function `f` as the distribution `φ ↦ ∫ f φ` (mathlib's
`Distribution.ofFun`, whose zero branch for non-locally-integrable `f` is never taken: continuous
functions are locally integrable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The distribution `φ ↦ ∫ f φ` of a continuous function `f` on `ℝ^d`. -/
def ofCont {d : ℕ} (f : C(Rd d, ℝ)) : DistRd d := Distribution.ofFun ⊤ (⇑f) volume ⊤

end HigherDimLQGMetric
