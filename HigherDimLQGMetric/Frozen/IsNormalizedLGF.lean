import HigherDimLQGMetric.Frozen.IsWholeSpaceLGF
import HigherDimLQGMetric.Frozen.SphereAvg

/-!
# Frozen definition: `IsNormalizedLGF`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57 ("We choose `h_1(0) = 0` when a representative is needed"), l. 1573 (Corollary 10.4): an LGF
normalized by its unit-sphere average at the origin.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h` is a whole-space LGF normalized so that `h_1(0) = 0` almost surely. -/
def IsNormalizedLGF {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    (P : Measure Ω) : Prop :=
  IsWholeSpaceLGF h P ∧ ∀ᵐ ω ∂P, sphereAvg (h ω) 1 0 = 0

end HigherDimLQGMetric
