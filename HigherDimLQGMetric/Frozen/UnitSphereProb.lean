import HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Frozen definition: `unitSphereProb`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57–59 (spherical averages `h_r(z)`): the uniform probability measure on the unit sphere of
`ℝ^d`, as a measure on `ℝ^d` (mathlib's `Measure.toSphere` of Lebesgue measure, pushed forward and
normalized; rotation invariant).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The uniform probability measure on the unit sphere of `ℝ^d` (as a measure on `ℝ^d`). -/
def unitSphereProb (d : ℕ) : Measure (Rd d) :=
  ((volume : Measure (Rd d)).toSphere univ)⁻¹ •
    ((volume : Measure (Rd d)).toSphere.map (Subtype.val))

end HigherDimLQGMetric
