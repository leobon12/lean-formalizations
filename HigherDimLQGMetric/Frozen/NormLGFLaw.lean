import HigherDimLQGMetric.Frozen.IsNormalizedLGF

/-!
# Frozen definition: `normLGFLaw`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57, 1573 ("for `h_1(0) = 0`"), [1] (1.5): the law on `𝒟'(ℝ^d)` of the LGF normalized by
`h_1(0) = 0` (`Classical.choose`; junk `0`). The frozen characterization `normLGFLaw_spec` states that for
`d ≥ 2` it is a probability measure, it is the law of a normalized LGF, and it is the only such law, so
the choice is canonical.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

open Classical in
/-- The law of the LGF normalized by `h_1(0) = 0` (junk `0` if none exists; excluded for `d ≥ 2` by
`normLGFLaw_spec`). -/
def normLGFLaw (d : ℕ) : Measure (DistRd d) :=
  if hμ : ∃ μ : Measure (DistRd d), IsProbabilityMeasure μ ∧ IsNormalizedLGF id μ then hμ.choose
  else 0

end HigherDimLQGMetric
