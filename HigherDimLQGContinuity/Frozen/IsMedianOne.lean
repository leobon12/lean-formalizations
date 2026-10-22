import HigherDimLQGMetric.Frozen.NormLGFLaw
import HigherDimLQGMetric.Frozen.ContMetric
import HigherDimLFPP.Frozen.E1

/-!
# Frozen definition: `IsMedianOne`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): (1.2), l. 32–34 ("Normalize the γ-LQG metric
by `med D^γ_h(0, e₁) = 1`"), for the field of l. 17–18 (the whole-space LGF with average zero on the unit
sphere, whose law is the frozen `HigherDimLQGMetric.normLGFLaw d`), and l. 1302–1307 (the unit-distance median
is unique, [8, Lemma 10.3]). `1` is a median of `E_h(0, e₁)` when `h` has the law `normLGFLaw d`:
`P[E_h(0, e₁) ≤ 1] ≥ 1/2` and `P[E_h(0, e₁) ≥ 1] ≥ 1/2` (the convention of `LQGMetric.IsMedian`).
Set form under `normLGFLaw d` (ruling N4): no `Measure.map`, hence no junk law for a non-measurable `E`; the
two sets are measured by the outer measure, which is the measure for every measurable `E`, in particular for
every strong assignment (`IsStrongExpMetric.measurable`). `normLGFLaw` is a `Classical.choose` with junk value
`0`; the sealed `HigherDimLQGMetric.normLGFLaw_spec` excludes the junk branch for `d ≥ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- `1` is a median of `E_h(0, e₁)` when `h` has the law `normLGFLaw d` of the LGF normalized by
`h_1(0) = 0`: both closed half-lines at `1` have probability at least `1/2`. -/
def IsMedianOne (d : ℕ) (E : DistRd d → ContMetric d) : Prop :=
  (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {g | (E g).1 (0, e₁ d) ≤ 1} ∧
    (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {g | 1 ≤ (E g).1 (0, e₁ d)}

end HigherDimLQGContinuity
