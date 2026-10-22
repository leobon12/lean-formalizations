import HigherDimLQGMetric.Frozen.IsWholeSpaceLGF
import HigherDimLQGMetric.Frozen.OfCont
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Frozen definition: `IsLGFPlusCont`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 63–64 ("whenever the input is a whole-space LGF plus a possibly random continuous function"),
[1] §1.2 ("one can couple `h` with a random continuous function `f` such that the law of `h - f` is that
of a whole-space LGF"): `h - f` is an LGF for a measurable random continuous `f` on the same probability
space (arbitrary dependence on `h`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h` is a whole-space LGF plus a (possibly random, possibly dependent) continuous function. -/
def IsLGFPlusCont {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    (P : Measure Ω) : Prop :=
  Measurable h ∧ ∃ f : Ω → C(Rd d, ℝ), Measurable f ∧
    IsWholeSpaceLGF (fun ω => h ω - ofCont (f ω)) P

end HigherDimLQGMetric
