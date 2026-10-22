import HigherDimLQGMetric.Frozen.IsWholeSpaceLGF
import HigherDimLQGMetric.Frozen.OfCont
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Frozen definition: `IsLGFPlusBddCont`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 108 ("For an LGF plus a bounded continuous function, require this for all `r > 0`"), l. 1576,
[1] Axiom V and Theorem 1.3: as `IsLGFPlusCont`, with every realization of `f` bounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h` is a whole-space LGF plus a (possibly random, possibly dependent) bounded continuous
function. -/
def IsLGFPlusBddCont {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    (P : Measure Ω) : Prop :=
  Measurable h ∧ ∃ f : Ω → C(Rd d, ℝ), Measurable f ∧ (∀ ω, ∃ M : ℝ, ∀ z, |f ω z| ≤ M) ∧
    IsWholeSpaceLGF (fun ω => h ω - ofCont (f ω)) P

end HigherDimLQGMetric
