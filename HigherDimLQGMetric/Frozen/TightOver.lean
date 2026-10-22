import HigherDimLQGMetric.Frozen.IsContinuousMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Frozen definition: `TightOver`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 106–108 ("is tight locally uniformly over ... with all limits inducing the Euclidean topology"),
[1] Axiom V ("tight with respect to the local uniform topology ... every subsequential limit is a
continuous metric"): the random continuous functions `X r`, `r ∈ S`, are a.e.-measurable (without this a
non-measurable `X r` would have the junk law `0`, MA0 fidelity note 3), their laws form a tight family on
`C(ℝ^d × ℝ^d, ℝ)`, and every law in the weak closure of the family (each law and every subsequential limit)
is carried by continuous metrics inducing the Euclidean topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The laws of `X r`, `r ∈ S`, are tight and every law in their closure is carried by continuous
metrics inducing the Euclidean topology. -/
def TightOver {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → C(Rd d × Rd d, ℝ)) (S : Set ℝ) : Prop :=
  (∀ r ∈ S, AEMeasurable (X r) P) ∧
  IsTightMeasureSet {μ | ∃ r ∈ S, μ = P.map (X r)} ∧
  ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
    μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)} →
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric D

end HigherDimLQGMetric
