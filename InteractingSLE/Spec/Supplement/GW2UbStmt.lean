/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzSched

/-!
# The stage law in the relative chart, in law-transfer form (the piece for PROVE-GW2-STAGEMEAN, D76)

Packet PROVE-GW2-RELDET (round 38, decision D73 route (ii), with the split of D76). The tip exclusion of the stopped
stage law (`StageLawXSStatement`, the case of a contact at or before the stop) runs on the stage field `Hr` read in the
relative stage chart (`StageInst.chartX`, the counterflow tip at `∞`). Its first step is the stage law as a flow-line
statement in that chart: given the stage record, `Hr` is the GFF with the boundary data of the record's word, so its
flow line from `0` (the decoded canonical driver code of `(β rec, Hr)`) is an `SLE_κ(ρ)` evolution of that word, and
every event null for all such flow lines is null for the stage.

**`StageFieldLawXStatement`** is that transfer, on the field: an event of `(word, field)` that is null for every GFF
with the data of a sorted word is null on the stage's record event. It is the regular-conditional-law form of
`OpenLinesX.condGFF` (round 28's `condGFF_of_mean0`). PROVE-GW2-STAGEMEAN proves it (D76); RELDET consumes it as
stated, with `A = {(b, g) | (b, Fd (b, g)) ∈ Bad}` for a canonical driver code `Fd` and the tip-exclusion event `Bad`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Sde GW2Sdh Supp8.GB6

/-- **The stage field law in the relative chart, in law-transfer form** (for PROVE-GW2-STAGEMEAN, D76). For a stage
instance with the open lines inputs (whose `condGFF` is the conditional GFF law of the stage field given the stage
record), every measurable event of `(word, field)` that is null for every GFF with the data of a sorted word is null
for `(β (srecX), Hr)` on the stage's record event. -/
def StageFieldLawXStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) (hWm : ∀ t, Measurable (I.W t)),
    OpenLinesX I c r l x₀ hWm → Measurable I.β → (∀ y ∈ I.E, (I.β y).IsSorted) → Measurable I.Hr →
    ∀ A : Set (BoundaryWord × DistOn upperHalfPlaneOpens), MeasurableSet A →
    (∀ b : BoundaryWord, b.IsSorted → ∀ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ →
      IsGFFWithBoundaryData μ id b.fn b.jumps → ∀ᵐ g ∂μ, (b, g) ∉ A) →
    ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → (I.β (I.srecX c r l x₀ ω), I.Hr ω) ∉ A

end InteractingSLE.Theorem14.GW2Rd
