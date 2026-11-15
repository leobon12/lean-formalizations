/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafRetTrace
import InteractingSLE.Spec.Coupling.WFSLeafRetMean

/-!
# Retained-set data from marked locality and countable freezing limits

`HasRetainedTraceLimits` isolates the two mathematical inputs at a cutoff:
the trace closure is local with the history among its marks, and Borel
frozen-mean approximants converge to its germ conditional means on the
countable family `comb c`. The set reader, its geometry, the distribution
version and its pairings at every test are constructed here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField LawUnique
open QuantumZipper (H)

/-- The locality and scalar freezing inputs at a recorded cutoff. This is a
named proposition, not a claim that these inputs follow from a through coupling. -/
def HasRetainedTraceLimits {nL nR : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (Y : Ω → HistorySpace nL nR)
    (a : CoordJ → ℕ → HistorySpace nL nR → ℝ) : Prop :=
  IsHistoryAvoidanceLocal (MeasurableSpace.comap Y inferInstance)
    (retainedTraceReader ∘ Y) h P ∧
  ∀ c : CoordJ, ∀ᵐ ω ∂P, Tendsto (fun n => a c n (Y ω)) atTop
    (𝓝 ((P[fun ω' => h ω' (comb upperHalfPlaneOpens c) |
      germSigma (retainedTraceReader ∘ Y) h ⊔ MeasurableSpace.comap Y inferInstance]) ω))

/-- All the per-coupling clauses needed by `hRetained`, with the set and mean
readers now fixed explicitly. -/
theorem retainedTraceData_of_limits
    {nL nR : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {a : CoordJ → ℕ → HistorySpace nL nR → ℝ} (hL : HasRetainedTraceLimits P h Y a) :
    (∀ᵐ ω ∂P, retainedTraceReader (Y ω) ⊆ H ∧ IsOpen (H \ retainedTraceReader (Y ω))) ∧
    IsHistoryAvoidanceLocal (MeasurableSpace.comap Y inferInstance)
      (retainedTraceReader ∘ Y) h P ∧
    ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (retainedTraceReader ∘ Y) h P g ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, g ω φ = retainedMeanReader a (Y ω) φ := by
  have hAc : ∀ᵐ ω ∂P, retainedTraceReader (Y ω) ⊆ H ∧ IsOpen (H \ retainedTraceReader (Y ω)) :=
    Eventually.of_forall fun ω => retainedTraceReader_geometry (Y ω)
  obtain ⟨g, hg, heq⟩ := exists_localSetMean_eq_retainedMeanReader hh hY
    (measurable_retainedTraceReader.comp hY) hAc hL.1 hL.2
  exact ⟨hAc, hL.1, g, hg, fun φ => heq.mono fun ω hω => congrArg (fun T => T φ) hω⟩

end InteractingSLE.WFS
