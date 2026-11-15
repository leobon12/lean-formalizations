/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE26Clock

/-!
# Measurable crossing gates and actual gated observations

Packet PROVE-T14-GW2ROOT2. The gate reads only rational physical times
strictly earlier than the query. The query itself may equal the record's
successful cutoff. No future crossing time is revealed by this reader.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootD25

/-- A past crossing, detected from live rational physical observations. -/
def crossedBefore (a s v q : ℝ≥0) : Set (RecData × RecData) :=
  {p | ∃ r : ℚ≥0, (r : ℝ≥0) < q ∧ (r : ℝ≥0) < v ∧
    2 < (physicalObservationRead a s v r p).1}

/-- The actual pair observed only after the detected crossing. -/
def crossedObservationRead (a s v q : ℝ≥0) (p : RecData × RecData) : ℝ × ℂ :=
  open scoped Classical in
  if p ∈ crossedBefore a s v q then physicalObservationRead a s v q p else (0, 0)

/-- Also impose a specified finite physical failure cutoff. -/
def cutoffObservationRead (a s v F q : ℝ≥0) (p : RecData × RecData) : ℝ × ℂ :=
  if q < F then crossedObservationRead a s v q p else (0, 0)

theorem measurableSet_crossedBefore (a s v q : ℝ≥0) :
    MeasurableSet (crossedBefore a s v q) := by
  have heq : crossedBefore a s v q = ⋃ r : ℚ≥0,
      {p | (r : ℝ≥0) < q ∧ (r : ℝ≥0) < v ∧
        2 < (physicalObservationRead a s v r p).1} := by
    ext p
    simp only [crossedBefore, mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurableSet_lt measurable_const
      ((measurable_physicalObservationRead a s v r).fst)))

theorem measurable_crossedObservationRead (a s v q : ℝ≥0) :
    Measurable (crossedObservationRead a s v q) :=
  Measurable.ite (measurableSet_crossedBefore a s v q)
    (measurable_physicalObservationRead a s v q) measurable_const

theorem measurable_cutoffObservationRead (a s v F q : ℝ≥0) :
    Measurable (cutoffObservationRead a s v F q) := by
  change Measurable fun p => if q < F then crossedObservationRead a s v q p else (0, 0)
  by_cases hq : q < F
  · simpa only [hq, ↓reduceIte] using
      measurable_crossedObservationRead a s v q
  · simpa only [hq, ↓reduceIte] using
      (measurable_const : Measurable fun _ : RecData × RecData => ((0, 0) : ℝ × ℂ))

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

/-- Exact observability of both gates in the literal retained stage records. -/
theorem measurable_stageSigma_cutoffObservationRead (j : Fin n) (a v F q : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      cutoffObservationRead a s v F q
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_cutoffObservationRead a s v F q).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

theorem measurable_rootSigma_cutoffObservationRead {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (a v F q : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l] (fun ω =>
      cutoffObservationRead a s v F q (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_cutoffObservationRead hκ h12p βA c₀ h s W ζ _ _ j a v F q

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
