/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Random
import InteractingSLE.Spec.Supplement.GW2RootV7Record

/-!
# Concrete normalized clocks, physical observations and stopped samples

Packet PROVE-T14-GW2ROOT2. All definitions use the actual two records.
The sample is killed at the recorded relative capacity and reads the
normalized driver at every live rational time. Its measurability and
reading identity hold everywhere, without geometric or law hypotheses.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootB23

/-- Relative capacity in the chart dilated by `a`, at physical time `t`. -/
def physicalClock (a s t : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  a ^ 2 * (RootZ21.forwardCapacity s t p).toNNReal

/-- The normalized driver and tip at the capacity actually reached at `t`. -/
def physicalObservationRead (a s v t : ℝ≥0) (p : RecData × RecData) : ℝ × ℂ :=
  scaledRelativeObservationRead a s v (physicalClock a s t p) p

/-- The actual normalized driver record, killed at its recorded capacity. -/
def relativeSample (a s v : ℝ≥0) (p : RecData × RecData) : RootV7.DriverRecord :=
  (physicalClock a s v p, fun q =>
    if ((q : ℝ≥0) : ℝ≥0∞) < (physicalClock a s v p : ℝ≥0∞) then
      scaledRelativeDriverRead a s v q p else 0)

theorem measurable_physicalClock (a s t : ℝ≥0) : Measurable (physicalClock a s t) :=
  measurable_const.mul ((RootZ21.measurable_forwardCapacity s t).real_toNNReal)

theorem measurable_physicalObservationRead (a s v t : ℝ≥0) :
    Measurable (physicalObservationRead a s v t) :=
  measurable_scaledRelativeObservationRead_random measurable_id
    (measurable_physicalClock a s t) a s v

theorem measurable_relativeSample (a s v : ℝ≥0) : Measurable (relativeSample a s v) := by
  have hlife := measurable_coe_nnreal_ennreal.comp (measurable_physicalClock a s v)
  exact hlife.prodMk (measurable_pi_iff.mpr fun q =>
    Measurable.ite (measurableSet_lt measurable_const hlife)
      (measurable_scaledRelativeDriverRead a s v q) measurable_const)

/-- The experiment's `record_read` clause is an exact identity for this sample. -/
theorem relativeSample_read (a s v : ℝ≥0) (p : RecData × RecData) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < (relativeSample a s v p).1) :
    (relativeSample a s v p).2 q = scaledRelativeDriverRead a s v q p :=
  ite_eq_left hq

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

private theorem measurable_stageRecords (j : Fin n) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_fst.comp (comap_measurable
    (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
      (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j)

/-- The physical observation is known from the literal retained stage records. -/
theorem measurable_stageSigma_physicalObservationRead (j : Fin n) (a v t : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      physicalObservationRead a s v t
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_physicalObservationRead a s v t).comp
    (measurable_stageRecords hκ h12p βA c₀ h s W ζ spec n j)

/-- The entire killed sample, including its lifetime, is a measurable actual record. -/
theorem measurable_stageSigma_relativeSample (j : Fin n) (a v : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      relativeSample a s v (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_relativeSample a s v).comp
    (measurable_stageRecords hκ h12p βA c₀ h s W ζ spec n j)

variable {Θ : Set ℝ} {Q : Set ℝ≥0}

theorem measurable_rootSigma_physicalObservationRead (r : ScaledRootIdx Θ Q)
    (l : List (EntryIdx Θ Q)) (j : Fin ((entryList l).length + 1)) (a v t : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l] (fun ω =>
      physicalObservationRead a s v t (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_physicalObservationRead hκ h12p βA c₀ h s W ζ _ _ j a v t

theorem measurable_rootSigma_relativeSample (r : ScaledRootIdx Θ Q)
    (l : List (EntryIdx Θ Q)) (j : Fin ((entryList l).length + 1)) (a v : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l] (fun ω =>
      relativeSample a s v (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_relativeSample hκ h12p βA c₀ h s W ζ _ _ j a v

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
