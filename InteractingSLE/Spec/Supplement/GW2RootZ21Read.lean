/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Image
import InteractingSLE.Spec.Supplement.GW2JDetR4Driver
import InteractingSLE.Spec.Supplement.GW2RootU19Observe

/-!
# A total Borel forward capacity reader from two stopped records

Packet PROVE-T14-GW2ROOT2. Its inputs are the retained counterflow
record and one physical flow-piece record. The reader is measurable in
the actual retained stage, at every sample and at any measurable cutoff.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- The visible forward image of the physical hull read from two records. -/
def forwardHull (s t : ℝ≥0) (p : RecData × RecData) : Set ℂ :=
  relMap (rdrv p.1) s ''
    (QuantumZipper.fwdHull (rdrv p.2) t ∩ relDomain (rdrv p.1) s)

/-- Half the grid capacity of that actual visible forward image. -/
def forwardCapacity (s t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (WholeField.hcapHit (forwardHull s t p)).toReal / 2

/-- Hitting measurability also holds at a measurable physical cutoff. -/
theorem measurable_forwardHull_random {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable[mΩ, hittingSigma] fun ω => forwardHull s (t ω) (p ω) :=
  measurable_image_relMap s (measurable_fst.comp hp)
    (GW2JDetR4.measurable_fwdHull_rdrv_time (measurable_snd.comp hp) ht)

theorem measurable_forwardCapacity_random {Ω : Type*} [MeasurableSpace Ω]
    (s : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable fun ω => forwardCapacity s (t ω) (p ω) :=
  ((WholeField.measurable_hcapHit.comp
    (measurable_forwardHull_random s hp ht)).ennreal_toReal).div_const 2

theorem measurable_forwardCapacity (s t : ℝ≥0) : Measurable (forwardCapacity s t) :=
  measurable_forwardCapacity_random s measurable_id measurable_const

theorem forwardCapacity_nonneg (s t : ℝ≥0) (p : RecData × RecData) :
    0 ≤ forwardCapacity s t p := div_nonneg ENNReal.toReal_nonneg (by norm_num)

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

/-- The concrete forward capacity reader is observable in the exact
retained stage. No ambient measurable space or source regularity is needed. -/
theorem measurable_stageSigma_forwardCapacity (j : Fin n) (t : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W' ζ' spec n]
      (fun ω => forwardCapacity s t
        (cfRec s W' ζ' ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_forwardCapacity s t).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W' ζ' spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W' ζ' spec n j))

/-- The same observable reader in the original root-test sigma-algebra. -/
theorem measurable_rootSigma_forwardCapacity {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (t : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r l]
      (fun ω => forwardCapacity s t (cfRec s W' ζ' ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_forwardCapacity hκ h12p βA c₀ h s W' ζ' _ _ j t

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21
