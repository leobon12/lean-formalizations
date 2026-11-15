/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Prefix
import InteractingSLE.Spec.Restart.ClockInv

/-!
# A Borel inverse of the actual forward capacity clock

Packet PROVE-T14-GW2ROOT2. The landed rational-supremum inverse clock
is measurable on the complete record space. Its inverse identity is
proved from the original traces on every protected prefix.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open Exist Staged StagedLaw Restart Supp8.GB6

/-- The physical time of a relative capacity level, read from two records
and capped at a prescribed physical recording horizon. -/
def forwardClockInverse (s v u : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  invClock (fun t => forwardCapacity s t p) (v : ℝ≥0∞) u

theorem measurable_forwardClockInverse (s v u : ℝ≥0) :
    Measurable (forwardClockInverse s v u) := by
  classical
  unfold forwardClockInverse invClock
  refine Measurable.iSup fun q : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt (measurable_forwardCapacity s _) measurable_const))

/-- On a protected source prefix the concrete inverse is within the
retained physical horizon and gives the exact attained relative level.
No clock normalization, regularity or inverse identity is assumed. -/
theorem forwardClockInverse_spec_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ QuantumZipper.H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    (u : ℝ≥0)
    (hu : (u : ℝ) ≤ forwardCapacity s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    forwardClockInverse s v u p ≤ v ∧
      forwardCapacity s (forwardClockInverse s v u p) p = u := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let a := fun t => forwardCapacity s t p
  obtain ⟨h0, hm, hc⟩ := forwardCapacity_regular_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) := by
    refine ⟨h0, ?_, ?_, fun h => (ENNReal.coe_ne_top h).elim⟩
    · rwa [hset]
    · rwa [hset]
  have hu' : (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞) := by
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hu
  have hh := ha.invClock_spec hu'
  exact ⟨ENNReal.coe_le_coe.mp hh.1, hh.2⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21
