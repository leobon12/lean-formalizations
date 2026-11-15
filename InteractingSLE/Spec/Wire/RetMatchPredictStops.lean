/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchPredictSup

/-!
# Positive bounded announcing times in the killed driving filtration

The first positive member of the given announcing sequence can be selected
using events measurable at time zero. Taking maxima with this member, then
capping by `n + 1`, gives a positive bounded announcing sequence.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchPredict

open Restart.RetAux79

/-- The given announcing sequence first becomes positive at index `n`. -/
def firstPositiveEvent {κ θ : ℝ} (M : StoppedTypeModel κ θ) (n : ℕ) : Set M.space :=
  {ω | 0 < M.data.driveStops n ω ∧ ∀ k < n, M.data.driveStops k ω = 0}

theorem measurableSet_firstPositiveEvent {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (n : ℕ) :
    MeasurableSet[drivingFiltration M.law M.data.killedMeas 0] (firstPositiveEvent M n) := by
  have hp : MeasurableSet[drivingFiltration M.law M.data.killedMeas 0]
      {ω | 0 < M.data.driveStops n ω} := by
    have he : {ω | 0 < M.data.driveStops n ω} =
        {ω | M.data.driveStops n ω ≤ (0 : WithTop ℝ≥0)}ᶜ := by
      ext ω
      change (0 : WithTop ℝ≥0) < M.data.driveStops n ω ↔
        ¬ M.data.driveStops n ω ≤ (0 : WithTop ℝ≥0)
      exact lt_iff_not_ge
    rw [he]
    exact (M.data.driveStopping n 0).compl
  unfold firstPositiveEvent
  rw [Set.ofPred_and]
  refine hp.inter ?_
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => by
    simpa only [WithTop.coe_zero, le_zero_iff] using M.data.driveStopping k 0

theorem firstPositiveEvent_unique {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {ω : M.space} {n k : ℕ} (hn : ω ∈ firstPositiveEvent M n)
    (hk : ω ∈ firstPositiveEvent M k) : n = k := by
  rcases lt_trichotomy n k with h | h | h
  · exact ((ne_of_gt hn.1) (hk.2 n h)).elim
  · exact h
  · exact ((ne_of_gt hk.1) (hn.2 k h)).elim

open Classical in
/-- First positive announcing time; infinity if all members vanish. -/
def firstPositiveDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    M.space → WithTop ℝ≥0 :=
  fun ω => ⨅ n, if ω ∈ firstPositiveEvent M n then M.data.driveStops n ω else ⊤

theorem firstPositiveDriveStop_eq {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {ω : M.space} {n : ℕ} (hn : ω ∈ firstPositiveEvent M n) :
    firstPositiveDriveStop M ω = M.data.driveStops n ω := by
  classical
  unfold firstPositiveDriveStop
  refine le_antisymm ?_ (le_iInf fun k => ?_)
  · simpa only [ite_eq_left hn] using
      (iInf_le (fun k => if ω ∈ firstPositiveEvent M k then M.data.driveStops k ω else ⊤) n)
  · by_cases hk : ω ∈ firstPositiveEvent M k
    · rw [ite_eq_left hk, ← firstPositiveEvent_unique M hn hk]
    · rw [ite_eq_right hk]
      exact le_top

theorem isStoppingTime_firstPositiveDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    IsStoppingTime (drivingFiltration M.law M.data.killedMeas) (firstPositiveDriveStop M) := by
  classical
  have : (drivingFiltration M.law M.data.killedMeas).IsRightContinuous := by
    unfold drivingFiltration
    infer_instance
  apply IsStoppingTime.iInf
  intro n
  exact (M.data.driveStopping n).piecewise_of_le
    (fun _ => MeasurableSet.const _)
    (fun _ => zero_le) (fun _ => zero_le)
    (measurableSet_firstPositiveEvent M n)

theorem ae_firstPositiveDriveStop_bounds {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    ∀ᵐ ω ∂M.law, 0 < firstPositiveDriveStop M ω ∧
      (firstPositiveDriveStop M ω : ℝ≥0∞) < M.data.life ω := by
  classical
  filter_upwards [M.data.lifePos, M.data.driveLt, M.data.driveLimit] with ω hV hlt hlim
  have hex : ∃ n, 0 < M.data.driveStops n ω := by
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hV)).exists
    exact ⟨n, hn⟩
  have hn : ω ∈ firstPositiveEvent M (Nat.find hex) := by
    refine ⟨Nat.find_spec hex, fun k hk => ?_⟩
    exact le_antisymm (le_of_not_gt (Nat.find_min hex hk)) zero_le
  rw [firstPositiveDriveStop_eq M hn]
  exact ⟨Nat.find_spec hex, hlt _⟩

/-- Positive bounded replacement of the model's original announcing stops. -/
def boundedDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ) (n : ℕ) :
    M.space → WithTop ℝ≥0 :=
  fun ω => min (max (M.data.driveStops n ω) (firstPositiveDriveStop M ω))
    (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0)

theorem isStoppingTime_boundedDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (n : ℕ) : IsStoppingTime (drivingFiltration M.law M.data.killedMeas)
      (boundedDriveStop M n) :=
  ((M.data.driveStopping n).max (isStoppingTime_firstPositiveDriveStop M)).min_const _

theorem boundedDriveStop_le {κ θ : ℝ} (M : StoppedTypeModel κ θ) (n : ℕ)
    (ω : M.space) : (boundedDriveStop M n ω : ℝ≥0∞) ≤ ((n : ℝ≥0) + 1 : ℝ≥0) :=
  min_le_right _ _

theorem monotone_boundedDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (ω : M.space) : Monotone fun n => boundedDriveStop M n ω := by
  intro n k hnk
  exact min_le_min (max_le_max_right _ (M.data.driveMono ω hnk))
    (WithTop.coe_le_coe.2 (add_le_add (Nat.cast_le.2 hnk) le_rfl))

theorem ae_boundedDriveStop_bounds {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    ∀ᵐ ω ∂M.law, ∀ n, 0 < (boundedDriveStop M n ω : ℝ≥0∞) ∧
      (boundedDriveStop M n ω : ℝ≥0∞) < M.data.life ω := by
  filter_upwards [ae_firstPositiveDriveStop_bounds M, M.data.driveLt]
    with ω hb hlt n
  have hcap : (0 : WithTop ℝ≥0) < (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0) := by
    exact_mod_cast (show (0 : ℝ≥0) < (n : ℝ≥0) + 1 from by positivity)
  refine ⟨lt_min (hb.1.trans_le (le_max_right _ _)) hcap, ?_⟩
  exact lt_of_le_of_lt (min_le_left _ _) (max_lt (hlt n) hb.2)

theorem ae_tendsto_boundedDriveStop {κ θ : ℝ} (M : StoppedTypeModel κ θ) :
    ∀ᵐ ω ∂M.law, Tendsto (fun n => (boundedDriveStop M n ω : ℝ≥0∞))
      atTop (𝓝 (M.data.life ω)) := by
  have hcap : Tendsto (fun n : ℕ => (n : ℝ≥0∞) + 1) atTop (𝓝 ⊤) := by
    simpa only [top_add] using
      (ENNReal.tendsto_nat_nhds_top.add (tendsto_const_nhds (x := (1 : ℝ≥0∞))))
  filter_upwards [M.data.driveLimit, ae_firstPositiveDriveStop_bounds M] with ω hl hb
  change Tendsto
    (fun n => min (max (M.data.driveStops n ω : ℝ≥0∞)
      (firstPositiveDriveStop M ω : ℝ≥0∞)) ((n : ℝ≥0∞) + (1 : ℝ≥0∞)))
      atTop (𝓝 (M.data.life ω))
  have hconv :=
    (hl.max (tendsto_const_nhds (x := (firstPositiveDriveStop M ω : ℝ≥0∞)))).min hcap
  have he : min (max (M.data.life ω) (firstPositiveDriveStop M ω : ℝ≥0∞))
      (⊤ : ℝ≥0∞) = M.data.life ω :=
    (congrArg (fun x : ℝ≥0∞ => min x ⊤)
      (max_eq_left (show (firstPositiveDriveStop M ω : ℝ≥0∞) ≤ M.data.life ω
        from hb.2.le))).trans (min_eq_left le_top)
  exact he ▸ hconv

end InteractingSLE.Wire.RetMatchPredict
