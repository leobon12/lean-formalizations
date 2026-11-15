/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleRun
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# The successive chart of a switched schedule is the Loewner chart of the joined driver

Packet PROVE-GW2-SWITCH. A GW2 schedule launches each piece at the tip of the previous one, in the
chart `GW2Schedule.succChart` (the translation to the root followed by the centred Loewner maps of
the stopped pieces; `GW2Schedule.run_gw2`). Concatenating the stopped real-time drivers at their own
times gives one driver, `joinDrv`, defined up to the total time `joinTime`. By the domain Markov
property of the Loewner flow (`QuantumZipper.RS.fwdMapInv_add_shift`), the inverse of the successive
chart is the translated inverse Loewner map of the joined driver:

* `joinTime`, `joinDrv`; `continuous_joinDrv`, `joinDrv_zero`, `joinDrv_eqOn`, `shiftDrive_joinDrv_eqOn`;
* **`succChart_inv_eq`**: `(succChart x Δ D k).2.1 z = x + fwdMapInv (joinDrv Δ D k) (joinTime Δ D k) z`
  for `z ∈ ℍ`, when the first `k` stopped drivers are continuous and start at `0`.

This is deterministic and holds for every driver family; no probability is involved.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2TipSystem.Swc

open GW2Schedule Exist Staged StagedLaw

variable (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- The total own time of the first `k` stopped pieces (the time of the `k`-th switch). -/
def joinTime : ℕ → ℝ
  | 0 => 0
  | k + 1 => joinTime k + stopTime (Δ k) (D k)

/-- **The joined real-time driver** of the first `k` stopped pieces: piece `j` is run, from the
value reached at the switch, during `[joinTime j, joinTime (j + 1)]`. -/
def joinDrv : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun r =>
      if r ≤ joinTime Δ D k then joinDrv k r
      else joinDrv k (joinTime Δ D k) + stopDrv (Δ k) (D k) (r - joinTime Δ D k)

theorem joinTime_nonneg : ∀ k, 0 ≤ joinTime Δ D k
  | 0 => le_rfl
  | k + 1 => add_nonneg (joinTime_nonneg k) (stopTime_nonneg _ _)

theorem joinTime_succ (k : ℕ) : joinTime Δ D (k + 1) = joinTime Δ D k + stopTime (Δ k) (D k) := rfl

variable {Δ D}

/-- Before the `k`-th switch the joined driver of `k + 1` pieces is that of `k` pieces. -/
theorem joinDrv_eqOn (k : ℕ) :
    EqOn (joinDrv Δ D (k + 1)) (joinDrv Δ D k) (Icc 0 (joinTime Δ D k)) := by
  intro r hr
  change (if r ≤ joinTime Δ D k then joinDrv Δ D k r else _) = _
  rw [ite_eq_left hr.2]

/-- **The joined driver is continuous and starts at `0`** when the stopped drivers are. -/
theorem continuous_joinDrv {k : ℕ}
    (hc : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0) :
    Continuous (joinDrv Δ D k) ∧ joinDrv Δ D k 0 = 0 := by
  induction k with
  | zero => exact ⟨continuous_const, rfl⟩
  | succ k ih =>
    obtain ⟨hJ, hJ0⟩ := ih fun j hj => hc j (Nat.lt_succ_of_lt hj)
    obtain ⟨hS, hS0⟩ := hc k (Nat.lt_succ_self k)
    refine ⟨?_, ?_⟩
    · change Continuous fun r => if r ≤ joinTime Δ D k then joinDrv Δ D k r
        else joinDrv Δ D k (joinTime Δ D k) + stopDrv (Δ k) (D k) (r - joinTime Δ D k)
      refine continuous_if_le continuous_id continuous_const hJ.continuousOn
        (continuous_const.add (hS.comp (continuous_id.sub continuous_const))).continuousOn ?_
      intro r hr
      change r = joinTime Δ D k at hr
      rw [hr, sub_self, hS0, add_zero]
    · change (if (0 : ℝ) ≤ joinTime Δ D k then joinDrv Δ D k 0 else _) = 0
      rw [ite_eq_left (joinTime_nonneg Δ D k), hJ0]

/-- After the `k`-th switch the shifted joined driver is the `k`-th stopped driver. -/
theorem shiftDrive_joinDrv_eqOn {k : ℕ} (hS0 : stopDrv (Δ k) (D k) 0 = 0) :
    EqOn (QuantumZipper.RS.shiftDrive (joinDrv Δ D (k + 1)) (joinTime Δ D k))
      (stopDrv (Δ k) (D k)) (Icc 0 (stopTime (Δ k) (D k))) := by
  intro u hu
  have hT : joinDrv Δ D (k + 1) (joinTime Δ D k) = joinDrv Δ D k (joinTime Δ D k) :=
    joinDrv_eqOn k ⟨joinTime_nonneg Δ D k, le_rfl⟩
  change joinDrv Δ D (k + 1) (joinTime Δ D k + u) - joinDrv Δ D (k + 1) (joinTime Δ D k) = _
  rw [hT]
  rcases eq_or_lt_of_le hu.1 with hu0 | hupos
  · subst hu0
    rw [add_zero, hT, sub_self, hS0]
  · have hlt : ¬ joinTime Δ D k + u ≤ joinTime Δ D k := by linarith
    change (if joinTime Δ D k + u ≤ joinTime Δ D k then _ else
      joinDrv Δ D k (joinTime Δ D k) + stopDrv (Δ k) (D k) (joinTime Δ D k + u - joinTime Δ D k)) -
        _ = _
    rw [ite_eq_right hlt, add_sub_cancel_left, add_sub_cancel_left]

/-- **The successive chart's inverse is the translated inverse Loewner map of the joined driver**
(domain Markov property: `F_{T + δ} = F_T ∘ F^{(T)}_δ`), on `ℍ`. -/
theorem succChart_inv_eq (x : ℝ) {k : ℕ}
    (hc : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0)
    {z : ℂ} (hz : z ∈ H) :
    (succChart x Δ D k).2.1 z = (x : ℂ) + fwdMapInv (joinDrv Δ D k) (joinTime Δ D k) z := by
  induction k generalizing z with
  | zero =>
    change z + (x : ℂ) = (x : ℂ) + fwdMapInv (fun _ : ℝ => (0 : ℝ)) 0 z
    rw [fwdMapInv_zero_time continuous_const rfl hz, add_comm]
  | succ k ih =>
    have hck : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0 :=
      fun j hj => hc j (Nat.lt_succ_of_lt hj)
    obtain ⟨hS, hS0⟩ := hc k (Nat.lt_succ_self k)
    obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hck
    obtain ⟨hJ', hJ'0⟩ := continuous_joinDrv hc
    have hT := joinTime_nonneg Δ D k
    have hδ := stopTime_nonneg (Δ k) (D k)
    set w := fwdMapInv (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k)) z with hw
    have hwH : w ∈ H :=
      (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hS hS0 hδ hz).1
    change (succChart x Δ D k).2.1 w = _
    rw [ih hck hwH, joinTime_succ,
      QuantumZipper.RS.fwdMapInv_add_shift hJ' hJ'0 hT hδ hz]
    have hshift : fwdMapInv (QuantumZipper.RS.shiftDrive (joinDrv Δ D (k + 1)) (joinTime Δ D k))
        (stopTime (Δ k) (D k)) z = w :=
      LP.fwdMapInv_eq_of_eqOn_Icc (QuantumZipper.RS.continuous_shiftDrive hJ' _) hS
        (QuantumZipper.RS.shiftDrive_zero _ _) hS0 hδ (shiftDrive_joinDrv_eqOn hS0) hz
    rw [hshift]
    have hprev : fwdMapInv (joinDrv Δ D (k + 1)) (joinTime Δ D k) w =
        fwdMapInv (joinDrv Δ D k) (joinTime Δ D k) w :=
      LP.fwdMapInv_eq_of_eqOn_Icc hJ' hJ hJ'0 hJ0 hT (joinDrv_eqOn k) hwH
    rw [hprev]

end InteractingSLE.Theorem14.GW2TipSystem.Swc
