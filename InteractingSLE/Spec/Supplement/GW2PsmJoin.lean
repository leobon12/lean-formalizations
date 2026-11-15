/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwcChart

/-!
# GW2's open lines: joined drivers of programs agreeing on a prefix

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic; the union side of the Claim(k) step):

* `joinDrv_congr`: equal stops and drives on the first `m` pieces give equal joined drivers and times up to `m`;
* **`joinDrv_succ_eqOn_of_le`**: if moreover piece `m` has the same drive and its first stop is below the second,
  the joined drivers after `m + 1` pieces agree up to the end of the first program's piece `m`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Psm

open GW2TipSystem.Swc Exist.Staged Exist.StagedLaw

/-- **Equal first `m` pieces give equal joined drivers and times.** -/
theorem joinDrv_congr {Δ Δ' : ℕ → ℝ≥0∞} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {m : ℕ}
    (hΔ : ∀ j < m, Δ j = Δ' j) (hD : ∀ j < m, D j = D' j) :
    ∀ k ≤ m, joinDrv Δ D k = joinDrv Δ' D' k ∧ joinTime Δ D k = joinTime Δ' D' k := by
  intro k hk
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hk)
    have hk' : k < m := hk
    have hst : stopTime (Δ k) (D k) = stopTime (Δ' k) (D' k) := by rw [hΔ k hk', hD k hk']
    have hsd : stopDrv (Δ k) (D k) = stopDrv (Δ' k) (D' k) := by rw [hΔ k hk', hD k hk']
    refine ⟨funext fun r => ?_, ?_⟩
    · change (if r ≤ joinTime Δ D k then joinDrv Δ D k r
          else joinDrv Δ D k (joinTime Δ D k) + stopDrv (Δ k) (D k) (r - joinTime Δ D k)) =
        (if r ≤ joinTime Δ' D' k then joinDrv Δ' D' k r
          else joinDrv Δ' D' k (joinTime Δ' D' k) + stopDrv (Δ' k) (D' k) (r - joinTime Δ' D' k))
      rw [h1, h2, hsd]
    · rw [joinTime_succ, joinTime_succ, h2, hst]

/-- **Agreement after one more piece with the same drive, up to the shorter stop.** -/
theorem joinDrv_succ_eqOn_of_le {Δ Δ' : ℕ → ℝ≥0∞} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {m : ℕ}
    (hΔ : ∀ j < m, Δ j = Δ' j) (hD : ∀ j < m, D j = D' j) (hDm : D m = D' m) (hle : Δ m ≤ Δ' m) :
    EqOn (joinDrv Δ D (m + 1)) (joinDrv Δ' D' (m + 1)) (Icc 0 (joinTime Δ D (m + 1))) := by
  obtain ⟨h1, h2⟩ := joinDrv_congr hΔ hD m le_rfl
  intro r hr
  change (if r ≤ joinTime Δ D m then joinDrv Δ D m r
      else joinDrv Δ D m (joinTime Δ D m) + stopDrv (Δ m) (D m) (r - joinTime Δ D m)) =
    (if r ≤ joinTime Δ' D' m then joinDrv Δ' D' m r
      else joinDrv Δ' D' m (joinTime Δ' D' m) + stopDrv (Δ' m) (D' m) (r - joinTime Δ' D' m))
  rw [h1, h2]
  split_ifs with h
  · rfl
  · congr 1
    -- `r − T ≤ stopTime (Δ m) (D m)`: the two stopped drivers agree there
    have hr2 : r - joinTime Δ' D' m ≤ stopTime (Δ m) (D m) := by
      have := hr.2
      rw [joinTime_succ, h2] at this
      linarith
    have hr0 : 0 ≤ r - joinTime Δ' D' m := by linarith [not_le.1 h]
    set x := r - joinTime Δ' D' m with hx
    change (retOf (Δ m) (D m)).1 x.toNNReal = (retOf (Δ' m) (D' m)).1 x.toNNReal
    rw [← hDm]
    simp only [retOf]
    have hxle : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min (Δ m) (D m).2 := by
      rcases eq_or_ne (min (Δ m) (D m).2) ⊤ with htop | htop
      · rw [htop]; exact le_top
      · rw [← ENNReal.coe_toNNReal htop, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe]
        exact hr2
    have h1' : min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δ m) (D m).2) = (x.toNNReal : ℝ≥0∞) := min_eq_left hxle
    have h2' : min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δ' m) (D m).2) = (x.toNNReal : ℝ≥0∞) :=
      min_eq_left (hxle.trans (min_le_min_right _ hle))
    rw [h1', h2']

end InteractingSLE.Theorem14.GW2Psm
