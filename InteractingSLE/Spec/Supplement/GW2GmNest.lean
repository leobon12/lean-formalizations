/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Supplement.GW2SwDCat
import InteractingSLE.Spec.Supplement.GW2SwcChart

/-!
# Re-nesting: the back-nested joined driver is the front-nested one

Packet PROVE-GW2-GEOM2 (step R3 of PROVE-GW2-SWITCH's plan). J31 reads a switched program through
Prop 5.13's back-nested `joinedDriver E 0 0 L = catPath w₀ t₀ (catPath w₁ (t₁ - t₀) (…))`, while the
physical carrier of PROVE-GW2-SWITCH uses the front-nested `Swc.joinDrv`
(`joinDrv (k+1) = catPath (joinDrv k) T_k (stopDrv_k)`). By the associativity of driver concatenation
(`SwD.catPath_assoc`) the two agree up to the last time of the program, once the pieces are the stopped
drivers and the switching times are the program's times:

* `joinTime_congr`, `joinDrv_congr`: the front-nested driver depends only on the pieces used;
* `schedTime_length_eq_lastTime`, `specDelta_schedSpec`;
* **`joinedDriver_eq_catPath_joinDrv`**: the re-nesting identity after `k` pieces;
* **`joinedDriver_eq_joinDrv`**: `joinedDriver E 0 0 L t = joinDrv Δ D L.length t` for `t ≤ lastTime 0 L`;
* `joinTime_eq_schedTime`: for a time-ordered schedule whose first `k` pieces succeed, the front-nested
  switching times are the schedule's times.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule Sec7.StripSideHeightProb

variable {Δ Δ' : ℕ → ℝ≥0∞} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The switching times of the front-nested driver depend only on the pieces used. -/
theorem joinTime_congr : ∀ {k : ℕ}, (∀ j < k, Δ j = Δ' j) → (∀ j < k, D j = D' j) →
    Swc.joinTime Δ D k = Swc.joinTime Δ' D' k
  | 0, _, _ => rfl
  | k + 1, hΔ, hD => by
    have ih := joinTime_congr (k := k) (fun j hj => hΔ j (Nat.lt_succ_of_lt hj))
      (fun j hj => hD j (Nat.lt_succ_of_lt hj))
    change Swc.joinTime Δ D k + stopTime (Δ k) (D k) =
      Swc.joinTime Δ' D' k + stopTime (Δ' k) (D' k)
    rw [ih, hΔ k (Nat.lt_succ_self k), hD k (Nat.lt_succ_self k)]

/-- The front-nested driver depends only on the pieces used. -/
theorem joinDrv_congr : ∀ {k : ℕ}, (∀ j < k, Δ j = Δ' j) → (∀ j < k, D j = D' j) →
    Swc.joinDrv Δ D k = Swc.joinDrv Δ' D' k
  | 0, _, _ => rfl
  | k + 1, hΔ, hD => by
    have h1 := joinDrv_congr (k := k) (fun j hj => hΔ j (Nat.lt_succ_of_lt hj))
      (fun j hj => hD j (Nat.lt_succ_of_lt hj))
    have h2 := joinTime_congr (k := k) (fun j hj => hΔ j (Nat.lt_succ_of_lt hj))
      (fun j hj => hD j (Nat.lt_succ_of_lt hj))
    funext r
    change (if r ≤ Swc.joinTime Δ D k then Swc.joinDrv Δ D k r else
        Swc.joinDrv Δ D k (Swc.joinTime Δ D k) + stopDrv (Δ k) (D k) (r - Swc.joinTime Δ D k)) =
      (if r ≤ Swc.joinTime Δ' D' k then Swc.joinDrv Δ' D' k r else
        Swc.joinDrv Δ' D' k (Swc.joinTime Δ' D' k) + stopDrv (Δ' k) (D' k) (r - Swc.joinTime Δ' D' k))
    rw [h1, h2, hΔ k (Nat.lt_succ_self k), hD k (Nat.lt_succ_self k)]

/-- The schedule time after all entries is the last time. -/
theorem schedTime_length_eq_lastTime (L : List (ℝ × ℝ≥0)) :
    schedTime 0 L L.length = lastTime 0 L := by
  rcases L.eq_nil_or_concat with rfl | ⟨L', b, rfl⟩
  · rfl
  · rw [List.concat_eq_append, lastTime_eq_getLast _ _ (by simp)]
    simp only [List.getLast_append, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte,
      List.getLast_singleton, List.length_append, List.length_singleton, schedTime,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

/-- The own times of a schedule's program are its time gaps. -/
theorem specDelta_schedSpec (x : ℝ) {L : List (ℝ × ℝ≥0)} {j : ℕ} (hj : j < L.length) :
    specDelta (schedSpec x L) j = schedDelta 0 L j := by
  have hi := isFlowProg_scheduleProgram 0 L j (by rw [GW2Schedule.length_scheduleProgram]; exact hj)
  have ht : instrTime (schedSpec x L) j = schedDelta 0 L j := by
    simp only [instrTime, schedSpec, hi]
  rw [specDelta, ht, ite_eq_right (schedDelta_ne_top _ _ _)]

/-- In a time-ordered schedule, the time before entry `k` is at most the time of entry `k`. -/
theorem schedTime_le_getElem {L : List (ℝ × ℝ≥0)} (hL : TimeOrdered 0 L) {k : ℕ}
    (hk : k < L.length) : schedTime 0 L k ≤ L[k].2 := by
  rcases k with _ | k
  · exact zero_le
  · change (L.getD k (0, 0)).2 ≤ L[k + 1].2
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.pairwise_iff_getElem.1 hL.1 k (k + 1) (by omega) hk (Nat.lt_succ_self k)

theorem schedTime_succ_eq_getElem {L : List (ℝ × ℝ≥0)} {k : ℕ} (hk : k < L.length) :
    schedTime 0 L (k + 1) = L[k].2 := by
  change (L.getD k (0, 0)).2 = L[k].2
  rw [List.getD_eq_getElem _ _ hk]

/-- **Re-nesting after `k` pieces.** If the pieces are the stopped drivers, start at `0`, and the
front-nested switching times are the schedule's times, the back-nested driver of a time-ordered
schedule is the front-nested driver of the first `k` pieces followed by the back-nested rest. -/
theorem joinedDriver_eq_catPath_joinDrv {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (L : List (ℝ × ℝ≥0)) (hL : TimeOrdered 0 L) (h0 : ∀ j, (E j ω).1 0 = 0)
    (hw : ∀ j < L.length, ∀ t : ℝ≥0, (E j ω).1 t = stopDrv (Δ j) (D j) t)
    (hT : ∀ k < L.length, Swc.joinTime Δ D k = schedTime 0 L k) :
    ∀ k ≤ L.length, joinedDriver E 0 0 L ω =
      catPath (fun t : ℝ≥0 => Swc.joinDrv Δ D k t) (schedTime 0 L k)
        (joinedDriver E k (schedTime 0 L k) (L.drop k) ω)
  | 0, _ => by
    funext t
    change _ = catPath (fun _ : ℝ≥0 => (0 : ℝ)) 0 (joinedDriver E 0 0 L ω) t
    by_cases ht : t ≤ 0
    · rw [catPath_of_le ht, le_antisymm ht zero_le,
        Sec5.Prop513Schedule.joinedDriver_zero E ω h0 0 0 L]
    · simp only [catPath, ht, ↓reduceIte, zero_add, tsub_zero]
  | k + 1, hk => by
    have hkL : k < L.length := by omega
    rw [joinedDriver_eq_catPath_joinDrv E ω L hL h0 hw hT k hkL.le,
      List.drop_eq_getElem_cons hkL]
    change catPath (fun t : ℝ≥0 => Swc.joinDrv Δ D k t) (schedTime 0 L k)
      (catPath (E k ω).1 (L[k].2 - schedTime 0 L k)
        (joinedDriver E (k + 1) L[k].2 (L.drop (k + 1)) ω)) = _
    rw [← SwD.catPath_assoc (h0 k), add_tsub_cancel_of_le (schedTime_le_getElem hL hkL),
      ← schedTime_succ_eq_getElem hkL]
    congr 1
    funext t
    have hTk : Swc.joinTime Δ D k = (schedTime 0 L k : ℝ) := hT k hkL
    change catPath (fun t : ℝ≥0 => Swc.joinDrv Δ D k t) (schedTime 0 L k) (E k ω).1 t =
      (if (t : ℝ) ≤ Swc.joinTime Δ D k then Swc.joinDrv Δ D k t else
        Swc.joinDrv Δ D k (Swc.joinTime Δ D k) + stopDrv (Δ k) (D k) (t - Swc.joinTime Δ D k))
    rw [hTk]
    by_cases ht : t ≤ schedTime 0 L k
    · rw [catPath_of_le ht, ite_eq_left (NNReal.coe_le_coe.2 ht)]
    · have ht' : ¬ (t : ℝ) ≤ schedTime 0 L k := fun h => ht (NNReal.coe_le_coe.1 h)
      rw [ite_eq_right ht']
      simp only [catPath, ht, ↓reduceIte]
      rw [hw k hkL, NNReal.coe_sub (le_of_not_ge ht)]

/-- **The back-nested joined driver is the front-nested one up to the last time.** -/
theorem joinedDriver_eq_joinDrv {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (L : List (ℝ × ℝ≥0)) (hL : TimeOrdered 0 L) (h0 : ∀ j, (E j ω).1 0 = 0)
    (hw : ∀ j < L.length, ∀ t : ℝ≥0, (E j ω).1 t = stopDrv (Δ j) (D j) t)
    (hT : ∀ k < L.length, Swc.joinTime Δ D k = schedTime 0 L k)
    {t : ℝ≥0} (ht : t ≤ lastTime 0 L) :
    joinedDriver E 0 0 L ω t = Swc.joinDrv Δ D L.length t := by
  rw [joinedDriver_eq_catPath_joinDrv E ω L hL h0 hw hT L.length le_rfl,
    catPath_of_le (by rwa [schedTime_length_eq_lastTime])]

/-- **The front-nested switching times are the schedule's times** while the pieces succeed. -/
theorem joinTime_eq_schedTime (x : ℝ) {L : List (ℝ × ℝ≥0)} (hL : TimeOrdered 0 L)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} :
    ∀ {k : ℕ}, k ≤ L.length → AllSucc (specDelta (schedSpec x L)) D k →
      Swc.joinTime (specDelta (schedSpec x L)) D k = schedTime 0 L k
  | 0, _, _ => by simp only [Swc.joinTime, schedTime, NNReal.coe_zero]
  | k + 1, hk, hs => by
    have hkL : k < L.length := by omega
    have ih := joinTime_eq_schedTime x hL (k := k) hkL.le (hs.mono (Nat.le_succ k))
    have hlt : specDelta (schedSpec x L) k < (D k).2 := hs k (Nat.lt_succ_self k)
    change Swc.joinTime (specDelta (schedSpec x L)) D k +
      stopTime (specDelta (schedSpec x L) k) (D k) = _
    rw [ih, stopTime, min_eq_left hlt.le, specDelta_schedSpec x hkL, schedDelta,
      List.getD_eq_getElem _ _ hkL, ENNReal.toNNReal_coe,
      NNReal.coe_sub (schedTime_le_getElem hL hkL), schedTime_succ_eq_getElem hkL]
    ring

end InteractingSLE.Theorem14.GW2TipSystem.Gm
