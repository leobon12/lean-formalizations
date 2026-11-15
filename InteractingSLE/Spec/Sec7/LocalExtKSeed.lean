/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKRestart

/-!
# The seed word of a restart and its processes

Packet PROVE-LOCEXT-K. After a restart at `T` on a cell with seed pattern `(S_L, S_R)`, the seed marks all start at the
driver and coincide afterwards; the distant marks have weight `0` in the seed-weight word. The stopped seed coupling of
`RestartSeedCouplingStatement` uses the deterministic **`1 + 1` seed word**:

* `oneSeedCount S = 1` if `S` is nonempty, `0` otherwise; `oneSeedIdx S k ∈ S` a chosen seed mark;
* `oneSeedY S = 0` (the positions), `oneSeedWts S ρ = ∑_S ρ` (the weight of the merged mark);
  `seedSumL (oneSeedY S_L) (oneSeedWts S_L ρL) = ∑_{S_L} ρL`;
* `r0W G W T`, `r0VL`, `r0VR`: the restarted driver and the restarted chosen seed marks, set to `0` off the good event `G`
  (so that they are adapted, `adaptedBefore_r0W`);
* `capStop_restart_eq_localStopPath`: on the cell, the capped local stop of the restarted path is its local stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Sec2.Restart

/-! ### The `1 + 1` seed word -/

section SeedWord

variable {n : ℕ}

open Classical in
/-- One merged seed mark on a side with a nonempty seed group, none otherwise. -/
def oneSeedCount (S : Finset (Fin n)) : ℕ := if S.Nonempty then 1 else 0

theorem nonempty_of_oneSeedCount {S : Finset (Fin n)} (k : Fin (oneSeedCount S)) : S.Nonempty := by
  classical
  by_contra hS
  have h0 : oneSeedCount S = 0 := by simp [oneSeedCount, hS]
  exact (h0 ▸ k).elim0

theorem oneSeedCount_of_nonempty {S : Finset (Fin n)} (hS : S.Nonempty) : oneSeedCount S = 1 := by
  classical
  simp [oneSeedCount, hS]

/-- The chosen seed mark of a side. -/
def oneSeedIdx (S : Finset (Fin n)) (k : Fin (oneSeedCount S)) : Fin n := S.min' (nonempty_of_oneSeedCount k)

theorem oneSeedIdx_mem (S : Finset (Fin n)) (k : Fin (oneSeedCount S)) : oneSeedIdx S k ∈ S :=
  Finset.min'_mem _ _

/-- The positions of the `1 + 1` seed word: `0`. -/
def oneSeedY (S : Finset (Fin n)) : Fin (oneSeedCount S) → ℝ := fun _ => 0

/-- The weight of the merged seed mark: the seed sum. -/
def oneSeedWts (S : Finset (Fin n)) (ρ : Fin n → ℝ) : Fin (oneSeedCount S) → ℝ := fun _ => ∑ i ∈ S, ρ i

theorem sum_oneSeedWts (S : Finset (Fin n)) (ρ : Fin n → ℝ) :
    ∑ k, (if oneSeedY S k = 0 then oneSeedWts S ρ k else 0) = ∑ i ∈ S, ρ i := by
  classical
  simp only [oneSeedY, oneSeedWts, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hS : S.Nonempty
  · rw [oneSeedCount_of_nonempty hS, Nat.cast_one, one_mul]
  · have h0 : oneSeedCount S = 0 := by simp [oneSeedCount, hS]
    rw [h0, Nat.cast_zero, zero_mul, Finset.not_nonempty_iff_eq_empty.1 hS, Finset.sum_empty]

theorem seedSumL_oneSeedY (S : Finset (Fin n)) (ρ : Fin n → ℝ) : seedSumL (oneSeedY S) (oneSeedWts S ρ) = ∑ i ∈ S, ρ i :=
  sum_oneSeedWts S ρ

theorem seedSumR_oneSeedY (S : Finset (Fin n)) (ρ : Fin n → ℝ) : seedSumR (oneSeedY S) (oneSeedWts S ρ) = ∑ i ∈ S, ρ i :=
  sum_oneSeedWts S ρ

theorem isOrderedForceWord_oneSeedY {nL nR : ℕ} (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) :
    IsOrderedForceWord (oneSeedY SL) (oneSeedY SR) :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

end SeedWord

/-! ### The processes of the seed word -/

section Processes

variable {Ω : Type*} {nL nR : ℕ}

open Classical in
/-- The restarted driver, `0` off `G`. -/
def r0W (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if ω ∈ G then restartDrv W T t ω else 0

open Classical in
/-- The restarted chosen left seed mark, `0` off `G`. -/
def r0VL (G : Set Ω) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (SL : Finset (Fin nL)) :
    Fin (oneSeedCount SL) → ℝ≥0 → Ω → ℝ :=
  fun k t ω => if ω ∈ G then restartMark (VL (oneSeedIdx SL k)) W T t ω else 0

open Classical in
/-- The restarted chosen right seed mark, `0` off `G`. -/
def r0VR (G : Set Ω) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (SR : Finset (Fin nR)) :
    Fin (oneSeedCount SR) → ℝ≥0 → Ω → ℝ :=
  fun k t ω => if ω ∈ G then restartMark (VR (oneSeedIdx SR k)) W T t ω else 0

variable {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0} {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {ω : Ω}

theorem r0W_of_mem (hω : ω ∈ G) (t : ℝ≥0) : r0W G W T t ω = restartDrv W T t ω := by
  simp [r0W, hω]

theorem r0VL_of_mem (hω : ω ∈ G) (k : Fin (oneSeedCount SL)) (t : ℝ≥0) :
    r0VL G VL W T SL k t ω = restartMark (VL (oneSeedIdx SL k)) W T t ω := by
  simp [r0VL, hω]

theorem r0VR_of_mem (hω : ω ∈ G) (k : Fin (oneSeedCount SR)) (t : ℝ≥0) :
    r0VR G VR W T SR k t ω = restartMark (VR (oneSeedIdx SR k)) W T t ω := by
  simp [r0VR, hω]

theorem rpath_r0W_of_mem (hω : ω ∈ G) :
    (fun s : ℝ => r0W G W T s.toNNReal ω) = fun s : ℝ => restartDrv W T s.toNNReal ω :=
  funext fun _ => r0W_of_mem hω _

end Processes

/-! ### The local stop at a restart -/

section Stop

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω} {r : ℝ} {ω : Ω}

/-- **On the cell, the capped local stop of the restarted path is its local stop.** -/
theorem capStop_restart_eq_localStopPath (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω)
    (hω : ω ∈ G) (hr : IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) :
    capStop r G (restartLife ζ T) (restartDrv W T) ω =
      localStopPath r (restartLife ζ T ω) (fun t => restartDrv W T t ω) := by
  have hF := isOrderedForceWord_cur hg hT
  have hseed := not_thresholdCondition_cur hg hT
  rw [capStop_restart_eq hω, capStop_eq_localStop (G := univ)
    (fun u _ => (IsGoodPath.restart (B := B) hg hT : _)) hF hr hseed (mem_univ ()), localStop_of_mem (mem_univ ())]

theorem capStop_restart_lt (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω)
    (hω : ω ∈ G) (hr : IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) :
    ((capStop r G (restartLife ζ T) (restartDrv W T) ω : WithTop ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := by
  rw [capStop_restart_eq_localStopPath hg hT hω hr]
  exact localStopPath_lt (isIntegratedSLEPath_restart (B := B) hg hT) (isOrderedForceWord_cur hg hT) hr
    (not_thresholdCondition_cur hg hT) (hasThresholdLimit_restart hg hT)

end Stop

/-! ### Stopping and adaptedness in the restarted filtration -/

section Adapted

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)}

/-- **The capped local stop of the restarted path is a stopping time of the restarted filtration.** -/
theorem isStoppingTime_capStop_restart (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ) :
    IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT)
      (capStop r G (restartLife ζ T) (restartDrv W T)) := by
  have hσ := isStoppingTime_restartTime_capStop hX hT hGm hG0 hG r
  intro t
  have h := IsStoppingTime.measurableSet_stopping_time_le hσ (isStoppingTime_add_const hT t)
  have e : {ω | capStop r G (restartLife ζ T) (restartDrv W T) ω ≤ (t : WithTop ℝ≥0)} =
      {ω | restartTime T (capStop r G (restartLife ζ T) (restartDrv W T)) ω ≤ ((T ω + t : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (capStop_restart_ne_top (G := G) (r := r) (ζ := ζ) (W := W)
      (T := T) ω)
    simp only [mem_ofPred_eq, restartTime, ← hs, WithTop.untopD_coe, WithTop.coe_le_coe, add_le_add_iff_left]
  rw [e]
  exact h

variable (hX : IsMeasurableKilledDriving W VL VR ζ)
  (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (hGm : MeasurableSet G)
  (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ)
include hX hT hGm hG0 hG

/-- A process equal off `G` to `0` and on `G`, before the stop, to the restart of progressive versions is adapted
before the stop. -/
theorem adaptedBefore_r0_of_eq {X Y Z : ℝ≥0 → Ω → ℝ} (hY : AdaptedBefore (drivingFiltration P hX) ζ Y)
    (hZ : AdaptedBefore (drivingFiltration P hX) ζ Z)
    (hXeq : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < capStop r G (restartLife ζ T) (restartDrv W T) ω →
      X t ω = progVersion ζ Y (T ω + t) ω - progVersion ζ Z (T ω) ω)
    (hX0 : ∀ ω ∉ G, ∀ t, X t ω = 0) :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT)
      (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) X := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hS := isStoppingTime_capStop_restart hX hT hGm hG0 hG r
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hζ : IsStoppingTime 𝓓 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hWad
  have hpv := adaptedBefore_restart hT hζ (isStronglyProgressive_progVersion hY) (isStronglyProgressive_progVersion hZ)
  have hle : ∀ s : ℝ≥0, MeasurableSet[restartFiltration 𝓓 T hT s]
      {ω | ((capStop r G (restartLife ζ T) (restartDrv W T) ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := fun s => hS s
  have hpv' := hpv.of_le hle fun ω => capStop_le (G := G) (ζ := restartLife ζ T) (W := restartDrv W T) r ω
  have hG𝓓 : ∀ t, MeasurableSet[restartFiltration 𝓓 T hT t] G := fun t =>
    measurableSpace_le_restartFiltration hT t _
      (measurableSet_stopped_of_zero hT (measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0))
  intro t A hA
  have e : {ω | (t : ℝ≥0∞) < (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞) ∧ X t ω ∈ A} =
      (G ∩ {ω | (t : ℝ≥0∞) < (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞) ∧
        progVersion ζ Y (T ω + t) ω - progVersion ζ Z (T ω) ω ∈ A}) ∪
      (Gᶜ ∩ ({ω | (t : ℝ≥0∞) < (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)} ∩
        {_ω | (0 : ℝ) ∈ A})) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, mem_compl_iff, not_true_eq_false,
        false_and, or_false]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hXeq ω hω t h1 ▸ h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, (hXeq ω hω t h1).symm ▸ h2⟩
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff, not_false_eq_true,
        true_and, false_or, hX0 ω hω t]
  rw [e]
  have hlt : MeasurableSet[restartFiltration 𝓓 T hT t]
      {ω | (t : ℝ≥0∞) < (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)} := by
    have h1 := (hle t).compl
    convert h1 using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact not_le.symm
  exact ((hG𝓓 t).inter (hpv' t A hA)).union ((hG𝓓 t).compl.inter (hlt.inter (MeasurableSet.const _)))

theorem adaptedBefore_r0W :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT)
      (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) (r0W G W T) := by
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX)
  refine adaptedBefore_r0_of_eq hX hT hGm hG0 hG r hWad hWad (fun ω hω t ht => ?_) (fun ω hω t => ?_)
  · have hlt : ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      have h1 : (t : ℝ≥0∞) < restartLife ζ T ω :=
        lt_of_lt_of_le ht (capStop_le (G := G) (ζ := restartLife ζ T) (W := restartDrv W T) r ω)
      exact (coe_lt_sub_iff _ _).1 h1
    have hT' : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hlt
    have hp := (hG ω hω).1
    rw [r0W_of_mem hω, restartDrv, (restart_values hp hlt).1, (restart_values hp hT').1]
  · simp [r0W, hω]

theorem adaptedBefore_r0VL (k : Fin (oneSeedCount SL)) :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT)
      (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) (r0VL G VL W T SL k) := by
  have hle := Ito.le_usualAugmentation (killedDrivingFiltration hX) P
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ W := Ito.adaptedBefore_mono hle
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hVad : AdaptedBefore (drivingFiltration P hX) ζ (VL (oneSeedIdx SL k)) := Ito.adaptedBefore_mono hle
    (Coupling.adaptedBefore_killedDriving_VL hX _)
  refine adaptedBefore_r0_of_eq hX hT hGm hG0 hG r hVad hWad (fun ω hω t ht => ?_) (fun ω hω t => ?_)
  · have hlt : ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      have h1 : (t : ℝ≥0∞) < restartLife ζ T ω :=
        lt_of_lt_of_le ht (capStop_le (G := G) (ζ := restartLife ζ T) (W := restartDrv W T) r ω)
      exact (coe_lt_sub_iff _ _).1 h1
    have hT' : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hlt
    have hp := (hG ω hω).1
    rw [r0VL_of_mem hω, restartMark, (restart_values hp hlt).2.1, (restart_values hp hT').1]
  · simp [r0VL, hω]

theorem adaptedBefore_r0VR (k : Fin (oneSeedCount SR)) :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT)
      (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) (r0VR G VR W T SR k) := by
  have hle := Ito.le_usualAugmentation (killedDrivingFiltration hX) P
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ W := Ito.adaptedBefore_mono hle
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hVad : AdaptedBefore (drivingFiltration P hX) ζ (VR (oneSeedIdx SR k)) := Ito.adaptedBefore_mono hle
    (Coupling.adaptedBefore_killedDriving_VR hX _)
  refine adaptedBefore_r0_of_eq hX hT hGm hG0 hG r hVad hWad (fun ω hω t ht => ?_) (fun ω hω t => ?_)
  · have hlt : ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      have h1 : (t : ℝ≥0∞) < restartLife ζ T ω :=
        lt_of_lt_of_le ht (capStop_le (G := G) (ζ := restartLife ζ T) (W := restartDrv W T) r ω)
      exact (coe_lt_sub_iff _ _).1 h1
    have hT' : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hlt
    have hp := (hG ω hω).1
    rw [r0VR_of_mem hω, restartMark, (restart_values hp hlt).2.2, (restart_values hp hT').1]
  · simp [r0VR, hω]

end Adapted

end LocalExt

end InteractingSLE
