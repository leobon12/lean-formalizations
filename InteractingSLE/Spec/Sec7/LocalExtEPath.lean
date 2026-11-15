/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtEHist
import InteractingSLE.Spec.Sec5.Markov

/-!
# (R3) at a restart, pathwise

Packet PROVE-LOCEXT-E. At a finite time `T < ζ` the shifted path seen from the driver
(`W'_t = W_{T+t} − W_T`, `V'_t = V_{T+t} − W_T`, `ζ' = ζ − T`; `Sec5.Markov.restartDrv`, `restartMark`, `restartLife`)
is a good path for the word with positions `c = V_T − W_T` (`IsGoodPath.restart`). Through the local stop `S'` of the
restarted path (radius `r`, `Sec7.LocalExt.capStop`):

* **`reindexHist_twoSeedProj_restart`** ((R3) at a restart): the restarted history stopped at `S'` is `reindexHist c r`
  of its two-seed history (PROVE-LOCEXT-C's `reindexHist_twoSeedProj_stoppedHistory`, applied on a one-point space to
  the restarted path);
* **`stoppedHistory_restartTime_eq_concatHist`**: the original history stopped at `σ = T + S'`
  (`Sec5.Markov.restartTime`) is the concatenation `concatHist` of the history stopped at `T` and the restarted
  history stopped at `S'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω} {r : ℝ} {ω : Ω}

/-! ### The restarted path -/

/-- The restarted left positions `V^L_T − W_T`. -/
def curL (VL : Fin nL → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : Fin nL → ℝ :=
  fun i => VL i (T ω) ω - W (T ω) ω

/-- The restarted right positions `V^R_T − W_T`. -/
def curR (VR : Fin nR → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : Fin nR → ℝ :=
  fun j => VR j (T ω) ω - W (T ω) ω

/-- The restarted Brownian motion `B_{T+t} − B_T`. -/
def restartBM (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => B (T ω + t) ω - B (T ω) ω

/-- The restarted path satisfies Definition 2.1 for the current positions. -/
theorem isIntegratedSLEPath_restart (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) :
    IsIntegratedSLEPath κ (curL VL W T ω) (curR VR W T ω) ρL ρR (fun t => restartDrv W T t ω)
      (fun i t => restartMark (VL i) W T t ω) (fun j t => restartMark (VR j) W T t ω)
      (fun t => restartBM B T t ω) (restartLife ζ T ω) :=
  hg.1.restart hT

/-- The terminal-state property survives the restart (translation invariance of the threshold condition). -/
theorem hasThresholdLimit_restart (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) :
    HasThresholdLimit ρL ρR (fun t => restartDrv W T t ω) (fun i t => restartMark (VL i) W T t ω)
      (fun j t => restartMark (VR j) W T t ω) (restartLife ζ T ω) := by
  intro T' hT' hT'ζ
  have hsum : ((T ω + T' : ℝ≥0) : ℝ≥0∞) = ζ ω := by
    have hne : ζ ω ≠ ⊤ := by
      intro htop
      simp only [restartLife, htop, ENNReal.top_sub_coe] at hT'ζ
      exact ENNReal.coe_ne_top hT'ζ
    rw [ENNReal.coe_add, hT'ζ, restartLife]
    exact add_tsub_cancel_of_le hT.le
  obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := hg.2 (T ω + T') (lt_of_lt_of_le hT' le_add_self) hsum
  refine ⟨w₀ - W (T ω) ω, fun i => vL₀ i - W (T ω) ω, fun j => vR₀ j - W (T ω) ω, ?_,
    (ForceWord.thresholdCondition_sub_iff ρL ρR w₀ (W (T ω) ω) vL₀ vR₀).2 hth⟩
  have hshift : Tendsto (fun t : ℝ≥0 => T ω + t) (𝓝[<] T') (𝓝[<] (T ω + T')) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add continuous_id).tendsto T').mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => (add_lt_add_iff_left (T ω)).2 ht
  have h := hlim.comp hshift
  have hc : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
      (p.1 - W (T ω) ω, fun i => p.2.1 i - W (T ω) ω, fun j => p.2.2 j - W (T ω) ω) :=
    (continuous_fst.sub continuous_const).prodMk
      ((continuous_pi fun i => ((continuous_apply i).comp continuous_snd.fst).sub continuous_const).prodMk
        (continuous_pi fun j => ((continuous_apply j).comp continuous_snd.snd).sub continuous_const))
  exact (hc.tendsto _).comp h

/-- **The restarted path is a good path** for the current positions. -/
theorem IsGoodPath.restart (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) :
    IsGoodPath κ (curL VL W T ω) (curR VR W T ω) ρL ρR (fun (t : ℝ≥0) (_ : Unit) => restartDrv W T t ω)
      (fun i (t : ℝ≥0) (_ : Unit) => restartMark (VL i) W T t ω)
      (fun j (t : ℝ≥0) (_ : Unit) => restartMark (VR j) W T t ω)
      (fun (t : ℝ≥0) (_ : Unit) => restartBM B T t ω) (fun _ => restartLife ζ T ω) () :=
  ⟨isIntegratedSLEPath_restart hg hT, hasThresholdLimit_restart hg hT⟩

/-- The current positions form an ordered force word. -/
theorem isOrderedForceWord_cur (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) :
    IsOrderedForceWord (curL VL W T ω) (curR VR W T ω) := by
  obtain ⟨-, -, -, -, -, -, hanti, hle, hge, hmono, -⟩ := hg.1
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun j => ?_⟩
  · simp only [curL]
    linarith [hanti (T ω) hT hij]
  · simp only [curL]
    linarith [hle (T ω) hT i]
  · simp only [curR]
    linarith [hmono (T ω) hT hij]
  · simp only [curR]
    linarith [hge (T ω) hT j]

/-- The current seed is admissible (the threshold condition fails before `ζ`). -/
theorem not_thresholdCondition_cur (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 (curL VL W T ω) (curR VR W T ω) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -⟩ := hg.1
  intro h
  refine hnot (T ω) hT ?_
  have h' := (ForceWord.thresholdCondition_sub_iff ρL ρR (W (T ω) ω) (W (T ω) ω) (fun i => VL i (T ω) ω)
    (fun j => VR j (T ω) ω)).1
  rw [sub_self] at h'
  exact h' h

/-! ### (R3) at a restart -/

/-- The capped local stop of the restarted path at a point of the good event is the one of the restarted path on a
one-point space. -/
theorem capStop_restart_eq (hω : ω ∈ G) :
    capStop r G (restartLife ζ T) (restartDrv W T) ω =
      capStop r univ (fun _ : Unit => restartLife ζ T ω) (fun (t : ℝ≥0) (_ : Unit) => restartDrv W T t ω) () := by
  unfold capStop
  rw [localStop_of_mem hω, localStop_of_mem (mem_univ ())]

/-- **(R3) at a restart**: through the local stop of the restarted path (radius `r` admissible for the current
positions), the restarted history is `reindexHist` of its two-seed history, with the current positions. -/
theorem reindexHist_twoSeedProj_restart (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hT : (T ω : ℝ≥0∞) < ζ ω) (hω : ω ∈ G) (hr : IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) :
    reindexHist (curL VL W T ω) (curR VR W T ω) r (twoSeedProj (curL VL W T ω) (curR VR W T ω)
        (stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
          (fun j => restartMark (VR j) W T) (restartLife ζ T)) (capStop r G (restartLife ζ T) (restartDrv W T)) ω)) =
      stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
        (fun j => restartMark (VR j) W T) (restartLife ζ T)) (capStop r G (restartLife ζ T) (restartDrv W T)) ω := by
  have h1 := reindexHist_twoSeedProj_stoppedHistory (G := univ) (isOrderedForceWord_cur hg hT) hr
    (not_thresholdCondition_cur hg hT) (fun u _ => (IsGoodPath.restart hg hT : _)) (mem_univ ())
  have e : stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
      (fun j => restartMark (VR j) W T) (restartLife ζ T)) (capStop r G (restartLife ζ T) (restartDrv W T)) ω =
      stoppedHistory (completedState (fun t (_ : Unit) => restartDrv W T t ω)
        (fun i t _ => restartMark (VL i) W T t ω) (fun j t _ => restartMark (VR j) W T t ω)
        (fun _ => restartLife ζ T ω)) (capStop r univ (fun _ : Unit => restartLife ζ T ω)
          (fun t _ => restartDrv W T t ω)) () := by
    simp only [stoppedHistory, stopAt, capStop_restart_eq hω]
    rfl
  rw [e]
  exact h1

/-! ### The concatenation at a restart -/

/-- The local stop of the restarted path is finite and strictly before the restarted lifetime. -/
theorem exists_capStop_restart (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω)
    (hω : ω ∈ G) (hr : IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) :
    ∃ s : ℝ≥0, capStop r G (restartLife ζ T) (restartDrv W T) ω = s ∧ (s : ℝ≥0∞) < restartLife ζ T ω := by
  have hF := isOrderedForceWord_cur hg hT
  have hseed := not_thresholdCondition_cur hg hT
  have hcap : capStop r G (restartLife ζ T) (restartDrv W T) ω =
      localStopPath r (restartLife ζ T ω) (fun t => restartDrv W T t ω) := by
    rw [capStop_restart_eq hω, capStop_eq_localStop (G := univ)
      (fun u _ => (IsGoodPath.restart (B := B) hg hT : _)) hF hr hseed (mem_univ ()), localStop_of_mem (mem_univ ())]
  have hlt := localStopPath_lt (isIntegratedSLEPath_restart (B := B) hg hT) hF hr hseed
    (hasThresholdLimit_restart hg hT)
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, localStopPath r (restartLife ζ T ω) (fun t => restartDrv W T t ω) = s :=
    WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon) |>.imp
      fun _ h => h.symm
  refine ⟨s, hcap.trans hs, ?_⟩
  have h := hlt
  rw [hs] at h
  exact h

/-- **The concatenation at a restart**: the original history stopped at `σ = T + S'` (`S'` the local stop of the
restarted path) is `concatHist` of the history stopped at `T` and the restarted history stopped at `S'`. -/
theorem stoppedHistory_restartTime_eq_concatHist (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hT : (T ω : ℝ≥0∞) < ζ ω) (hω : ω ∈ G) (hr : IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) :
    stoppedHistory (completedState W VL VR ζ) (restartTime T (capStop r G (restartLife ζ T) (restartDrv W T))) ω =
      concatHist (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
        (stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
          (fun j => restartMark (VR j) W T) (restartLife ζ T)) (capStop r G (restartLife ζ T) (restartDrv W T)) ω) := by
  obtain ⟨s, hs, hsζ⟩ := exists_capStop_restart (B := B) hg hT hω hr
  set S' := capStop r G (restartLife ζ T) (restartDrv W T) with hS'
  set X' := completedState (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T)
    (restartLife ζ T) with hX'
  have hσ : restartTime T S' ω = ((T ω + s : ℝ≥0) : WithTop ℝ≥0) := by
    simp only [restartTime, hs, WithTop.untopD_coe]
  have hTs : ((T ω + s : ℝ≥0) : ℝ≥0∞) < ζ ω := (Sec2.Restart.coe_lt_sub_iff _ _).1 hsζ
  -- the restarted state is continuous before the restarted lifetime
  have hp' := isIntegratedSLEPath_restart (B := B) hg hT
  have hcont : ContinuousOn (fun t => drivingState (restartDrv W T) (fun i => restartMark (VL i) W T)
      (fun j => restartMark (VR j) W T) t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} :=
    hp'.2.2.2.1.prodMk ((continuousOn_pi.2 hp'.2.2.2.2.1).prodMk (continuousOn_pi.2 hp'.2.2.2.2.2.1))
  have hX'eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → X' t ω =
      drivingState (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T) t ω :=
    fun t ht => ite_eq_left ht
  have hca : ∀ m : ℝ≥0, (m : ℝ≥0∞) < restartLife ζ T ω → ContinuousAt (fun t => X' t ω) m := by
    intro m hm
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    refine (hcont.continuousAt (hopen.mem_nhds hm)).congr ?_
    exact Filter.eventually_of_mem (hopen.mem_nhds hm) fun t ht => (hX'eq t ht).symm
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [stoppedHistory, concatHist, hσ, hs, WithTop.untopD_coe]
  · show completedState W VL VR ζ (stopAt (restartTime T S') q ω) ω =
      concatAt q (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω, stoppedHistory X' S' ω)
    rw [stopAt_of_eq_coe hσ]
    unfold concatAt
    simp only [stoppedHistory, WithTop.untopD_coe]
    by_cases hq : (q : ℝ≥0) ≤ T ω
    · simp only [hq, ↓reduceIte, stopAt_of_eq_coe (τ := fun ω => (T ω : WithTop ℝ≥0)) (ω := ω) rfl,
        min_eq_left hq, min_eq_left (hq.trans le_self_add)]
    · simp only [hq, ↓reduceIte]
      rw [not_le] at hq
      set u : ℝ≥0 := (q : ℝ≥0) - T ω with hu
      set m : ℝ≥0 := min u s with hm
      have hmζ : (m : ℝ≥0∞) < restartLife ζ T ω := lt_of_le_of_lt (by exact_mod_cast min_le_right u s) hsζ
      have hqT : (q : ℝ≥0) = T ω + u := (add_tsub_cancel_of_le hq.le).symm
      have hmin : min (q : ℝ≥0) (T ω + s) = T ω + m := by rw [hqT, min_add_add_left]
      have hTm : ((T ω + m : ℝ≥0) : ℝ≥0∞) < ζ ω := (Sec2.Restart.coe_lt_sub_iff _ _).1 hmζ
      -- the current state and the value of the restarted history at `u`
      have hcur : histState (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) =
          drivingState W VL VR (T ω) ω := by
        have h := histState_stoppedHistory (completedState W VL VR ζ)
          (τ := fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) (ω := ω) (T := T ω) rfl
        rw [h]
        exact ite_eq_left hT
      have hval : valueAt (stoppedHistory X' S' ω) u = X' m ω := by
        refine valueAt_eq_of_tendsto ?_
        have hs' : ∀ n, (stoppedHistory X' S' ω).2 (upDyad n u) = X' (min ((upDyad n u : ℚ≥0) : ℝ≥0) s) ω :=
          fun n => by simp only [stoppedHistory, stopAt_of_eq_coe hs]
        simp only [hs']
        exact (hca m hmζ).tendsto.comp ((tendsto_upDyad u).min tendsto_const_nhds)
      have e1 : (fun ω => (T ω : WithTop ℝ≥0)) ω = (T ω : WithTop ℝ≥0) := rfl
      rw [show histState (T ω, fun q => completedState W VL VR ζ (stopAt (fun ω => (T ω : WithTop ℝ≥0)) q ω) ω) =
          drivingState W VL VR (T ω) ω from hcur]
      rw [show valueAt (S' ω, fun q => X' (stopAt S' q ω) ω) u = X' m ω from hval, hmin, hX'eq m hmζ]
      simp only [completedState, hTm, ↓reduceIte, drivingState, shiftState, restartDrv, restartMark,
        sub_add_cancel]

end LocalExt

end InteractingSLE
