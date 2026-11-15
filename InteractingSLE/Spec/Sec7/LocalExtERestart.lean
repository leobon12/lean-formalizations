/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtECells
import InteractingSLE.Spec.Sec7.LocalExtEStmt

/-!
# The cell events of the restart rule at an own-filtration stop

Packet PROVE-LOCEXT-E. For a stopping time `τ ≤ ζ` of the frozen driving filtration `𝓓`, a good event `G` and a cell
code `c = (N, S_L, S_R, k)`:

* `cellTime τ c = min(τ, N + 1)`: a finite `𝓓`-stopping time, equal to `τ` on `{τ < N + 1}`;
* `cellEvent`: the points of `G` with `N ≤ τ < N + 1`, `τ < ζ`, whose (progressive version of the) state at `τ` is a
  cell state of `c`; **`measurableSet_cellEvent`**: it is an event of `𝓓_{min(τ, N+1)}`;
* `cellStop = min(τ, N+1) + S'`, `S'` the restarted local stop of radius `2^{-k}`; a `𝓓`-stopping time
  (`isStoppingTime_cellStop`), strictly after `τ` on the cell event (`lt_cellStop`) and before `ζ` (`cellStop_le`);
* `ae_mem_cellSet_iff`: almost surely, the recorded history `𝒳_τ` lies in `cellSet c` iff the point lies in the cell
  event (at `τ = ζ` the state is the terminal one, at which the threshold condition holds, so no admissible cell
  contains it).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Coupling

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The finite restart time of a cell -/

/-- `min(τ, N + 1)` as a finite time. -/
def cellTime (τ : Ω → WithTop ℝ≥0) (c : CellCode nL nR) (ω : Ω) : ℝ≥0 :=
  (min (τ ω) (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)).untopD 0

theorem coe_cellTime (τ : Ω → WithTop ℝ≥0) (c : CellCode nL nR) (ω : Ω) :
    ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := by
  unfold cellTime
  generalize hm : min (τ ω) (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) = m
  have hne : m ≠ ⊤ := hm ▸ ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  cases m with
  | top => exact absurd rfl hne
  | coe a => rfl

theorem coe_cellTime_of_lt {τ : Ω → WithTop ℝ≥0} {c : CellCode nL nR} {ω : Ω}
    (h : τ ω < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)) : ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) = τ ω := by
  rw [coe_cellTime, min_eq_left h.le]

theorem isStoppingTime_cellTime {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (c : CellCode nL nR) : IsStoppingTime 𝓖 fun ω => ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) := by
  have e : (fun ω => ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min (τ ω) (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := funext (coe_cellTime τ c)
  rw [e]
  exact hτ.min_const _

theorem cellTime_le {τ : Ω → WithTop ℝ≥0} (c : CellCode nL nR) :
    (fun ω => ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0)) ≤ τ := fun ω => by
  show ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω
  rw [coe_cellTime]; exact min_le_left _ _

/-- An event of `𝓖₀` is an event of every stopped σ-algebra. -/
theorem measurableSet_stopped_of_zero {𝓖 : Filtration ℝ≥0 mΩ} {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ)
    {s : Set Ω} (hs : MeasurableSet[𝓖 0] s) : MeasurableSet[hρ.measurableSpace] s :=
  ⟨le_iSup (fun t => (𝓖 t : MeasurableSpace Ω)) 0 _ hs, fun t => (𝓖.mono (zero_le (a := t)) _ hs).inter (hρ t)⟩

/-! ### The progressive state and the cell event -/

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The state of the progressive versions of the coordinates (`Sec2.Restart.progVersion`). -/
def pvState (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (Sec2.Restart.progVersion ζ W t ω, fun i => Sec2.Restart.progVersion ζ (VL i) t ω,
    fun j => Sec2.Restart.progVersion ζ (VR j) t ω)

/-- Before `ζ` on a good path the progressive state is the state. -/
theorem pvState_eq {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    pvState ζ W VL VR t ω = drivingState W VL VR t ω := by
  obtain ⟨h1, h2, h3⟩ := Sec2.Restart.restart_values hg.1 ht
  simp only [pvState, drivingState, h1, h2, h3]

/-- **The cell event** of a code: the points of `G` with `N ≤ τ < N + 1` and `τ < ζ` whose progressive state at `τ` is
a cell state. -/
def cellEvent (τ : Ω → WithTop ℝ≥0) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (c : CellCode nL nR) : Set Ω :=
  {ω | ω ∈ G ∧ ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ∧ τ ω < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) ∧
    ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ IsCellState c (pvState ζ W VL VR (cellTime τ c ω) ω)}

variable {P : Measure Ω}

/-- **The cell event belongs to `𝓓_{min(τ, N+1)}`.** -/
theorem measurableSet_cellEvent (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) {G : Set Ω} (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (c : CellCode nL nR) :
    MeasurableSet[(isStoppingTime_cellTime hτ c).measurableSpace] (cellEvent τ G ζ W VL VR c) := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hρ := isStoppingTime_cellTime hτ c
  have hle : killedDrivingFiltration hX ≤ 𝓓 := Ito.le_usualAugmentation _ P
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_W hX)
  have hLad : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_VL hX i)
  have hRad : ∀ j, AdaptedBefore 𝓓 ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_VR hX j)
  have hζ : IsStoppingTime 𝓓 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hWad
  -- the progressive state at the cell time
  have hev : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓓 ζ X →
      Measurable[hρ.measurableSpace] fun ω => Sec2.Restart.progVersion ζ X (cellTime τ c ω) ω := by
    intro X hX'
    have h := measurable_stoppedValue (Sec2.Restart.isStronglyProgressive_progVersion hX') hρ
    exact h
  have hst : Measurable[hρ.measurableSpace] fun ω => pvState ζ W VL VR (cellTime τ c ω) ω :=
    (hev hWad).prodMk ((@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) hρ.measurableSpace _ _ fun i => hev (hLad i)).prodMk
      (@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) hρ.measurableSpace _ _ fun j => hev (hRad j)))
  have hG : MeasurableSet[hρ.measurableSpace] G :=
    measurableSet_stopped_of_zero hρ (measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0)
  -- `N ≤ τ < N + 1` in terms of the cell time
  have hNτ : {ω | ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ∧ τ ω < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)} =
      {ω | ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0)} ∩
        {ω | ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, coe_cellTime, le_min_iff, min_lt_iff, lt_self_iff_false, or_false]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, WithTop.coe_le_coe.2 (by push_cast; linarith)⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  have hζlt : {ω | ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) < ζ ω} =
      {ω | (ζ ω : WithTop ℝ≥0) ≤ ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact ⟨fun h => not_le.2 h, fun h => not_le.1 h⟩
  have e : cellEvent τ G ζ W VL VR c = G ∩ ({ω | ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω ∧
      τ ω < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)} ∩ ({ω | ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) < ζ ω} ∩
        (fun ω => pvState ζ W VL VR (cellTime τ c ω) ω) ⁻¹' {x | IsCellState c x})) := by
    ext ω
    simp only [cellEvent, mem_ofPred_eq, mem_inter_iff, mem_preimage, and_assoc]
  rw [e, hNτ, hζlt]
  exact hG.inter (((hρ.measurableSet_ge' _).inter (hρ.measurableSet_lt' _)).inter
    ((IsStoppingTime.measurableSet_stopping_time_le hζ hρ).compl.inter (hst (measurableSet_isCellState c))))

/-! ### The cell stop -/

section CellStop

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0} {G : Set Ω}

/-- **The cell stop** `min(τ, N+1) + S'`, `S'` the local stop of radius `2^{-k}` of the path restarted at
`min(τ, N+1)`. -/
def cellStop (τ : Ω → WithTop ℝ≥0) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (c : CellCode nL nR) :
    Ω → WithTop ℝ≥0 :=
  restartTime (cellTime τ c) (capStop c.radius G (restartLife ζ (cellTime τ c)) (restartDrv W (cellTime τ c)))

theorem isStoppingTime_cellStop (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (c : CellCode nL nR) :
    IsStoppingTime (drivingFiltration P hX) (cellStop τ G ζ W c) :=
  isStoppingTime_restartTime_capStop hX (isStoppingTime_cellTime hτ c) hGm hG0 hG c.radius

/-- On the cell event the restart time is `τ`. -/
theorem coe_cellTime_of_mem {c : CellCode nL nR} {ω : Ω} (hω : ω ∈ cellEvent τ G ζ W VL VR c) :
    ((cellTime τ c ω : ℝ≥0) : WithTop ℝ≥0) = τ ω :=
  coe_cellTime_of_lt hω.2.2.1

/-- On the cell event the state at `τ` is a cell state, and the cell radius is admissible for the current positions. -/
theorem isCellState_of_mem (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {c : CellCode nL nR} {ω : Ω}
    (hω : ω ∈ cellEvent τ G ζ W VL VR c) : IsCellState c (drivingState W VL VR (cellTime τ c ω) ω) := by
  have h := hω.2.2.2.2
  rwa [pvState_eq (hG ω hω.1) hω.2.2.2.1] at h

theorem isSeedRadius_of_mem (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {c : CellCode nL nR} {ω : Ω}
    (hω : ω ∈ cellEvent τ G ζ W VL VR c) :
    IsSeedRadius (curL VL W (cellTime τ c) ω) (curR VR W (cellTime τ c) ω) c.radius :=
  (isCellState_of_mem hG hω).2.2.1

/-- The restarted local stop is positive and finite. -/
theorem exists_capStop_restart_pos {ω' : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω') {T : Ω → ℝ≥0}
    (hT : (T ω' : ℝ≥0∞) < ζ ω') (hω : ω' ∈ G) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℝ≥0, capStop r G (restartLife ζ T) (restartDrv W T) ω' = s ∧ 0 < s ∧
      (s : ℝ≥0∞) ≤ restartLife ζ T ω' := by
  have hp' := isIntegratedSLEPath_restart (B := B) (T := T) hg hT
  have hζ' : 0 < restartLife ζ T ω' := tsub_pos_of_lt hT
  have hpos : 0 < capStop r G (restartLife ζ T) (restartDrv W T) ω' := by
    unfold capStop
    rw [localStop_of_mem hω]
    exact lt_min (localStopPath_pos hp'.2.2.2.1 hp'.1 hr hζ') hζ'
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (capStop_restart_ne_top (G := G) (r := r) (ζ := ζ) (W := W)
    (T := T) ω')
  refine ⟨s, hs.symm, ?_, ?_⟩
  · rw [← hs] at hpos; exact WithTop.coe_lt_coe.1 hpos
  · have h := capStop_le (G := G) (ζ := restartLife ζ T) (W := restartDrv W T) r ω'
    rw [← hs] at h
    exact h

/-- **On the cell event the cell stop is strictly after `τ` and not after `ζ`.** -/
theorem lt_cellStop_and_le (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {c : CellCode nL nR} {ω : Ω}
    (hω : ω ∈ cellEvent τ G ζ W VL VR c) :
    τ ω < cellStop τ G ζ W c ω ∧ cellStop τ G ζ W c ω ≤ (ζ ω : WithTop ℝ≥0) := by
  obtain ⟨s, hs, hs0, hsζ⟩ := exists_capStop_restart_pos (B := B) (hG ω hω.1) hω.2.2.2.1 hω.1 c.radius_pos
  have hcs : cellStop τ G ζ W c ω = ((cellTime τ c ω + s : ℝ≥0) : WithTop ℝ≥0) := by
    simp only [cellStop, restartTime, hs, WithTop.untopD_coe]
  rw [hcs, ← coe_cellTime_of_mem hω]
  refine ⟨WithTop.coe_lt_coe.2 (lt_add_of_pos_right _ hs0), ?_⟩
  change ((cellTime τ c ω + s : ℝ≥0) : ℝ≥0∞) ≤ ζ ω
  rw [ENNReal.coe_add]
  calc ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) + s ≤ (cellTime τ c ω : ℝ≥0∞) + (ζ ω - cellTime τ c ω) :=
        add_le_add le_rfl hsζ
    _ = ζ ω := add_tsub_cancel_of_le hω.2.2.2.1.le

end CellStop

/-! ### The cell of the recorded history is the cell event -/

section CellIff

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0} {G : Set Ω}

/-- The history stopped at a finite `T < ζ` has the current state `X_T`. -/
theorem histState_stoppedHistory_of_lt {ω : Ω} {T : ℝ≥0} (hτ : τ ω = T) (hT : (T : ℝ≥0∞) < ζ ω) :
    histState (stoppedHistory (completedState W VL VR ζ) τ ω) = drivingState W VL VR T ω := by
  rw [histState_stoppedHistory _ hτ]
  exact ite_eq_left hT

/-- **The recorded history lies in the cell iff the point lies in the cell event** (on the good event, for an
admissible code and an admissible initial seed). At `τ = ζ` the current state is the terminal state, at which the
threshold condition holds, so no admissible cell contains it. -/
theorem mem_cellSet_iff (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hτζ : ∀ ω, τ ω ≤ (ζ ω : WithTop ℝ≥0))
    {c : CellCode nL nR} (hc : IsAdmCode ρL ρR c) {ω : Ω} (hω : ω ∈ G) :
    stoppedHistory (completedState W VL VR ζ) τ ω ∈ cellSet c ↔ ω ∈ cellEvent τ G ζ W VL VR c := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hτT : τ ω = (cellTime τ c ω : WithTop ℝ≥0) := (coe_cellTime_of_lt h2).symm
    rw [histState_stoppedHistory _ hτT] at h3
    have hlt : ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      have hle : ((cellTime τ c ω : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := by
        have h := hτζ ω
        rw [hτT] at h
        exact h
      refine lt_of_le_of_ne hle fun heq => ?_
      -- at `ζ` the completed state is the terminal state, where the threshold condition holds
      have hg := hG ω hω
      have hpos : 0 < cellTime τ c ω := by
        have h0 := hg.zeta_pos hseed
        rw [← heq] at h0
        exact_mod_cast h0
      obtain ⟨w₀, vL₀, vR₀, hL, hth⟩ := hg.2 (cellTime τ c ω) hpos heq
      have : NeBot (𝓝[<] (cellTime τ c ω)) := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      have hval : completedState W VL VR ζ (cellTime τ c ω) ω = (w₀, vL₀, vR₀) := by
        rw [completedState, ite_eq_right (by rw [heq]; exact lt_irrefl _)]
        exact hL.limUnder_eq
      rw [hval] at h3
      exact not_thresholdCondition_of_isCellState hc h3 hth
    refine ⟨hω, h1, h2, hlt, ?_⟩
    rw [pvState_eq (hG ω hω) hlt]
    have e : completedState W VL VR ζ (cellTime τ c ω) ω = drivingState W VL VR (cellTime τ c ω) ω :=
      ite_eq_left hlt
    rw [e] at h3
    exact h3
  · rintro ⟨-, h1, h2, hlt, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [histState_stoppedHistory_of_lt (coe_cellTime_of_lt h2).symm hlt, ← pvState_eq (hG ω hω) hlt]
    exact h3

end CellIff

end LocalExt

end InteractingSLE
