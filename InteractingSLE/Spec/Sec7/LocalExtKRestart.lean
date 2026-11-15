/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKKer
import InteractingSLE.Spec.Sec7.LocalExtIRestart
import InteractingSLE.Spec.Sec7.LocalExtEStop
import InteractingSLE.Spec.Sec7.LocalExtERestart

/-!
# The restart is a random-word coupling under `P[·|D]`

Packet PROVE-LOCEXT-K. For the data of `RestartSeedCouplingStatement` (a frozen optional hull coupling, a finite stopping
time `T` of its driving filtration `𝓓`, a good event `G`, an admissible seed pattern `(S_L, S_R)` with radius `r`, and a
cell event `D ∈ 𝓓_T` of positive probability) and a `𝓓_T`-measurable version `K̃` of the recorded history `𝒳_T`, the
restarted processes under `P[·|D]` form the random-word setting of `LocalExtKJoint`:

* `admWord r x`: the word `x` if admissible, `(0, 0)` otherwise; `restartWord r K̃ ω`: the current positions read from
  `K̃ ω`, made admissible (`𝓖'₀ = 𝓓_T`-measurable, admissible everywhere, and `= (curL, curR)` on `D ∩ G`);
* **`isWordSetting_restart`**: under `P[·|D]`, with the restarted filtration `𝓖'_s = 𝓓_{T+s}`, the restarted field
  `h' = restartField κ (h, K̃)` and the restarted processes satisfy the coupling clause (PROVE-LOCEXT-I's
  `isCouplingCharFun_restart_cond`) and are almost surely good paths of the word `restartWord r K̃` (`IsWordPath`); the
  seed sums of the word are `∑_{S_L} ρL`, `∑_{S_R} ρR`;
* `isStoppingTime_capStop_restart`: the capped local stop of the restarted path is a stopping time of `𝓖'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)
open Sec7 Sec5.Markov Sec2.Restart

/-! ### The admissible restart word -/

section Word

variable {nL nR : ℕ}

open Classical in
/-- An admissible word: `x` itself if admissible for the radius `r`, otherwise the word with all positions `0`. -/
def admWord (r : ℝ) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : (Fin nL → ℝ) × (Fin nR → ℝ) :=
  if IsAdmWord r x then x else (0, 0)

theorem isAdmWord_zero {r : ℝ} (hr : 0 < r) : IsAdmWord (nL := nL) (nR := nR) r (0, 0) := by
  refine ⟨⟨fun i j _ => le_rfl, fun i => le_rfl, fun i j _ => le_rfl, fun j => le_rfl⟩, hr, fun i hi => ?_,
    fun j hj => ?_⟩
  · exact absurd rfl hi
  · exact absurd rfl hj

theorem isAdmWord_admWord {r : ℝ} (hr : 0 < r) (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : IsAdmWord r (admWord r x) := by
  unfold admWord
  split_ifs with hx
  · exact hx
  · exact isAdmWord_zero hr

theorem admWord_of_adm {r : ℝ} {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) : admWord r x = x := by
  simp only [admWord, hx, ↓reduceIte]

theorem measurable_admWord (r : ℝ) : Measurable (admWord (nL := nL) (nR := nR) r) := by
  classical
  exact Measurable.ite (measurableSet_isAdmWord r) measurable_id measurable_const

/-- **The restart word**: the current positions read from a recorded history, made admissible. -/
def restartWord (r : ℝ) {Ω : Type*} (K : Ω → DrivingHist nL nR) (ω : Ω) : (Fin nL → ℝ) × (Fin nR → ℝ) :=
  admWord r (posL (histState (K ω)), posR (histState (K ω)))

theorem measurable_restartWord (r : ℝ) {Ω : Type*} {m : MeasurableSpace Ω} {K : Ω → DrivingHist nL nR}
    (hK : Measurable K) : Measurable (restartWord r K) :=
  (measurable_admWord r).comp ((measurable_posL.comp (measurable_histState.comp hK)).prodMk
    (measurable_posR.comp (measurable_histState.comp hK)))

end Word

/-! ### The restart under `P[·|D]` -/

section Restart

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {G : Set Ω} {T : Ω → ℝ≥0}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {r : ℝ} {D : Set Ω}

/-- The hypothesis on the cell event `D` in `RestartSeedCouplingStatement`. -/
def IsRestartCell (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (G : Set Ω) (T : Ω → ℝ≥0) (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) (r : ℝ) (D : Set Ω) : Prop :=
  ∀ ω ∈ D, ω ∈ G ∧ (T ω : ℝ≥0∞) < ζ ω ∧ (∀ i, VL i (T ω) ω = W (T ω) ω ↔ i ∈ SL) ∧
    (∀ j, VR j (T ω) ω = W (T ω) ω ↔ j ∈ SR) ∧ IsSeedRadius (curL VL W T ω) (curR VR W T ω) r

/-- On a good path with `T < ζ`, a version of `𝒳_T` gives the current positions as the word. -/
theorem restartWord_eq_cur {K : Ω → DrivingHist nL nR} {ω : Ω}
    (hK : K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (hTζ : (T ω : ℝ≥0∞) < ζ ω) (hadm : IsAdmWord r (curL VL W T ω, curR VR W T ω)) :
    restartWord r K ω = (curL VL W T ω, curR VR W T ω) := by
  have hs : histState (K ω) = drivingState W VL VR (T ω) ω := by
    rw [hK]; exact histState_stoppedHistory_of_lt rfl hTζ
  have e : (posL (histState (K ω)), posR (histState (K ω))) = (curL VL W T ω, curR VR W T ω) := by
    rw [hs]; rfl
  rw [restartWord, e, admWord_of_adm hadm]

/-- The seed sums of the current positions on the cell. -/
theorem seedSumL_curL {ω : Ω} (hpat : ∀ i, VL i (T ω) ω = W (T ω) ω ↔ i ∈ SL) :
    seedSumL (curL VL W T ω) ρL = ∑ i ∈ SL, ρL i := by
  classical
  rw [seedSumL, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ SL)]
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => i ∈ SL), seedWtL (curL VL W T ω) ρL i = ρL i := fun i hi => by
    have hi' : i ∈ SL := (Finset.mem_filter.1 hi).2
    simp only [seedWtL, curL, sub_eq_zero, (hpat i).2 hi', ↓reduceIte]
  have h2 : ∀ i ∈ Finset.univ.filter (fun i => i ∉ SL), seedWtL (curL VL W T ω) ρL i = 0 := fun i hi => by
    have hi' : i ∉ SL := (Finset.mem_filter.1 hi).2
    have : ¬ VL i (T ω) ω - W (T ω) ω = 0 := fun h0 => hi' ((hpat i).1 (sub_eq_zero.1 h0))
    simp only [seedWtL, curL, this, ↓reduceIte]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  congr 1
  ext i; simp

theorem seedSumR_curR {ω : Ω} (hpat : ∀ j, VR j (T ω) ω = W (T ω) ω ↔ j ∈ SR) :
    seedSumR (curR VR W T ω) ρR = ∑ j ∈ SR, ρR j := by
  classical
  rw [seedSumR, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ SR)]
  have h1 : ∀ j ∈ Finset.univ.filter (fun j => j ∈ SR), seedWtR (curR VR W T ω) ρR j = ρR j := fun j hj => by
    have hj' : j ∈ SR := (Finset.mem_filter.1 hj).2
    simp only [seedWtR, curR, sub_eq_zero, (hpat j).2 hj', ↓reduceIte]
  have h2 : ∀ j ∈ Finset.univ.filter (fun j => j ∉ SR), seedWtR (curR VR W T ω) ρR j = 0 := fun j hj => by
    have hj' : j ∉ SR := (Finset.mem_filter.1 hj).2
    have : ¬ VR j (T ω) ω - W (T ω) ω = 0 := fun h0 => hj' ((hpat j).1 (sub_eq_zero.1 h0))
    simp only [seedWtR, curR, this, ↓reduceIte]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  congr 1
  ext j; simp

variable (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
  (hX : IsMeasurableKilledDriving W VL VR ζ)
  (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
  (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
  (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
  {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
  (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
    (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)

omit [IsProbabilityMeasure P] in
include hPD hDp in
theorem pos_radius_of_isRestartCell : 0 < r := by
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hPD
  exact (hDp ω hω).2.2.2.2.1

include hC hκ hD hPD hDp hKm hK hG in
/-- The coupling clause of the restart under `P[·|D]` (PROVE-LOCEXT-I). -/
theorem isCouplingCharFun_restartWord :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR (P[|D]) (restartFiltration (drivingFiltration P hX) T hT)
      (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T) (restartLife ζ T)
      (fun ω => restartField κ (h ω, K ω)) :=
  isCouplingCharFun_restart_cond hC hκ hX hT hD hPD hKm
    (ae_of_all _ fun ω hω hTζ => hK ω (hG ω (hDp ω hω).1).1 hTζ)

omit [IsProbabilityMeasure P] in
include hC hKm in
theorem measurable_restartField_word : Measurable fun ω => restartField κ (h ω, K ω) := by
  have h1 := (measurable_restartField (nL := nL) (nR := nR) κ).comp
    (hC.2.1.prodMk (hKm.mono hT.measurableSpace_le le_rfl))
  exact h1

omit [IsProbabilityMeasure P] in
include hKm in
/-- The restart word is known at time `0` of the restarted filtration. -/
theorem measurable_restartWord_zero :
    Measurable[restartFiltration (drivingFiltration P hX) T hT 0] (restartWord r K) := by
  rw [restartFiltration_zero]
  exact measurable_restartWord r hKm

omit [IsProbabilityMeasure P] in
include hPD hDp in
theorem isAdmWord_restartWord (ω : Ω) : IsAdmWord r (restartWord r K ω) :=
  isAdmWord_admWord (pos_radius_of_isRestartCell hPD hDp) _

omit [IsProbabilityMeasure P] in
include hDp hK hG in
/-- On the cell the restart word is the current positions, and the restarted path is a good path of it. -/
theorem restartWord_eq_and_isWordPath {ω : Ω} (hω : ω ∈ D) :
    restartWord r K ω = (curL VL W T ω, curR VR W T ω) ∧
      IsWordPath κ ρL ρR (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T)
        (restartBM B T) (restartLife ζ T) (restartWord r K) ω := by
  obtain ⟨hωG, hTζ, -, -, hr⟩ := hDp ω hω
  have hg := hG ω hωG
  have hadm : IsAdmWord r (curL VL W T ω, curR VR W T ω) := ⟨isOrderedForceWord_cur hg hTζ, hr⟩
  have hw := restartWord_eq_cur (hK ω hg.1 hTζ) hTζ hadm
  refine ⟨hw, ?_⟩
  unfold IsWordPath
  rw [hw]
  exact ⟨isIntegratedSLEPath_restart hg hTζ, hasThresholdLimit_restart hg hTζ, not_thresholdCondition_cur hg hTζ⟩

omit [IsProbabilityMeasure P] in
include hD hDp hK hG in
/-- Almost surely under `P[·|D]` the restarted path is a good path of the restart word. -/
theorem ae_isWordPath_restart :
    ∀ᵐ ω ∂(P[|D]), IsWordPath κ ρL ρR (restartDrv W T) (fun i => restartMark (VL i) W T)
      (fun j => restartMark (VR j) W T) (restartBM B T) (restartLife ζ T) (restartWord r K) ω := by
  filter_upwards [ae_cond_mem (hT.measurableSpace_le _ hD)] with ω hω
  exact (restartWord_eq_and_isWordPath hG hDp hK hω).2

omit [IsProbabilityMeasure P] in
include hD hDp hK hG in
/-- Almost surely under `P[·|D]` the seed sums of the restart word are the pattern sums. -/
theorem ae_seedSum_restartWord :
    ∀ᵐ ω ∂(P[|D]), seedSumL (restartWord r K ω).1 ρL = ∑ i ∈ SL, ρL i ∧
      seedSumR (restartWord r K ω).2 ρR = ∑ j ∈ SR, ρR j := by
  filter_upwards [ae_cond_mem (hT.measurableSpace_le _ hD)] with ω hω
  rw [(restartWord_eq_and_isWordPath (ρL := ρL) (ρR := ρR) hG hDp hK hω).1]
  exact ⟨seedSumL_curL (hDp ω hω).2.2.1, seedSumR_curR (hDp ω hω).2.2.2.1⟩

end Restart

end LocalExt

end InteractingSLE
