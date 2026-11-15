/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# Lemma 7.1, terminal capacity: the coupling means of the stopped driver

Packet PROVE-LEMMA71B. Continuation of `Lemma71BStop.lean`. If the coupling means of a driver `W` killed at `T` are
local martingales before `min (swallowTime z) T` (`HasMartingaleMeansBefore`), then the coupling means of the stopped
driver `stopDrv W T G n` (with its own geometric force points) are local martingales before
`min (swallowTime z) (exitAbove W T G n)`: up to the exit time the two drivers, their geometric images and their
Loewner chains agree, and the localizing times of `W` stopped at the exit time localize the stopped driver.

## Main results

* `geomR_congr`, `geomL_congr`, `coupProc_congr`: causality of the geometric images and of the coupling process;
* `continuousWithinAt_coupProc_killed`: the coupling process of a driver continuous on `[0, T)` is right-continuous
  before `min (swallowTime z) T` (through the driver frozen after a time before `T`);
* **`isLocalMartingaleBefore_coupProc_stopDrv`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71B

open MartChar MartChar.RealFlow Coupling

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Causality of the geometric images and of the coupling process -/

section Congr

variable {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0}

theorem geomR_congr (hW' : Continuous fun s => W' s ω) (h : ∀ s ≤ t, W s ω = W' s ω)
    (xR : Fin nR → ℝ) (i : Fin nR) : geomR W xR i t ω = geomR W' xR i t ω := by
  refine rightImg_congr (hW'.comp continuous_real_toNNReal) t.coe_nonneg (fun r hr => ?_) (xR i)
  exact h _ (Real.toNNReal_le_iff_le_coe.2 hr.2)

theorem geomL_congr (hW' : Continuous fun s => W' s ω) (h : ∀ s ≤ t, W s ω = W' s ω)
    (xL : Fin nL → ℝ) (i : Fin nL) : geomL W xL i t ω = geomL W' xL i t ω := by
  simp only [geomL]
  congr 1
  have hc : Continuous (Bessel.realPath (fun t ω => -W' t ω) ω) := by
    show Continuous fun s : ℝ => -W' s.toNNReal ω
    exact (hW'.comp continuous_real_toNNReal).neg
  refine rightImg_congr (w' := Bessel.realPath (fun t ω => -W' t ω) ω) hc t.coe_nonneg
    (fun r hr => ?_) (-xL i)
  simp only [Bessel.realPath]
  rw [h _ (Real.toNNReal_le_iff_le_coe.2 hr.2)]

theorem coupProc_congr {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ}
    (h : ∀ s ≤ t, W s ω = W' s ω) (hL : ∀ i, VL i t ω = VL' i t ω) (hR : ∀ i, VR i t ω = VR' i t ω)
    (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (z : ℂ) :
    coupProc κ ρL ρR W VL VR z t ω = coupProc κ ρL ρR W' VL' VR' z t ω := by
  simp only [coupProc]
  rw [couplingMean_congr (w := wpath W ω) (w' := wpath W' ω) t.coe_nonneg
    (fun r hr => h _ (Real.toNNReal_le_iff_le_coe.2 hr.2)), h t le_rfl]
  simp only [hL, hR]

end Congr

/-! ### Ordering of the geometric images -/

theorem le_geomR {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : Continuous fun s => W s ω) (xR : Fin nR → ℝ)
    (i : Fin nR) (t : ℝ≥0) : W t ω ≤ geomR W xR i t ω := by
  have h := le_rightImg (w := Bessel.realPath W ω) (hW.comp continuous_real_toNNReal) (xR i)
    t.coe_nonneg
  rw [realPath_coe] at h
  exact h

theorem geomL_le {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : Continuous fun s => W s ω) (xL : Fin nL → ℝ)
    (i : Fin nL) (t : ℝ≥0) : geomL W xL i t ω ≤ W t ω := by
  have hc : Continuous (Bessel.realPath (fun t ω => -W t ω) ω) := by
    show Continuous fun s : ℝ => -W s.toNNReal ω
    exact (hW.comp continuous_real_toNNReal).neg
  have h := le_rightImg (w := Bessel.realPath (fun t ω => -W t ω) ω) hc (-xL i) t.coe_nonneg
  rw [realPath_coe] at h
  simp only [geomL]
  linarith

/-! ### Right-continuity of the killed coupling process -/

section Killed

variable {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- **The coupling process of a driver continuous on `[0, T)` is right-continuous before `min (swallowTime z) T`.**
Before a time `s₂ < min (swallowTime z) T` the driver agrees with the driver frozen after `s₂`, which is continuous,
so `continuousWithinAt_coupProc` applies. -/
theorem continuousWithinAt_coupProc_killed {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) {z : ℂ} (hz : z ∈ H)
    (ω : Ω) (s : ℝ≥0)
    (hs : (s : WithTop ℝ≥0) < min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω)) :
    ContinuousWithinAt (coupProc κ ρL ρR W (geomL W xL) (geomR W xR) z · ω) (Ici s) s := by
  obtain ⟨s₁, hss₁, hs₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  obtain ⟨s₂, hs₁₂, hs₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs₁
  have hss₂ : s < s₂ := (ENNReal.coe_lt_coe.1 hss₁).trans (ENNReal.coe_lt_coe.1 hs₁₂)
  have hs₂T : (s₂ : ℝ≥0∞) < T ω := lt_of_lt_of_le hs₂ (min_le_right _ _)
  have hs₂sw : (s₂ : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) :=
    lt_of_lt_of_le hs₂ (min_le_left _ _)
  -- the driver frozen after `s₂`
  set Wf : ℝ≥0 → Ω → ℝ := fun t _ => W (min t s₂) ω with hWf
  have hmem : ∀ t : ℝ≥0, min t s₂ ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun t =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right t s₂) hs₂T
  have hWfc : ∀ ω', Continuous fun t => Wf t ω' := fun _ =>
    (hc ω).comp_continuous (continuous_id.min continuous_const) hmem
  have hagree : ∀ t ≤ s₂, W t ω = Wf t ω := fun t ht => by simp only [hWf, min_eq_left ht]
  -- the frozen driver does not swallow `z` before `s₂`
  have hsw : (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath Wf ω) z : WithTop ℝ≥0) := by
    have hmin := min_swallowTime_congr (w := wpath W ω) (w' := wpath Wf ω) (c := s₂)
      (fun r _ hr => hagree _ (WithTop.coe_le_coe.1 hr)) hz
    have h1 : min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (s₂ : WithTop ℝ≥0) =
        (s₂ : WithTop ℝ≥0) := min_eq_right hs₂sw.le
    have h2 : (s₂ : WithTop ℝ≥0) ≤ (QuantumZipper.swallowTime (wpath Wf ω) z : WithTop ℝ≥0) :=
      le_trans (le_of_eq (h1.symm.trans hmin)) (min_le_left _ _)
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hss₂) h2
  have hcont := continuousWithinAt_coupProc (κ := κ) (ρL := ρL) (ρR := ρR) hWfc
    (fun i ω' => (isForcePath_geomL hWfc xL ω' i).1) (fun i ω' => (isForcePath_geomR hWfc xR ω' i).1)
    (fun ω' t i => geomL_le (hWfc ω') xL i t) (fun ω' t i => le_geomR (hWfc ω') xR i t) hz ω s hsw
  -- the two coupling processes agree on `[0, s₂]`
  have heq : ∀ t ≤ s₂, coupProc κ ρL ρR W (geomL W xL) (geomR W xR) z t ω =
      coupProc κ ρL ρR Wf (geomL Wf xL) (geomR Wf xR) z t ω := fun t ht =>
    coupProc_congr (fun r hr => hagree r (hr.trans ht))
      (fun i => geomL_congr (hWfc ω) (fun r hr => hagree r (hr.trans ht)) xL i)
      (fun i => geomR_congr (hWfc ω) (fun r hr => hagree r (hr.trans ht)) xR i) κ ρL ρR z
  refine hcont.congr_of_eventuallyEq ?_ (heq s hss₂.le)
  filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds hss₂)] with t ht
  exact heq t ht

end Killed

/-! ### The coupling means of the stopped driver -/

section Transfer

variable {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- Up to the exit time, the stopped driver, its geometric images and its coupling process agree with those of `W`. -/
theorem coupProc_stopDrv_eq {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {n : ℝ} {ω : Ω} (hW0 : W 0 ω = 0)
    (hc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) {z : ℂ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ exitAbove W T G n ω) :
    coupProc κ ρL ρR (stopDrv W T G n) (geomL (stopDrv W T G n) xL) (geomR (stopDrv W T G n) xR) z t ω =
      coupProc κ ρL ρR W (geomL W xL) (geomR W xR) z t ω := by
  have hagree : ∀ r ≤ t, W r ω = stopDrv W T G n r ω := fun r hr =>
    (stopDrv_eq_of_le hW0 hunb ((WithTop.coe_le_coe.2 hr).trans ht)).symm
  have hcs := continuous_stopDrv (n := n) hW0 hc hunb
  exact (coupProc_congr hagree (fun i => geomL_congr hcs hagree xL i)
    (fun i => geomR_congr hcs hagree xR i) κ ρL ρR z).symm

/-- The exit time comes no later than `T`. -/
theorem exitAbove_le {n : ℝ} {ω : Ω}
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) :
    exitAbove W T G n ω ≤ (T ω : WithTop ℝ≥0) := by
  by_cases hω : ω ∈ G
  · rcases eq_or_ne (exitAbove W T G n ω) ⊤ with htop | hne
    · have hT : T ω = ⊤ := by
        by_contra hT
        exact exitAbove_ne_top hω (hunb hω) hT htop
      rw [hT]
      exact le_top
    · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [← hu]
      exact (lt_of_exitAbove_eq hω hu.symm).le
  · rw [exitAbove_of_notMem hω]
    exact zero_le

/-- **The coupling means of the stopped driver are local martingales before `min (swallowTime z) (exitAbove)`**,
when those of the killed driver are local martingales before `min (swallowTime z) T`. -/
theorem isLocalMartingaleBefore_coupProc_stopDrv {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    {P : Measure Ω} [IsFiniteMeasure P] {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hm : HasMartingaleMeansBefore κ xL xR ρL ρR P 𝓖 W T)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G)
    (hunb : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (n : ℝ) {z : ℂ} (hz : z ∈ H) :
    IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath (stopDrv W T G n) ω) z : WithTop ℝ≥0)
        (exitAbove W T G n ω))
      (coupProc κ ρL ρR (stopDrv W T G n) (geomL (stopDrv W T G n) xL) (geomR (stopDrv W T G n) xR) z) := by
  set τ := exitAbove W T G n with hτdef
  have hτ : IsStoppingTime 𝓖 τ := isStoppingTime_exitAbove hWa hG hc n
  obtain ⟨σ, hσ, hσζ, hσlim, hσmart⟩ := hm
    (fun ω t => meanExt κ ρL ρR (W t ω) (fun i => geomL W xL i t ω) (fun i => geomR W xR i t ω))
    (fun ω t => isBoundedHarmonicExtension_meanExt κ ρL ρR (W t ω) _ _) z hz
  set X := coupProc κ ρL ρR W (geomL W xL) (geomR W xR) z with hX
  set Xs := coupProc κ ρL ρR (stopDrv W T G n) (geomL (stopDrv W T G n) xL)
    (geomR (stopDrv W T G n) xR) z with hXs
  have hσmart' : ∀ k, Martingale (stoppedProcess X (σ k)) 𝓖 P := hσmart
  -- the swallowing times agree below the exit time
  have hsw : ∀ ω, min (QuantumZipper.swallowTime (wpath (stopDrv W T G n) ω) z : WithTop ℝ≥0) (τ ω) =
      min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (τ ω) := fun ω =>
    min_swallowTime_congr (fun r _ hr => stopDrv_eq_of_le (hW0 ω) (hunb ω) hr) hz
  refine ⟨fun k ω => min (σ k ω) (τ ω), fun k => (hσ k).min hτ, fun k ω => ?_, ?_, fun k => ?_⟩
  · exact (min_le_min ((hσζ k ω).trans (min_le_left _ _)) le_rfl).trans_eq (hsw ω).symm
  · filter_upwards [hσlim] with ω hω r hr
    have hr := lt_of_lt_of_eq hr (hsw ω)
    have hr1 : (r : WithTop ℝ≥0) < min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω) :=
      lt_min (lt_of_lt_of_le hr (min_le_left _ _))
        (lt_of_lt_of_le (lt_of_lt_of_le hr (min_le_right _ _)) (exitAbove_le (hunb ω)))
    filter_upwards [hω r hr1] with k hk
    exact lt_min hk (lt_of_lt_of_le hr (min_le_right _ _))
  · -- the stopped process is `X` stopped at `σ k`, stopped again at the exit time
    have heq : stoppedProcess Xs (fun ω => min (σ k ω) (τ ω)) =
        stoppedProcess (stoppedProcess X (σ k)) τ := by
      funext t ω
      have hne₁ : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hne₂ : min (t : WithTop ℝ≥0) (min (σ k ω) (τ ω)) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      set r := (min (t : WithTop ℝ≥0) (min (σ k ω) (τ ω))).untopA with hr
      have hr' : (r : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (min (σ k ω) (τ ω)) :=
        coe_untopA_of_ne_top hne₂
      have hrτ : (r : WithTop ℝ≥0) ≤ τ ω := by
        rw [hr']; exact (min_le_right _ _).trans (min_le_right _ _)
      have hrhs : (min (((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0) : WithTop ℝ≥0) (σ k ω)).untopA = r := by
        rw [coe_untopA_of_ne_top hne₁]
        congr 1
        rw [min_comm (σ k ω) (τ ω), min_assoc, min_comm (τ ω) (σ k ω)]
      show Xs (min (t : WithTop ℝ≥0) (min (σ k ω) (τ ω))).untopA ω =
        X (min (((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0) : WithTop ℝ≥0) (σ k ω)).untopA ω
      rw [hrhs, ← hr]
      exact coupProc_stopDrv_eq (hW0 ω) (hc ω) (hunb ω) hrτ
    rw [heq]
    exact Martingale.stoppedProcess_of_rightContinuous (hσmart' k)
      (continuousWithinAt_stoppedProcess (hσζ k)
        fun ω s hs => continuousWithinAt_coupProc_killed hc hz ω s hs) hτ

end Transfer

end InteractingSLE.Sec7.Lemma71B
