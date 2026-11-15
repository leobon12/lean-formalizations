/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGPath
import InteractingSLE.GFF.PushforwardLoewner

/-!
# Aux. lemma 53: the measurable Loewner chart read from a recorded history

Packet PROVE-LOCEXT-G. Specification p. 245, Aux. lemma 53: "condition on the recorded driving history and map the
active field and future hulls by the centered map `f_τ = g_τ − W_τ`, with the inherited logarithmic derivative
branch". The chart `f_T` is read from the recorded history `y = 𝒳_T` (`histDrv`, `LocalExtGPath.lean`):

* **Loewner locality without global continuity**: the hull `K_t` only reads the driver on `[0, t']` for any `t' > t`
  (`fwdHull_congr_of_eqOn_of_lt`; QuantumZipper's version assumes global continuity), hence for drivers continuous on
  `[0, t']`, agreement on `[0, t]` suffices (`fwdHull_congr_of_continuousOn`); the same for the inverse map and the
  Loewner chart `Chart.id.loewner w t` (`id_loewner_congr`);
* `histChart y`: the Loewner chart at the recorded time of the driver read from `y`; conformal for **every** `y`
  (`isConformal_histChart`), with measurable domain events, forward maps and lifts (`measurableSet_mem_dom_histChart`,
  `measurable_indicator_fwd_histChart`, `measurable_indicator_lift_histChart`);
* **`measurable_histChartField`**: the chart field `(h, y) ↦ σ (h ∘ f⁻¹) + a + k (arg f′ ∘ f⁻¹)` of the chart read
  from `y` is a measurable function of `(h, y)`;
* **`restartChart_eq_histChart`**: on a path continuous before `ζ` with `W₀ = 0` and `T < ζ`, the restart chart
  `restartChart W T` of `Sec5.Markov` (the chart of Aux. lemma 53) is the chart read from the recorded history `𝒳_T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace LocalExt

open Sec7

/-! ### Loewner locality -/

section Congr

variable {W W' : ℝ → ℝ} {t t' : ℝ}

/-- **The hull at `t` reads the driver on `[0, t']` only**, for every `t' > t` (no continuity needed). -/
theorem fwdHull_congr_of_eqOn_of_lt (ht : 0 ≤ t) (htt' : t < t') (h : EqOn W W' (Icc 0 t')) :
    fwdHull W t = fwdHull W' t := by
  have key : ∀ {V V' : ℝ → ℝ}, EqOn V V' (Icc 0 t') → ∀ {z : ℂ},
      (∀ T, 0 ≤ T → (∃ u, IsForwardSol V z T u) → T ≤ t) →
      ∀ T, 0 ≤ T → (∃ u, IsForwardSol V' z T u) → T ≤ t := by
    intro V V' hV z hall T hT ⟨u, hu⟩
    by_contra hlt
    push Not at hlt
    have hm : 0 ≤ min T t' := le_min hT (ht.trans htt'.le)
    have hu' := QuantumZipper.isForwardSol_restrict hu hm (min_le_left _ _)
    have hu'' : IsForwardSol V z (min T t') u :=
      (Ito.isForwardSol_iff_of_eqOn (fun s hs => hV ⟨hs.1, hs.2.trans (min_le_right _ _)⟩) u).2 hu'
    exact absurd (hall _ hm ⟨u, hu''⟩) (not_le.2 (lt_min hlt htt'))
  ext z
  rw [QuantumZipper.LoewnerAlgebra.mem_fwdHull_iff ht, QuantumZipper.LoewnerAlgebra.mem_fwdHull_iff ht]
  exact ⟨fun ⟨hz, hall⟩ => ⟨hz, key h hall⟩, fun ⟨hz, hall⟩ => ⟨hz, key h.symm hall⟩⟩

/-- **The hull at `t` of drivers continuous on `[0, t']`, `t' > t`, agreeing on `[0, t]`, is the same.** -/
theorem fwdHull_congr_of_continuousOn (hW : ContinuousOn W (Icc 0 t')) (hW' : ContinuousOn W' (Icc 0 t'))
    (ht : 0 ≤ t) (htt' : t < t') (h : EqOn W W' (Icc 0 t)) : fwdHull W t = fwdHull W' t := by
  have ht' : 0 ≤ t' := ht.trans htt'.le
  have h1 : fwdHull W t = fwdHull (Ito.clampDrv W t') t :=
    fwdHull_congr_of_eqOn_of_lt ht htt' Ito.clampDrv_eqOn.symm
  have h2 : fwdHull W' t = fwdHull (Ito.clampDrv W' t') t :=
    fwdHull_congr_of_eqOn_of_lt ht htt' Ito.clampDrv_eqOn.symm
  rw [h1, h2]
  refine QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn (Ito.continuous_clampDrv ht' hW)
    (Ito.continuous_clampDrv ht' hW') ht fun s hs => ?_
  have hs' : s ∈ Icc 0 t' := ⟨hs.1, hs.2.trans htt'.le⟩
  rw [Ito.clampDrv_eqOn hs', Ito.clampDrv_eqOn hs', h hs]

theorem fwdMapInv_congr_of_continuousOn (hW : ContinuousOn W (Icc 0 t')) (hW' : ContinuousOn W' (Icc 0 t'))
    (ht : 0 ≤ t) (htt' : t < t') (h : EqOn W W' (Icc 0 t)) (w : ℂ) : fwdMapInv W t w = fwdMapInv W' t w := by
  have hK := fwdHull_congr_of_continuousOn hW hW' ht htt' h
  have hf : fwdMap W t = fwdMap W' t := funext fun z => Ito.fwdMap_congr_of_eqOn h
  unfold fwdMapInv
  rw [hK, hf]

/-- **The Loewner chart at `t` of drivers continuous on `[0, t']`, `t' > t`, agreeing on `[0, t]`, is the same.** -/
theorem id_loewner_congr (hW : ContinuousOn W (Icc 0 t')) (hW' : ContinuousOn W' (Icc 0 t'))
    (ht : 0 ≤ t) (htt' : t < t') (h : EqOn W W' (Icc 0 t)) : Chart.id.loewner W t = Chart.id.loewner W' t := by
  unfold Chart.loewner Chart.id
  refine Prod.ext (funext fun z => Ito.fwdMap_congr_of_eqOn h) (Prod.ext (funext fun z => ?_) (funext fun z => ?_))
  · exact congrArg (fun x => x) (fwdMapInv_congr_of_continuousOn hW hW' ht htt' h z)
  · simp only
    rw [Ito.logDerivFwd_congr_of_eqOn h ht le_rfl]

end Congr

/-! ### The chart read from a history -/

section HistChart

variable {nL nR : ℕ}

/-- **The Loewner chart read from a recorded history**: `(f, f⁻¹, arg f′)` of the driver read from `y`
(`histDrv`) at the recorded time `histTime y`. -/
def histChart (y : DrivingHist nL nR) : Chart :=
  Chart.id.loewner (Ito.rpath (histDrv y)) (histTime y)

theorem histChart_eq (y : DrivingHist nL nR) :
    histChart y = Chart.loewnerChartAtTime (fun t y => histDrv y t) histTime y := rfl

theorem isConformal_histChart (y : DrivingHist nL nR) : (histChart y).IsConformal :=
  Chart.isConformal_loewnerChartAtTime (W := fun t y => histDrv y t) (τ := histTime)
    (fun y => continuous_histDrv y) (fun y => histDrv_zero y) y

theorem measurable_stoppedDrv_histDrv (t : ℝ≥0) :
    Measurable (Chart.stoppedDrv (fun t y => histDrv y t) (histTime (nL := nL) (nR := nR)) t) := by
  have h := (measurable_histDrv (nL := nL) (nR := nR)).comp
    (measurable_id.prodMk ((measurable_const (a := t)).min measurable_histTime))
  exact h

theorem measurableSet_mem_dom_histChart (z : ℂ) :
    MeasurableSet {y : DrivingHist nL nR | z ∈ (histChart y).dom} :=
  Chart.measurableSet_mem_dom_loewnerChartAtTime le_rfl (fun y => continuous_histDrv y) (fun y => histDrv_zero y)
    measurable_histTime measurable_stoppedDrv_histDrv z

theorem measurable_indicator_fwd_histChart (z : ℂ) :
    Measurable ({y : DrivingHist nL nR | z ∈ (histChart y).dom}.indicator fun y => (histChart y).1 z) :=
  Chart.measurable_indicator_fwd_loewnerChartAtTime le_rfl (fun y => continuous_histDrv y)
    (fun y => histDrv_zero y) measurable_histTime measurable_stoppedDrv_histDrv z

theorem measurable_indicator_lift_histChart (z : ℂ) :
    Measurable ({y : DrivingHist nL nR | z ∈ (histChart y).dom}.indicator fun y => (histChart y).2.2 z) :=
  Chart.measurable_indicator_lift_loewnerChartAtTime le_rfl (fun y => continuous_histDrv y)
    (fun y => histDrv_zero y) measurable_histTime measurable_stoppedDrv_histDrv z

theorem continuousOn_lift_histChart (y : DrivingHist nL nR) :
    ContinuousOn (histChart y).2.2 (histChart y).dom :=
  Chart.continuousOn_lift_loewner ((continuous_histDrv y).comp continuous_real_toNNReal)
    (by simp [histDrv_zero]) (histTime y).coe_nonneg

/-- **The chart field read from a history is a measurable function of the field and the history**:
`(h, y) ↦ σ (h ∘ f⁻¹) + a + k (arg f′ ∘ f⁻¹)` with `f` the chart read from `y`. -/
theorem measurable_histChartField (σ a k : ℝ) :
    Measurable fun p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR =>
      Chart.chartTransport (isConformal_histChart p.2) σ a k p.1 := by
  have hWs : ∀ t : ℝ≥0, Measurable (Chart.stoppedDrv
      (fun t (p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) => histDrv p.2 t)
      (fun p => histTime p.2) t) := fun t => (measurable_stoppedDrv_histDrv t).comp measurable_snd
  have h := Chart.measurable_chartTransport_loewnerChartAtTime
    (W := fun t (p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) => histDrv p.2 t)
    (τ := fun p => histTime p.2) le_rfl (fun p => continuous_histDrv p.2) (fun p => histDrv_zero p.2)
    (measurable_histTime.comp measurable_snd) hWs (h := fun p => p.1) measurable_fst σ a k
  exact h

end HistChart

/-! ### The restart chart is the chart read from the recorded history -/

section Restart

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The restart chart `f_T` of Aux. lemma 53 is the chart read from the recorded history `𝒳_T`**, on a path
continuous before `ζ` with `W₀ = 0`, at a finite `T < ζ`. -/
theorem restartChart_eq_histChart {T : Ω → ℝ≥0} {ω : Ω}
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    (hT : (T ω : ℝ≥0∞) < ζ ω) :
    Sec5.Markov.restartChart W T ω =
      histChart (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) := by
  obtain ⟨T', hTT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT
  have hTT'' : (T ω : ℝ) < T' := by exact_mod_cast hTT'
  unfold Sec5.Markov.restartChart histChart
  rw [histTime_stoppedHistory]
  refine id_loewner_congr (t' := T') ?_ ?_ (T ω).coe_nonneg hTT'' fun s hs => ?_
  · intro s hs
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      refine lt_of_le_of_lt ?_ hT'ζ
      exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2
    exact ((hWc.continuousAt (((isOpen_Iio (a := ζ ω)).preimage ENNReal.continuous_coe).mem_nhds hsζ)).comp
      continuous_real_toNNReal.continuousAt).continuousWithinAt
  · exact ((continuous_histDrv _).comp continuous_real_toNNReal).continuousOn
  · have hsT : s.toNNReal ≤ T ω := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp only [Ito.rpath]
    rw [histDrv_stoppedHistory hWc hW0 hT, min_eq_left hsT]

end Restart

end LocalExt

end InteractingSLE
