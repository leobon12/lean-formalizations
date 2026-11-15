/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutRawLaw
import InteractingSLE.Spec.Sec7.LocalExtGKernel
import InteractingSLE.Spec.Sec7.PocketStopWallsFinHull
import InteractingSLE.Spec.Sec7.LocalExtASetup

/-! # The actual ambient chart in the marked raw-union comparison (R98 §2) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketStopSide PocketStopWallsFin R5Enl LocalExt

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bdrv : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- The original-time ambient chart is a valid retained reference on a
fixed probability-one event. A marked raw union containing its hull then
has the ambient increment law, for every version of the two means.
The event is in the original driving record, before the walls are added. -/
theorem exists_ambientRawIncrementLawOn
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bdrv ζ h) (hκ : 0 < κ)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    (hℋ : ℋ ≤ mΩ) (hInfo : drivingFiltration P hX s ≤ ℋ)
    {B : Ω → Set ℂ} (hBm : Measurable[ℋ, hittingSigma] B)
    (hBreg : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBloc : IsHistoryAvoidanceLocal ℋ B (centredField h u) P)
    (hSub : ∀ ω, regHull W ζ s ω ∩ H ⊆ B ω) :
    ∃ G : Set Ω, MeasurableSet[drivingFiltration P hX s] G ∧ P Gᶜ = 0 ∧
      (∀ ω ∈ G, (Sec5.Markov.restartChart W (fun _ => s) ω).IsConformal ∧
        ((Sec5.Markov.restartChart W (fun _ => s) ω).dom : Set ℂ) = H \ regHull W ζ s ω) ∧
      ∀ gK : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (regHull W ζ s) (centredField h u) P gK →
        ∀ gB : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B (centredField h u) P gB →
          HasOldChartIncrementLawOn P G (Sec5.Markov.restartChart W (fun _ => s))
            (curOn univ fun ω => H \ B ω) gK gB := by
  have hτ := isStoppingTime_const (drivingFiltration P hX) s
  obtain ⟨Y, hYm, hYeq⟩ := exists_measurable_stoppedHistory_version (κ := κ) (xL := xL) (xR := xR)
    (ρL := ρL) (ρR := ρR) (B := Bdrv) hX hτ
  rw [IsStoppingTime.measurableSpace_const] at hYm
  let Good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => Bdrv t ω) (ζ ω) ∧ ζ ω = ⊤
  have hGood : ∀ᵐ ω ∂P, Good ω := (hC.1.2.2.2.2).and hζ
  let G : Set Ω := (toMeasurable P {ω | ¬ Good ω})ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hG0 : P Gᶜ = 0 := by
    rw [show Gᶜ = toMeasurable P {ω | ¬ Good ω} by simp only [G, compl_compl], measure_toMeasurable]
    exact ae_iff.1 hGood
  have hGG : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra hbad
    exact hω (subset_toMeasurable P {ω | ¬ Good ω} hbad)
  have hG : MeasurableSet[drivingFiltration P hX s] G :=
    (drivingFiltration P hX).mono (zero_le (a := s)) _
      (measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0)
  have hChart : ∀ ω ∈ G, Sec5.Markov.restartChart W (fun _ => s) ω = histChart (Y ω) := by
    intro ω hω
    obtain ⟨hp, hLife⟩ := hGG ω hω
    have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hLife]; exact ENNReal.coe_lt_top
    rw [hYeq ω hp hsζ]
    exact restartChart_eq_histChart hp.2.2.2.1 hp.1 hsζ
  have hConf : ∀ ω ∈ G, (Sec5.Markov.restartChart W (fun _ => s) ω).IsConformal := by
    intro ω hω
    rw [hChart ω hω]
    exact isConformal_histChart _
  have hDom : ∀ ω ∈ G, ((Sec5.Markov.restartChart W (fun _ => s) ω).dom : Set ℂ) = H \ regHull W ζ s ω := by
    intro ω hω
    obtain ⟨hp, hLife⟩ := hGG ω hω
    have hWc : Continuous fun t : ℝ≥0 => W t ω := by
      have he : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by simp [hLife]
      exact continuousOn_univ.1 (he ▸ hp.2.2.2.1)
    have hWr := Chart.continuous_rpath_of_continuous hWc
    have hWr0 := Chart.rpath_zero_of hp.1
    rw [(hConf ω hω).coe_dom, regHull_eq hWc hLife]
    change fwdMapInv (fun t : ℝ => W t.toNNReal ω) s '' H = _
    exact QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 s.coe_nonneg
  have hKm : Measurable[drivingFiltration P hX s, hittingSigma] (regHull W ζ s) := by
    have hm := measurable_regHull_stopping hC hκ hX hζ
      (τ := fun _ => (s : WithTop ℝ≥0)) hτ (fun _ => WithTop.coe_ne_top)
    rw [IsStoppingTime.measurableSpace_const] at hm
    simpa only [WithTop.untopD_coe] using hm
  have hKloc : IsHistoryAvoidanceLocal (drivingFiltration P hX s) (regHull W ζ s) (centredField h u) P := by
    have hl := isHistoryAvoidanceLocal_regHull hC hκ hu hX hζ (fun _ => (s : WithTop ℝ≥0)) hτ
      (fun _ => WithTop.coe_ne_top)
    simpa only [IsStoppingTime.measurableSpace_const, WithTop.untopD_coe] using hl
  have hKreg : ∀ ω, regHull W ζ s ω ⊆ H ∧ IsOpen (H \ regHull W ζ s ω) := fun ω =>
    ⟨fun _ hz => hz.1, QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((continuous_regDrv W ζ ω).comp continuous_real_toNNReal) s.coe_nonneg⟩
  have hFwd : ∀ z, Measurable[drivingFiltration P hX s]
      ((G ∩ {ω | z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom}).indicator
        fun ω => (Sec5.Markov.restartChart W (fun _ => s) ω).1 z) := by
    intro z
    have hFm := (measurable_indicator_fwd_histChart z).comp hYm
    have hEq : ((G ∩ {ω | z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom}).indicator
        fun ω => (Sec5.Markov.restartChart W (fun _ => s) ω).1 z) =
        G.indicator ({ω | z ∈ (histChart (Y ω)).dom}.indicator fun ω => (histChart (Y ω)).1 z) := by
      funext ω
      by_cases hω : ω ∈ G
      · by_cases hz : z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom
        · have hzG : ω ∈ G ∩ {ω | z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom} := ⟨hω, hz⟩
          have hzY : ω ∈ {ω | z ∈ (histChart (Y ω)).dom} := by
            change z ∈ (histChart (Y ω)).dom
            rwa [← hChart ω hω]
          rw [indicator_of_mem hzG, indicator_of_mem hω, indicator_of_mem hzY]
          exact congrArg (fun c : Chart => c.1 z) (hChart ω hω)
        · have hzG : ω ∉ G ∩ {ω | z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom} := fun h => hz h.2
          have hzY : ω ∉ {ω | z ∈ (histChart (Y ω)).dom} := by
            change z ∉ (histChart (Y ω)).dom
            rwa [← hChart ω hω]
          rw [indicator_of_notMem hzG, indicator_of_mem hω, indicator_of_notMem hzY]
      · have hzG : ω ∉ G ∩ {ω | z ∈ (Sec5.Markov.restartChart W (fun _ => s) ω).dom} := fun h => hω h.1
        rw [indicator_of_notMem hzG, indicator_of_notMem hω]
    rw [hEq]
    exact hFm.indicator hG
  refine ⟨G, hG, hG0, fun ω hω => ⟨hConf ω hω, hDom ω hω⟩, ?_⟩
  exact hasAmbientRawIncrementLawOn_of_marked (isZeroBoundaryGFF_centredField hC hu) hInfo hℋ
    hKm hBm hKreg hBreg hKloc hBloc hSub
    ((show drivingFiltration P hX s ≤ germSigma (regHull W ζ s) (centredField h u) ⊔
      drivingFiltration P hX s from le_sup_right) _ hG) hConf
    (fun z => (hFwd z).mono le_sup_right le_rfl) hDom Subset.rfl
    (fun ω _ => dom_curOn_of_mem (mem_univ ω) (hBreg ω).2 sdiff_subset)

end InteractingSLE.Sec7.R5Out
