/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfChartSetup
import InteractingSLE.Spec.Sec5.CfChartCongr

/-!
# Null-set conversions for the counterflow chart

Packet PROVE-CFCHART2. Regularize the image driver on the complement of the good event and enlarge
the raw filtration by that event. This preserves the chart clause and makes every driver path
continuous, starting at zero. The killing time becomes infinity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open CfGiven CfChart
open LawUnique
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
  {W W₂ : ℝ≥0 → Ω → ℝ} {VL VL₂ : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR VR₂ : Fin nR → ℝ≥0 → Ω → ℝ} {ζ ζ₂ : Ω → ℝ≥0∞} {c c₂ : Ω → Chart} {a k : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- Almost sure equality of the complete chart data preserves the canonical chart clause. -/
theorem IsChartCanon.congr_data_ae (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    (he : ∀ᵐ ω ∂P, ζ₂ ω = ζ ω ∧ c₂ ω = c ω ∧ (∀ t, W₂ t ω = W t ω) ∧
      (∀ i t, VL₂ i t ω = VL i t ω) ∧ ∀ j t, VR₂ j t ω = VR j t ω) :
    IsChartCanon κ ρL ρR P 𝓐 W₂ VL₂ VR₂ ζ₂ c₂ a k h := by
  apply CfChart.IsChartCanon.congr_ae hcan
  intro t φ
  filter_upwards [he] with ω ⟨hζ, hc, hW, hVL, hVR⟩ hE
  have hU : canonU κ ρL ρR W₂ VL₂ VR₂ t ω = canonU κ ρL ρR W VL VR t ω := by
    simp only [canonU, Restart.DomainMarkov.bheProc, hW, hVL, hVR]
  constructor
  · simpa only [chartEv, hζ, hc, hW, mem_ofPred_eq] using hE
  · simp only [chartRhs, hU, hc, hW]

end Congr

section Filtration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Enlarging the original sigma algebra enlarges its almost sure completion. -/
theorem aeSigma_mono {m₁ m₂ : MeasurableSpace Ω} (hm : m₁ ≤ m₂) :
    @aeSigma Ω mΩ P m₁ ≤ @aeSigma Ω mΩ P m₂ := by
  rintro A ⟨B, hB, he⟩
  exact ⟨B, hm _ hB, he⟩

/-- Add the observation of a measurable event at time zero. -/
def eventFiltration (𝓐 : Filtration ℝ≥0 mΩ) (A : Set Ω) (hA : MeasurableSet A) :
    Filtration ℝ≥0 mΩ :=
  𝓐 ⊔ Filtration.const ℝ≥0 (MeasurableSpace.generateFrom {A})
    (MeasurableSpace.generateFrom_le (by intro s hs; rcases hs with rfl; exact hA))

theorem le_eventFiltration (𝓐 : Filtration ℝ≥0 mΩ) (A : Set Ω) (hA : MeasurableSet A) (t : ℝ≥0) :
    𝓐 t ≤ eventFiltration 𝓐 A hA t := le_sup_left

theorem measurableSet_eventFiltration (𝓐 : Filtration ℝ≥0 mΩ) (A : Set Ω) (hA : MeasurableSet A)
    (t : ℝ≥0) : MeasurableSet[eventFiltration 𝓐 A hA t] A :=
  (show MeasurableSpace.generateFrom {A} ≤ eventFiltration 𝓐 A hA t from le_sup_right) _
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton A))

theorem eventFiltration_le_aeSigma (𝓐 : Filtration ℝ≥0 mΩ) {A : Set Ω} (hA : MeasurableSet A)
    (hAe : ∀ᵐ ω ∂P, ω ∈ A) (t : ℝ≥0) : eventFiltration 𝓐 A hA t ≤ aeSigma P (𝓐 t) := by
  refine sup_le (le_aeSigma _ _) (MeasurableSpace.generateFrom_le ?_)
  intro s hs
  rcases hs with rfl
  exact measurableSet_aeSigma_of_ae hAe

open scoped Classical in
/-- Freeze a process to zero outside an event. -/
def eventDriver (A : Set Ω) (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if ω ∈ A then W t ω else 0

omit mΩ in
theorem eventDriver_eq {A : Set Ω} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∈ A) (t : ℝ≥0) :
    eventDriver A W t ω = W t ω := ite_eq_left hω

omit mΩ in
theorem eventDriver_zero {A : Set Ω} {W : ℝ≥0 → Ω → ℝ} (hW : ∀ ω ∈ A, W 0 ω = 0) (ω : Ω) :
    eventDriver A W 0 ω = 0 := by
  classical
  by_cases hω : ω ∈ A
  · rw [eventDriver_eq hω, hW ω hω]
  · exact ite_eq_right hω

omit mΩ in
theorem continuous_eventDriver {A : Set Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ ω ∈ A, Continuous fun t => W t ω) (ω : Ω) :
    Continuous fun t => eventDriver A W t ω := by
  classical
  by_cases hω : ω ∈ A
  · simpa only [eventDriver, ite_eq_left hω] using hW ω hω
  · simpa only [eventDriver, ite_eq_right hω] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ))

theorem stronglyAdapted_eventDriver (𝓐 : Filtration ℝ≥0 mΩ) {A : Set Ω} (hA : MeasurableSet A)
    {W : ℝ≥0 → Ω → ℝ} (hW : StronglyAdapted 𝓐 W) :
    StronglyAdapted (eventFiltration 𝓐 A hA) (eventDriver A W) := by
  classical
  intro t
  exact ((hW t).mono (le_eventFiltration 𝓐 A hA t)).piecewise
    (measurableSet_eventFiltration 𝓐 A hA t) stronglyMeasurable_const

end Filtration

section Image

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}
  {E : Set (Ω × HistorySpace 0 0)} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}

/-- The raw filtration observes the entire killed driver at each fixed time. -/
theorem stronglyAdapted_qW_raw (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) :
    StronglyAdapted (qRaw xL xR W VL VR ζ s E) (qW W VL VR ζ s E) := by
  intro t
  apply Measurable.stronglyMeasurable
  intro A hA
  exact measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inl rfl⟩⟩
    (measurable_qW hX hE hEg t hA)

omit mΩ in
/-- Infinite terminal capacity gives a globally continuous image driver. -/
theorem continuous_qW_of_top (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {p : Ω × HistorySpace 0 0}
    (htop : qT W VL VR ζ s E p = ⊤) : Continuous fun t => qW W VL VR ζ s E t p := by
  have hc := (isKilledCurve_qgCurve (q := s) hEg p).continuousOn_kcW
  have hu : {t : ℝ≥0 | (t : WithTop ℝ≥0) < kcLife (qgCurve W s E p) (qgPre W VL VR ζ s E p)} = univ := by
    ext t
    change ((t : WithTop ℝ≥0) < qT W VL VR ζ s E p) ↔ t ∈ univ
    simp only [htop, WithTop.coe_lt_top, mem_univ]
  rw [hu] at hc
  exact continuousOn_univ.1 hc

end Image

end InteractingSLE.Sec5.CfConv
