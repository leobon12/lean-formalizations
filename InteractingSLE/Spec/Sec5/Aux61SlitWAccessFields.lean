/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceGeometry
import InteractingSLE.Spec.Sec5.Aux61MeanIdChart
import InteractingSLE.Spec.Sec5.Aux61GInstGluedLanding

/-! # Selected-access and inherited-lift fields for the physical source -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61FibData Aux61GInst

/-- Shrinking a window can only advance its capped exit time. -/
theorem exitTime_mono_window {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V U : Set ℂ} (hVU : V ⊆ U) (x : X) :
    Aux61FibData.exitTime E c ρ T V x ≤ Aux61FibData.exitTime E c ρ T U x := by
  classical
  apply iSup_mono
  intro a
  by_cases hx : x ∈ winEv E c ρ T V (a : ℝ≥0)
  · have hxU : x ∈ winEv E c ρ T U (a : ℝ≥0) :=
      ⟨hx.1, hx.2.1, fun u hu => hVU (hx.2.2 u hu)⟩
    simp only [hx, hxU, ↓reduceIte]
    exact le_rfl
  · simp only [hx, ↓reduceIte]
    exact bot_le

/-- Selected-access landing on a larger window supplies landing on every
subwindow. The contact approach remains the same actual access. -/
theorem hasAccessLanding_mono_window {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V U : Set ℂ} (hVU : V ⊆ U)
    (hland : HasAccessLanding E c ρ T U) : HasAccessLanding E c ρ T V := by
  intro x hx hpos heq hfin
  have heqU : Aux61FibData.exitTime E c ρ T U x = T x :=
    le_antisymm (IsRestartSpec.exitTime_le x) (heq ▸ exitTime_mono_window hVU x)
  obtain ⟨L, hLU, hL⟩ := hland x hx hpos heqU hfin
  exact ⟨L, fun hLV => hLU (hVU hLV), hL⟩

/-- The inherited physical branch proves the harmonic-lift field; it is
not an additional input to the selected-access construction. -/
theorem SourceChartGeometry.harmonic_lift {W : ℝ → ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {r : ℝ≥0} {c : Chart} (hg : SourceChartGeometry W η K r c) :
    InnerProductSpace.HarmonicOnNhd c.2.2 c.dom :=
  Aux61MeanId.harmonicOnNhd_of_eqOn c.dom.isOpen
    (Aux61MeanId.harmonicOnNhd_im_physicalRestartLog c.dom.isOpen hg.simply
      (fun _ hz => (hg.retained hz).1) hg.target) hg.lift

/-- Harmonicity of the inherited branch also proves its required continuity. -/
theorem SourceChartGeometry.continuous_lift {W : ℝ → ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {r : ℝ≥0} {c : Chart} (hg : SourceChartGeometry W η K r c) :
    ContinuousOn c.2.2 c.dom := hg.harmonic_lift.continuousOn

end InteractingSLE.Sec5.Aux61SlitW
