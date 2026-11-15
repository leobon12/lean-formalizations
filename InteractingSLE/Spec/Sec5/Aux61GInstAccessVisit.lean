/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessCode
import InteractingSLE.Spec.Sec5.Aux61FibDataCover

/-! # Physical endpoint and visit facts for the selected-access code -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal Classical
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Aux61Fib

/-- A positive finite physical hitting time gives a finite window-exit event. -/
theorem mem_exitEv_of_finite {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {x : X}
    (hx : x ∈ E) (hT0 : 0 < T x) (hfin : T x < ⊤) : x ∈ exitEv E c ρ T V :=
  ⟨⟨hx, hT0⟩, (IsRestartSpec.exitTime_le x).trans_lt hfin⟩

/-- Reading in capacity time preserves a visit at the completed endpoint. -/
theorem accessExitCode_mem_visitSet {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
    (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    {a k p q y : ℝ} {h : X → DistOn upperHalfPlaneOpens}
    {x : X} (hx : x ∈ exitEv E c ρ T V) (hy : y ∈ Ioo p q)
    (he : accessExitPoint E c ρ T V x = (y : ℂ)) :
    accessExitCode E c ρ T V a k h x ∈ visitSet p q := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hm : (y : ℂ) ∈ accessExitPath E c ρ T V x '' Iic (exitNN E c ρ T V x) :=
    ⟨_, mem_Iic.2 le_rfl, by simpa [accessExitPath, hx] using he⟩
  rw [← hp.image_capPath hc hx] at hm
  obtain ⟨u, hu, heq⟩ := hm
  refine ⟨u, (accessExitCode_life x) ▸ hu, y, hy, ?_⟩
  rw [accessExitCode_trace hs hV hV0 hland hinj x hu]
  exact heq

end InteractingSLE.Sec5.Aux61GInst
