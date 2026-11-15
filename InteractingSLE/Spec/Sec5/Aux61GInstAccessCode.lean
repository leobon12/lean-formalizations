/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessGood

/-! # The measurable restart code using selected-access landing -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Restart Aux61Fib

/-- Restart code completed along the actual path at its window exit. -/
def accessExitCode {X : Type*} (E : Set X) (c : X → Chart)
    (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (a k : ℝ)
    (h : X → DistOn upperHalfPlaneOpens) : X → FibCode :=
  fibRead (chartFieldOf (exitEv E c ρ T V) c a k h)
    (capPath (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V))
    (capEnd (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V))

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → DistOn upperHalfPlaneOpens}

omit [MeasurableSpace X] in
theorem accessExitCode_field (x : X) :
    (accessExitCode E c ρ T V a k h x).field = chartFieldOf (exitEv E c ρ T V) c a k h x := rfl

omit [MeasurableSpace X] in
theorem accessExitCode_life (x : X) :
    (accessExitCode E c ρ T V a k h x).life =
      capEnd (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x := rfl

include hs hV hV0 hland hinj

/-- Measurability needs only the selected left-time limit. -/
theorem measurable_accessExitCode (hliftc : ∀ x ∈ E, ContinuousOn (c x).2.2 (c x).dom)
    (hh : Measurable h) : Measurable (accessExitCode E c ρ T V a k h) := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  exact measurable_fibRead
    (measurable_chartFieldOf hp.measurableSet hs.chart
      (fun x hx => hs.conf x hx.1.1) (fun x hx => hliftc x hx.1.1) hh a k)
    (hp.measurable_capEnd hc) hp.measurable_capPath
    (hp.continuousOn_capPath hc) (hp.capPath_zero hc)

theorem accessExitCode_trace (x : X) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) ≤
      capEnd (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x) :
    (accessExitCode E c ρ T V a k h x).trace u =
      capPath (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) x u := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := isClockOn_accessExitPath hs hV hV0 hland hinj
  exact fibRead_trace (hp.measurable_capEnd hc) hp.measurable_capPath
    (hp.continuousOn_capPath hc) (hp.capPath_zero hc) x hu

/-- All path facts for the access-based code, with the original fibre data. -/
theorem pathGood_accessExitCode (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    {x : X} (hx : x ∈ exitEv E c ρ T V) : PathGood d (accessExitCode E c ρ T V a k h x) := by
  obtain ⟨-, -, hi, hH, hUH, hin, hout⟩ := accessExitPath_facts hs hV hV0 hland hinj hx
  have hne : d.Vᶜ.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hb := d.buffer_compact.isBounded.subset (d.V_sub.trans subset_closure)
    rw [hemp] at hb
    exact NormedSpace.unbounded_univ ℝ ℂ hb
  subst hdV
  exact (isPathSpec_accessExitPath hs hV hV0 hland).pathGood_capPath
    (isClockOn_accessExitPath hs hV hV0 hland hinj) hx hi hH hUH d hℓ hV hne hin hout
    (accessExitCode_life x) fun _ hu => accessExitCode_trace hs hV hV0 hland hinj x hu

end InteractingSLE.Sec5.Aux61GInst
