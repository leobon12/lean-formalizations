/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWCapacity

/-! # The measurable Galmarino rule for the selected-access code time -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open LawUnique Aux61ULoc Aux61FibData Aux61GInst Restart
open Restart.FlowStopIdentG

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X] {nL nR : ℕ}
  {E : Set X} {cc : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}

/-- The actual inverse clock sends capacity time zero to physical duration zero. -/
theorem accessTime_zero (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E cc ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens} {x : X}
    (hq : 0 < (accessExitCode E cc ρ T V a k h x).life) :
    accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x 0 = 0 := by
  have hx := mem_exitEv_of_lt_accessLife (q := 0) hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hclk := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hcl := hp.isClockOn_capClock hclk hx
  have he := hcl.invClock_apply (r := 0) (by simp)
  simpa only [accessTime, hcl.zero, Real.toNNReal_zero] using he

/-- When the R1 chart is chosen on the initial retained-record space, the
selected-access physical code times have measurable Galmarino versions.
The versions agree at every live chart time, including time zero. -/
theorem exists_selectedAccessRule
    (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E cc ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    (c : Y × HistorySpace nL nR → Chart) (hc : IsMeasChart c) (r : ℝ≥0)
    (Y₀ : X → Y) (R₀ : X → HistorySpace nL nR)
    (hchart : ∀ x ∈ E, cc x = c (Y₀ x, stopRec r (R₀ x)))
    (hρ : ∀ x ∈ E, ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x →
      ρ x u = histTrace 0 (R₀ x) (r + u))
    (a k : ℝ) (h : X → LQGMetric.DistOn upperHalfPlaneOpens) :
    ∃ rule : ℝ≥0 → Y × HistorySpace nL nR → ℝ≥0∞,
      (∀ q, Measurable (rule q)) ∧ (∀ q, IsGalmarinoRule stopRec (rule q)) ∧
      (∀ p, rule 0 p = r) ∧ (∀ q p, rule 0 p ≤ rule q p) ∧
      ∀ (q : ℝ≥0) x, (q : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life →
        rule q (Y₀ x, R₀ x) =
          ((r + accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨capacityRule c r, measurable_capacityRule hc r, isGalmarinoRule_capacityRule c r,
    capacityRule_zero c r, fun q p => ?_, fun q x hq => ?_⟩
  · rw [capacityRule_zero]
    exact start_le_capacityRule c r q p
  · have hx := (mem_exitEv_of_lt_accessLife hq).1.1
    by_cases hq0 : q = 0
    · subst q
      rw [capacityRule_zero, accessTime_zero hs hV hV0 hland hinj hq, add_zero]
    · exact capacityRule_eq_accessTime hs hV hV0 hland hinj (hchart x hx) (hρ x hx)
        (pos_iff_ne_zero.2 hq0) hq

/-- For the actual killed own history, the chart-path reader clause follows
from the generating trace and continuity of the own driving state. -/
theorem restartPath_eq_histTrace_of_killedHistory
    {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {η : ℝ≥0 → ℂ}
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    (hη : IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η t - (0 : ℝ)))
    {r u : ℝ≥0} (hu : ((r + u : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    η (r + u) = histTrace 0 (killedHistory W VL VR ζ ω) (r + u) :=
  (histTrace_killedHistory hc hW0 hη hu).symm

end InteractingSLE.Sec5.Aux61SlitW
