/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistMarks
import InteractingSLE.Spec.Sec5.Aux61GContEndpoint

/-! # Initial history distribution for the selected-access restart code

The source's finite contact or witnessed window exit gives positive
capacity lifetime. Retaining the actual initial Gaussian mean then supplies
the measurable harmonic history distribution, with reference continuation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GHist
open Aux61GInst Aux61FibData
open Aux61Fib (FibData)
open Aux61ChLoc (IsChartGaussAt)

universe u
variable {X : Type u} {𝒢₀ : MeasurableSpace X} [mX : MeasurableSpace X]
  {Er : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  {a k : ℝ} {h : X → DistOn upperHalfPlaneOpens}

/-- A selected-access exit has positive capacity lifetime, using the
actual simple completed path and its strictly increasing capacity clock. -/
theorem accessExitCode_life_pos (hs : IsRestartSpec Er c ρ T)
    (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : HasAccessLanding Er c ρ T V)
    (hinj : ∀ x ∈ Er, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    {x : X} (hx : x ∈ exitEv Er c ρ T V) :
    0 < (accessExitCode Er c ρ T V a k h x).life := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hc := hp.isClockOn_capClock (isClockOn_accessExitPath hs hV hV0 hland hinj) hx
  have hpos : 0 < capClock (exitEv Er c ρ T V) (accessExitPath Er c ρ T V)
      (exitNN Er c ρ T V) x (exitNN Er c ρ T V x) := by
    have hzero : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (exitNN Er c ρ T V x : ℝ≥0∞)} :=
      show (0 : ℝ≥0∞) ≤ _ from zero_le
    have hend : exitNN Er c ρ T V x ∈
        {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (exitNN Er c ρ T V x : ℝ≥0∞)} :=
      show (exitNN Er c ρ T V x : ℝ≥0∞) ≤ (exitNN Er c ρ T V x : ℝ≥0∞) from le_rfl
    have hlt := hc.strictMonoOn hzero hend (exitNN_pos hs hV hV0 hx)
    simpa only [hc.zero] using hlt
  simp only [accessExitCode_life, capEnd, hx, ↓reduceIte]
  exact ENNReal.ofReal_pos.2 hpos

/-- The cover's physical stop condition supplies its actual measurable
harmonic initial distribution after enriching the retained history by the
initial Gaussian mean. No separate landing limit, positive lifetime,
history factor or harmonicity assumption is needed. -/
theorem exists_reference_factor_of_access_restart
    {β : Type*} [mβ : MeasurableSpace β]
    {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {B : Set β}
    {h₀ : X → DistOn upperHalfPlaneOpens} (d : FibData)
    (hZ : Measurable Z) (hB : MeasurableSet B)
    (hs : IsRestartSpec Er c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding Er c ρ T V)
    (hinj : ∀ x ∈ Er, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    (hliftc : ∀ x ∈ Er, ContinuousOn (c x).2.2 (c x).dom) (hh : Measurable h)
    (hphysical_stop : ∀ᵐ x ∂μ, Z x ∈ B → x ∈ Er ∧ 0 < T x ∧
      (T x < ⊤ ∨ ∃ t : ℝ≥0, (t : ℝ≥0∞) < T x ∧ inPath Er c ρ T x t ∉ V))
    (hG0 : IsChartGaussAt μ Z B (accessExitCode Er c ρ T V a k h) 0 𝒢₀ h₀) :
    ∃ T₀ : β × DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, Z x ∈ B → T₀ (meanHistory Z h₀ x) = h₀ x) ∧
      (∀ b : β × DistOn upperHalfPlaneOpens, b.1 ∉ B → T₀ b = referenceDist d) ∧
      (∀ᵐ b ∂μ.map (meanHistory Z h₀), IsHarmonicDistOn (T₀ b) H) ∧
      IsChartGaussAt μ (meanHistory Z h₀) (B ×ˢ univ)
        (accessExitCode Er c ρ T V a k h) 0 𝒢₀
        (fun x => T₀ (meanHistory Z h₀ x)) := by
  apply exists_reference_factor_of_initialGauss d hZ
    (measurable_accessExitCode hs hV hV0 hland hinj hliftc hh) hB hG0
  filter_upwards [hphysical_stop] with x hx hxB
  obtain ⟨hxE, hpos, hstop⟩ := hx hxB
  exact accessExitCode_life_pos hs hV hV0 hland hinj
    (Aux61GCont.mem_exitEv_of_contact_or_exit hxE hpos hstop)

end InteractingSLE.Sec5.Aux61GHist
