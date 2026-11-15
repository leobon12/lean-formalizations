/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistReference

/-! # Retain the actual initial harmonic mean as a past mark

The initial conditional mean is measurable for the initial conditioning
sigma-algebra. Including it in the retained record therefore preserves
the Gaussian law, and makes history factorization automatic. Later
decompositions are preserved whenever their marks contain the initial marks.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GHist
open Aux61Fib (FibCode FibData)
open Aux61ChLoc (IsChartGaussAt)

universe u

/-- Retained history with its actual initial Gaussian mean. -/
def meanHistory {X β : Type*} (Z : X → β) (h₀ : X → DistOn upperHalfPlaneOpens)
    (x : X) : β × DistOn upperHalfPlaneOpens := (Z x, h₀ x)

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β] {μ : Measure X}
  {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₀ h₁ : X → DistOn upperHalfPlaneOpens}

theorem measurable_meanHistory (hZ : Measurable Z) (hh₀ : Measurable h₀) :
    Measurable (meanHistory Z h₀) := hZ.prodMk hh₀

/-- Recording a conditioning-measurable initial mean changes neither
the live event nor the conditional Gaussian decomposition. -/
theorem isChartGaussAt_meanHistory (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hh₀ : Measurable[𝒢] h₀) :
    IsChartGaussAt μ (meanHistory Z h₀) (B ×ˢ univ) Y q 𝒢 h₁ := by
  refine ⟨hG.le, ?_, hG.marksY, hG.measurable, ?_, ?_⟩
  · exact ((Measurable.of_comap_le hG.marksZ).prodMk hh₀).comap_le
  · filter_upwards [hG.harmonic] with x hx hxB hxq
    exact hx hxB.1 hxq
  · intro φ
    filter_upwards [hG.gff φ] with x hx hxB hxq
    exact hx hxB.1 hxq

/-- No extra history-measurability premise on the actual initial mean
is needed if it is explicitly retained. Its reference continuation is
harmonic under the enlarged history law and preserves the initial Gaussian law. -/
theorem exists_reference_factor_of_initialGauss [IsFiniteMeasure μ]
    (d : FibData) (hZ : Measurable Z) (hY : Measurable Y) (hB : MeasurableSet B)
    (hG : IsChartGaussAt μ Z B Y 0 𝒢 h₀)
    (hlive : ∀ᵐ x ∂μ, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life) :
    ∃ T₀ : β × DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, Z x ∈ B → T₀ (meanHistory Z h₀ x) = h₀ x) ∧
      (∀ b : β × DistOn upperHalfPlaneOpens, b.1 ∉ B → T₀ b = referenceDist d) ∧
      (∀ᵐ b ∂μ.map (meanHistory Z h₀), IsHarmonicDistOn (T₀ b) H) ∧
      IsChartGaussAt μ (meanHistory Z h₀) (B ×ˢ univ) Y 0 𝒢
        (fun x => T₀ (meanHistory Z h₀ x)) := by
  have hZ' := measurable_meanHistory hZ (hG.measurable.mono hG.le le_rfl)
  have hG' := isChartGaussAt_meanHistory hG hG.measurable
  have hm : Measurable[(mβ.prod inferInstance).comap (meanHistory Z h₀)] h₀ :=
    measurable_snd.comp (comap_measurable (meanHistory Z h₀))
  have hlive' : ∀ᵐ x ∂μ, meanHistory Z h₀ x ∈ B ×ˢ univ → (0 : ℝ≥0∞) < (Y x).life :=
    hlive.mono fun x hx hxB => hx hxB.1
  obtain ⟨T₀, hT₀, he, hoff, hharm, hg⟩ :=
    exists_reference_history_factor d hZ' hY (hB.prod MeasurableSet.univ) hm hG' hlive'
  exact ⟨T₀, hT₀, fun x hx => he x ⟨hx, mem_univ _⟩,
    fun b hb => hoff b (fun hm => hb hm.1), hharm, hg⟩

end InteractingSLE.Sec5.Aux61GHist
