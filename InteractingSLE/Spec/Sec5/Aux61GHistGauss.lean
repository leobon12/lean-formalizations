/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistFactor
import InteractingSLE.Spec.Sec5.Aux61OldBCond

/-! # Retained-history factorization preserves the actual Gaussian law

Replacing a mean on a history event also changes the integrand outside
that event. Localization of conditional expectations supplies the required
Gaussian-law identity without an assumption about those outside values.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Function
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GHist
open Aux61Fib (FibCode)
open Aux61ChLoc (IsChartGaussAt)
open Aux61UnionK (measurable_field_apply measurable_apply_of_measurable)

universe u
variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β] {μ : Measure X} [IsFiniteMeasure μ]
  {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₀ h₀' : X → DistOn upperHalfPlaneOpens}

/-- A conditioning-measurable mean agreeing on the selected history event
has the same live conditional Gaussian decomposition there. -/
theorem isChartGaussAt_of_mean_eqOn (hY : Measurable Y) (hB : MeasurableSet B)
    (hG : IsChartGaussAt μ Z B Y q 𝒢 h₀) (hm : Measurable[𝒢] h₀')
    (he : ∀ x, Z x ∈ B → h₀' x = h₀ x) :
    IsChartGaussAt μ Z B Y q 𝒢 h₀' := by
  refine ⟨hG.le, hG.marksZ, hG.marksY, hm, ?_, ?_⟩
  · filter_upwards [hG.harmonic] with x hx hxB hxq
    rw [he x hxB]
    exact hx hxB hxq
  · intro φ
    have hS : MeasurableSet[𝒢] (Z ⁻¹' B) :=
      (Measurable.of_comap_le hG.marksZ) hB
    have hm₀ : Measurable h₀ := hG.measurable.mono hG.le le_rfl
    have hm₀' : Measurable h₀' := hm.mono hG.le le_rfl
    have heq := Aux61ChLoc.ae_condExp_eq_of_eqOn (μ := μ) hS
      (Aux61OldB.integrable_cexp ((measurable_field_apply hY φ).sub
        (measurable_apply_of_measurable hm₀' φ)))
      (Aux61OldB.integrable_cexp ((measurable_field_apply hY φ).sub
        (measurable_apply_of_measurable hm₀ φ)))
      (fun x hx => by
        dsimp only [Pi.sub_apply]
        rw [he x hx])
    filter_upwards [heq, hG.gff φ] with x hx hg hxB hxq
    exact (hx hxB).trans (hg hxB hxq)

/-- The actual initial Gaussian mean, if measurable for the retained
history, has a measurable history factor harmonic under the history law.
The original conditioning sigma-algebra and Gaussian law are preserved. -/
theorem exists_initial_harmonic_history_factor (hZ : Measurable Z) (hY : Measurable Y)
    (hB : MeasurableSet B) (hh₀ : Measurable[mβ.comap Z] h₀)
    (hG : IsChartGaussAt μ Z B Y 0 𝒢 h₀)
    (hlive : ∀ᵐ x ∂μ, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life) :
    ∃ T₀ : β → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, Z x ∈ B → T₀ (Z x) = h₀ x) ∧
      (∀ b ∉ B, T₀ b = 0) ∧
      (∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) H) ∧
      IsChartGaussAt μ Z B Y 0 𝒢 (fun x => T₀ (Z x)) := by
  have hharm : ∀ᵐ x ∂μ, Z x ∈ B → IsHarmonicDistOn (h₀ x) H := by
    filter_upwards [hG.harmonic, hlive] with x hx hl hxB
    simpa only [Aux61OldB.chartHull_zero, sdiff_empty] using hx hxB (hl hxB)
  obtain ⟨T₀, hT₀, he, hoff, hTharm⟩ :=
    exists_localized_harmonic_history_factor hZ hh₀ hB le_rfl hharm
  refine ⟨T₀, hT₀, he, hoff, hTharm, ?_⟩
  exact isChartGaussAt_of_mean_eqOn hY hB hG
    (hT₀.comp (Measurable.of_comap_le hG.marksZ)) he

end InteractingSLE.Sec5.Aux61GHist
