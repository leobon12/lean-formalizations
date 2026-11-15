/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistHarmonic
import LQGMetric.Field.StandardBorelRange
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Harmonic initial means as measurable retained-history distributions

Doob--Dynkin factorization and measurable harmonicity transfer the actual
initial distribution to the history law. A localized version sets the
factor to zero outside the retained-history piece.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology TopologicalSpace Function
open LQGMetric

namespace InteractingSLE.Sec5.Aux61GHist

variable {X β : Type*} [mβ : MeasurableSpace β] [mX : MeasurableSpace X]
  {μ : Measure X} {Z : X → β} {h₀ : X → DistOn upperHalfPlaneOpens}

/-- An actual history-measurable harmonic mean factors measurably through
the retained history, with harmonicity valid almost surely for its image law. -/
theorem exists_harmonic_history_factor (hZ : Measurable Z)
    (hh₀ : Measurable[mβ.comap Z] h₀) {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (hharm : ∀ᵐ x ∂μ, IsHarmonicDistOn (h₀ x) U) :
    ∃ T₀ : β → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, T₀ (Z x) = h₀ x) ∧ ∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) U := by
  obtain ⟨T₀, hT₀, he⟩ := hh₀.exists_eq_measurable_comp
  refine ⟨T₀, hT₀, fun x => (congrFun he x).symm, ?_⟩
  apply (ae_map_iff hZ.aemeasurable ((measurableSet_isHarmonicDistOn hU).preimage hT₀)).2
  change ∀ᵐ x ∂μ, IsHarmonicDistOn (T₀ (Z x)) U
  simpa only [he, Function.comp_apply] using hharm

/-- The zero distribution is harmonic on every open domain. -/
theorem isHarmonicDistOn_zero (U : Set ℂ) :
    IsHarmonicDistOn (0 : DistOn upperHalfPlaneOpens) U := by
  refine ⟨fun _ => 0, fun _ _ => InnerProductSpace.harmonicAt_const (0 : ℝ), fun ψ _ => ?_⟩
  simp only [zero_mul, integral_zero, zero_apply]

/-- On a measurable retained-history piece B, local harmonicity is enough:
the factor agrees with the actual mean on B and is zero elsewhere. -/
theorem exists_localized_harmonic_history_factor (hZ : Measurable Z)
    (hh₀ : Measurable[mβ.comap Z] h₀) {B : Set β} (hB : MeasurableSet B)
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (hharm : ∀ᵐ x ∂μ, Z x ∈ B → IsHarmonicDistOn (h₀ x) U) :
    ∃ T₀ : β → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, Z x ∈ B → T₀ (Z x) = h₀ x) ∧
      (∀ b ∉ B, T₀ b = 0) ∧ ∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) U := by
  obtain ⟨T, hT, he⟩ := hh₀.exists_eq_measurable_comp
  let T₀ : β → DistOn upperHalfPlaneOpens := B.indicator T
  have hT₀ : Measurable T₀ := hT.indicator hB
  refine ⟨T₀, hT₀, fun x hx => ?_, fun b hb => indicator_of_notMem hb T, ?_⟩
  · exact (indicator_of_mem hx T).trans (congrFun he x).symm
  · apply (ae_map_iff hZ.aemeasurable ((measurableSet_isHarmonicDistOn hU).preimage hT₀)).2
    filter_upwards [hharm] with x hx
    by_cases hxB : Z x ∈ B
    · dsimp only [T₀]
      have hxEq : T (Z x) = h₀ x := (congrFun he x).symm
      rw [indicator_of_mem hxB, hxEq]
      exact hx hxB
    · dsimp only [T₀]
      rw [indicator_of_notMem hxB]
      exact isHarmonicDistOn_zero U

end InteractingSLE.Sec5.Aux61GHist
