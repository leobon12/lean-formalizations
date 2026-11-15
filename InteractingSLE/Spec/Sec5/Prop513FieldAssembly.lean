/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513FieldLaw
import InteractingSLE.Spec.Sec5.Prop513FieldNoReturn

/-!
# The strip trace inputs with canonical covariance discharged

Only the centered no-return theorem remains a theorem-valued input. The original
strip GFF and the boundary heights supply the canonical field transport.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

universe u

namespace InteractingSLE.Sec5

open QuantumZipper Sec4

/-- The strip lifetime is infinite, using only the original GFF and heights. -/
theorem stripCounterflow_lifetime_of_stripGFF {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hcanon := Prop513Field.canonicalFieldStatement (x₀ := x₀) hκ hdata.1 hdata.2.1 hG
  obtain ⟨b', J', h', _, hfl, hadm⟩ :=
    exists_admissible_stripCounterflowDriver hκ hdata hcf hcanon
  obtain ⟨h'', 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact (aux6Statement (div_pos (by norm_num) hκ) _ _ _ _ P 𝓕 W VL VR B ζ
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) hadm hC.1).mono fun _ hω => hω.1

/-- The full strict-half-plane trace input follows from the original strip GFF,
its heights, and the centered no-return statement. -/
theorem stripCounterflow_trace_mem_H_of_stripGFF
    (hN : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u})
    {κ x₀ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  have hcanon := Prop513Field.canonicalFieldStatement (x₀ := x₀) hκ hdata.1 hdata.2.1 hG
  have hζ := stripCounterflow_lifetime_of_stripGFF hκ hdata hG hcf
  have hzero := stripCounterflow_noReturn_of_centered hN hκ hκ4 hcf hζ
  exact ae_stripCounterflow_lifetime_eq_top_and_trace_mem_H hκ hdata hcf hcanon hzero

end InteractingSLE.Sec5
