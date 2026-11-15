/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameSched
import InteractingSLE.Spec.Supplement.GW2ConeData

/-!
# The concrete frame on the actual centred counterflow space

The parameter field and its driver come from the existing centred coupling.
Only the deterministic identity of its boundary word with the source's chosen
Fig. 5.1 word is required. Both random-field frame obligations are discharged.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Prop513Bridge
open Sec4 Sec7.StripSysField

/-- On the original probability space, identify the parameter field of a centred
counterflow and recover the Fig. 5.1 field, with its exact GFF and driver laws.
The remaining word premise concerns deterministic boundary data only. -/
theorem exists_frame_of_centered_word {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℝ → ℝ} {J : Finset ℝ} (hg : IsPiecewiseConstantBoundaryData g J)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h g J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hword : ∀ x ∉ counterflowJumps J ∪
      Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}),
      counterflowData κ g x = stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b') x) :
    ∃ F : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
        (chiC (16 / κ)) (h ω) (F ω)) ∧
      IsFlowLineDriver (16 / κ) (counterflowData κ g) (counterflowJumps J) 0 P F W ζ ∧
      IsStripGFF κ P (fig51Source κ x₀ F)
        (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} ∧
      IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P (fig51Source κ x₀ F) W ζ ∧
      ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀))) (-1)
        (-(π * chiC κ)) (chiC (16 / κ)) (fig51Source κ x₀ F ω) (F ω) := by
  obtain ⟨F, hT, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hg hh hcf
  have hbP := isPiecewiseConstant_counterflowData κ hg
  have hGP := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hbP hfl
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hGP hword
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀))) (-1)
      (-(π * chiC κ)) (chiC (16 / κ)) (fig51Source κ x₀ F ω) (F ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (F ω)
  refine ⟨F, hT, hfl, hGF, ?_, hTF⟩
  refine ⟨counterflowData κ g, counterflowJumps J, F, hbP, ?_, hfl⟩
  simpa only [zero_add] using hTF

end InteractingSLE.Sec5.Prop513Bridge
