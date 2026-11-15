/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513Trace
import InteractingSLE.Spec.Supplement.GW4Completion
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# The strip no-return input from the centered no-return statement

The parameter field of any strip driver can be returned through the
infinity-source chart. The resulting centered counterflow has exactly the same
driver and lifetime. Its GFF boundary data are the existing `returnData`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5

open Sec4 Sec7.StripSysField

/-- Returning the parameter field gives a centered counterflow with the same
driver and lifetime, so the centered no-return input applies without changing
capacity time. -/
theorem stripCounterflow_noReturn_of_centered
    (hN : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u})
    {κ α q : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hcf : IsStripCounterflowDriver κ α q P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  obtain ⟨b', J', h', hb', _, hfl⟩ := hcf
  have hgff := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hb' hfl
  obtain ⟨u', hu', _⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  have hreturn := isGFFWithBoundaryData_returnField (cfOffset κ) (cfCoeff κ) ⟨u', hu'⟩ hgff
  have hcenter : IsCenteredCounterflowDriver κ P
      (fun ω => returnField (cfOffset κ) (cfCoeff κ) (h' ω)) W ζ :=
    ⟨b', J', h', hb', fun ω => isChartTransport_returnField _ _ (h' ω), hfl⟩
  exact hN κ hκ hκ4 (returnData (cfOffset κ) (cfCoeff κ) b') (returnExcept J')
    (isPiecewiseConstant_returnData _ _ hb') P _ hreturn W ζ hcenter hζ

end InteractingSLE.Sec5
