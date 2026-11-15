/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfCarryUpper
import InteractingSLE.Spec.Sec5.CfDownMain

/-! # Restart charts and schedules from literal raw physical members

The positive chart and its reduction are constructed jointly by CFCARRY;
zero prefix and integrability are proved. CFDOWN supplies the reflected chart.
-/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Relay
open Sec5 Sec5.CfConv Sec5.CfGiven Sec5.CfChart Exist Exist.Staged Exist.StagedLaw Restart LawUnique
  Sec5.Lemma47Angle Sec5.CrossRestart.KernelQ Sec5.CrossRestart.KernelQ.Kill47 Restart.DomainMarkov.K2
open Sec7.StripHeights44 (IsHeightBounded44)

/-- CFCARRY's exact raw physical locality premise, on explicitly quantified raw data. -/
def RawChartMembersOn : Prop :=
  ∀ {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (_hκ : 0 < κ) (_hκ4 : κ < 4) (_hb : IsPiecewiseConstantBoundaryData b J)
    (_hh : IsGFFWithBoundaryData P h b J)
    (_hcf : IsCenteredCounterflowDriver κ P h W' ζ') (_hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (_hθh : IsHeightBounded44 κ b J θ) (_hπh : IsHeightBounded44 κ b J (π / 2))
    (_hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (_hDm : Measurable D)
    (_hDreg : ∀ ω, IsRegularDriver (D ω))
    (_hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (_hs : 0 < s) {η : Ω → ℝ≥0 → ℂ}
    (_hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
      let W := fun t ω => (D ω).1 t
      let ζ := fun ω => (D ω).2
      let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0)
      let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0)
      ∀ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
        (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (N : Set Ω)
        (E : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0))
        (hι : Measurable fun ω => (toCoarse (coarseSigma h' W VL VR ζ N) ω,
          Cond44Ref.cfHistory W' ζ' ω)),
        (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω)) →
        IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0)
          (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) P 𝓕 W VL VR B ζ h' →
        P N = 0 → coarseSigma h' W VL VR ζ N ≤ mΩ → MeasurableSet E →
        (∀ p ∈ E, IsGood47 W VL VR ζ p) →
        (∀ p ∈ E, qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E p = ⊤) →
        (∀ᵐ ω ∂P, (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω) ∈ E) →
        HasSafeMembers P
          (Coupling.filtrationComap
            (qRaw (Ω := Coarse (coarseSigma h' W VL VR ζ N)) x y W VL VR ζ s E) hι)
          univ (fun ω => qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E
            (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω))
          (fun t ω => qW (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E t
            (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω))
          (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω))

/-- CFCARRY and CFDOWN give both consumers from raw locality, with no selected-witness leaf. -/
theorem qAndChart_of_raw (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hraw : RawChartMembersOn.{u}) :
    FrameQ.QScheduleFirstHitStatement.{u} ∧ CfGivenChartStatement.{u} := by
  have hUp := CfCarry.cfGivenChart44Up_of_raw_members hA href hraw
  exact ⟨CfCarry.qScheduleFirstHitStatement_of_up44 h44 h47 href hUp (CfDown.cfGivenChart44Down_of_up hUp),
    CfCarry.cfGivenChartStatement_of_up44 hUp⟩

end InteractingSLE.Wire.Relay
