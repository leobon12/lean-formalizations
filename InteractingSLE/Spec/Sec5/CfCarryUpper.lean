/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfCarrySource

/-!
# The upper (4.4) chart statement from raw physical locality alone

Packet PROVE-CFCHART2. The positive branch keeps chart, word reduction and
members jointly, and the zero branch is already proved. No selected-base
reduction hypothesis is used. Physical locality is the explicit remaining input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfCarry

open CfConv CfGiven CfChart Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47 Restart.DomainMarkov.K2
open Sec7.StripHeights44 (IsHeightBounded44)

/-- The complete upper (4.4) chart statement conditional on raw physical members.
The raw premise is quantified explicitly; reduction and zero prefix are proved. -/
theorem cfGivenChart44Up_of_raw_members (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hraw : ∀ {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
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
          (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω))) :
    QSched.CfGivenChart44UpStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s η hη
  by_cases hz : s = 0
  · subst s
    exact CfStep.zeroChart44Statement hA href κ b J P h W ζ hκ hκ4 hb hh hcf hζ
      θ hθ hθh hπh D hDm hDreg hD η hη
  · have hs : 0 < s := lt_of_le_of_ne (zero_le : 0 ≤ s) (Ne.symm hz)
    obtain ⟨d, hbase, hred, hmem⟩ := exists_chartBase_reduction_members44_of_raw
      hA href hκ hκ4 hb hcf hζ hθh hπh hθ hDm hDreg hD hs hη
      (hraw hκ hκ4 hb hh hcf hζ hθh hπh hθ hDm hDreg hD hs hη)
    exact Wire.Night.chart_of_base d hbase hred
      (CfStep.converted44IntegrableOn hA href κ b J P h W ζ hκ hκ4 hb hh hcf hζ
        θ hθ hθh hπh D hDm hDreg hD s hs η hη) hmem

/-- The upper (4.4) chart statement implies the original uniform-height chart
statement; the mirror-height branch is unnecessary under these original hypotheses. -/
theorem cfGivenChartStatement_of_up44 (hUp : QSched.CfGivenChart44UpStatement.{u}) :
    CfGivenChartStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s η hη
  have hπ : π / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith only [Real.pi_pos], le_rfl⟩
  exact hUp κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hθ)
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hπ) D hDm hDreg hD s η hη

/-- The schedule's first-hit theorem from the upper chart statement and its mirror.
Combining this with `cfGivenChart44Up_of_raw_members` eliminates the selected-base leaves. -/
theorem qScheduleFirstHitStatement_of_up44
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hUp : QSched.CfGivenChart44UpStatement.{u}) (hDn : QSched.CfGivenChart44DownStatement.{u}) :
    FrameQ.QScheduleFirstHitStatement.{u} :=
  QSched.qScheduleFirstHitStatement_of_input h44 h47 href
    (QSched.counterflowGivenPrefix44Statement_of_chart44
      (QSched.cfGivenChart44Statement_of_up_down hUp hDn))

end InteractingSLE.Sec5.CfCarry
