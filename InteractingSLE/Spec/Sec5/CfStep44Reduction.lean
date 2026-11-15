/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStepZeroFull

/-!
# A positive (4.4) chart retaining its proved word reduction

Packet PROVE-CFCHART2. Return the chart base and its reduction together, so
existential choice retains the proved property of the literal record marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfStep

open CfConv CfGiven Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open Sec7.PocketTraversal
open Sec7.StripHeights44 (IsHeightBounded44)

/-- The actual positive-time (4.4) construction has both the chart base and the
ordered zero-weight reduction. Choosing from this stronger existential retains both. -/
theorem exists_chartBase_reduction44 {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) :
    ∃ d : Wire.Night.ChartData Ω,
      Wire.Night.ChartBase κ P h (fun ω => recOf (s : ℝ≥0∞) (D ω)) η d ∧
      Wire.Night.ChartReduction κ P d := by
  let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let ρL := iwLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let ρR := iwRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let R := fun ω => recOf (s : ℝ≥0∞) (D ω)
  obtain ⟨𝓐, V, γ, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ :=
    QSched.exists_chartConst_omega44 hA href hκ hκ4 hb hcf hζ' hθh hπh hθ hDm hDreg hD hs hη
  have hsep := ae_record_strict_of44 hA href hκ hκ4 hb hcf hθh hπh hθ hDreg hD hs
  obtain ⟨kL, kR, eL, eR, _, _, heL, heR, htype⟩ :=
    CfFinish.exists_erasure_record_flowType_ae (show 0 < 16 / κ from div_pos (by norm_num) hκ)
      (x := x) (y := y) rfl rfl ρL ρR s R hsep
  refine ⟨⟨𝓐, _, _, ρL, ρR, (fun ω => recordXL s x (R ω)),
    (fun ω => recordXR s y (R ω)), V, γ⟩, ?_, ?_⟩
  · exact ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa,
      ae_of_all _ hthr, hchart, hpath⟩
  · exact ⟨kL + 1, kR + 1, eL.toEmbedding, eR.toEmbedding,
      eL.strictMono, eR.strictMono, heL, heR, htype⟩

end InteractingSLE.Sec5.CfStep
