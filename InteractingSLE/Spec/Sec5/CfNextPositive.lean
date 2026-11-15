/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextStrip

/-!
# Positive-prefix chart data with reduced word type and integrability

Packet PROVE-CFCHART2. All clauses of the requested positive-time data except
physical member locality are assembled here. No separation or word-type input is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfNext

open CfConv CfChart CfGiven Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open Sec7.PocketTraversal

/-- The exact reduced chart data at a positive prefix, including integrability,
word classification and the physical clock. Physical member locality is a separate obligation. -/
theorem exists_reduced_chartConst_omega {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J) (hh : Measurable h)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, z < 0 → z ∉ J → b z + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, 0 < z → z ∉ J → sleLambda κ ≤ b z + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) {η₀ : Ω → ℝ≥0 → ℂ}
    (hη₀ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η₀ ω)) :
    ∃ (𝓐 : Filtration ℝ≥0 mΩ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
      (V : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧
      (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, V 0 ω = 0) ∧ (∀ ω, Continuous fun t => V t ω) ∧ StronglyAdapted 𝓐 V ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V (geomLW V xL) (geomRW V xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf (s : ℝ≥0∞) (D ω)))
        (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => V t ω) ⊤ (η ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H ∧
            WangWu.negInv (η₀ ω (ℓ u)) =
              (recChart (recOf (s : ℝ≥0∞) (D ω))).2.1 (WangWu.negInv (η ω u)) := by
  let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let ρL := iwLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let ρR := iwRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0)
  let R := fun ω => recOf (s : ℝ≥0∞) (D ω)
  let XL := fun ω => recordXL s x (R ω)
  let XR := fun ω => recordXR s y (R ω)
  obtain ⟨𝓐, V, η, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ :=
    CfConv.exists_chartConst_omega hA href hκ hκ4 hb hcf hζ' hleft hright hθ hDm hDreg hD hs hη₀
  have hsep := ae_record_strict_of_strip hA href hκ hκ4 hb hcf hleft hright hθ hDreg hD hs
  obtain ⟨kL, kR, eL, eR, _, _, heL, heR, htype⟩ :=
    CfFinish.exists_erasure_record_flowType_ae (show 0 < 16 / κ from div_pos (by norm_num) hκ)
      (x := x) (y := y) rfl rfl ρL ρR s R hsep
  have hchart' := CfResume.chartConst_reindex_zero eL.toEmbedding eR.toEmbedding heL heR
    (fun ω => isConformal_cfChart (R ω)) hVc hchart
  have hxL' : Measurable[MeasurableSpace.comap R inferInstance] (fun ω => XL ω ∘ eL) := by
    let : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply (eL i)).comp hxL
  have hxR' : Measurable[MeasurableSpace.comap R inferInstance] (fun ω => XR ω ∘ eR) := by
    let : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun j => (measurable_pi_apply (eR j)).comp hxR
  refine ⟨𝓐, kL + 1, kR + 1, ρL ∘ eL, ρR ∘ eR, (fun ω => XL ω ∘ eL),
    (fun ω => XR ω ∘ eR), V, η, h𝒢, hxL', hxR',
    (fun ω i => hxL0 ω (eL i)), (fun ω j => hxR0 ω (eR j)),
    (fun ω _ _ hij => hxLa ω (eL.monotone hij)),
    (fun ω _ _ hij => hxRm ω (eR.monotone hij)), hV0, hVc, hVa, ?_, htype,
    CfResume.integrable_imgField_of_chartConst hκ hh h𝒢 hV0 hVc hchart, hchart', hpath⟩
  exact ae_of_all _ fun ω =>
    (thr_reindex_zero eL.toEmbedding eR.toEmbedding ρL ρR heL heR V XL XR ω).trans (hthr ω)

end InteractingSLE.Sec5.CfNext
