/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvThreshold

/-!
# The given-space chart clause with record-measurable marks

Packet PROVE-CFCHART2. Apply `CfChart.exists_chartCanon_omega` and discharge the conversions
to the record chart, geometric marks, original field and infinite lifetime. The weights here
retain the two junction marks, including junctions whose weight vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart Sec7.PocketTraversal Lemma47Angle

/-- The positive-time chart conversion on the original probability space, with all driver,
mark, threshold, chart regularity and physical-clock requirements discharged. The separate
field-locality, field-integrability and reduced-word type requirements are not asserted here. -/
theorem exists_chartConst_omega {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) {η₀ : Ω → ℝ≥0 → ℂ}
    (hη₀ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η₀ ω)) :
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
    ∃ (𝓑 : Filtration ℝ≥0 mΩ) (V : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap R inferInstance ≤ 𝓑 0 ∧
      Measurable[MeasurableSpace.comap R inferInstance] XL ∧
      Measurable[MeasurableSpace.comap R inferInstance] XR ∧
      (∀ ω i, XL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ XR ω j) ∧ (∀ ω, Antitone (XL ω)) ∧ (∀ ω, Monotone (XR ω)) ∧
      (∀ ω, V 0 ω = 0) ∧ (∀ ω, Continuous fun t => V t ω) ∧ StronglyAdapted 𝓑 V ∧
      (∀ ω, FCDet.thr ρL ρR V XL XR ω = ⊤) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓑 V (geomLW V XL) (geomRW V XR)
        (fun _ => ⊤) (fun ω => cfChart (R ω)) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => V t ω) ⊤ (η ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ QuantumZipper.H ∧
            WangWu.negInv (η₀ ω (ℓ u)) = (recChart (R ω)).2.1 (WangWu.negInv (η ω u)) := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, htr, hC, _, _, hE, hEg, hEtop, hEae, hcan⟩ :=
    CfChart.exists_chartCanon_omega hA href hκ hκ4 hb hcf hleft hright hθ hD hs
  obtain ⟨𝓑, V, hR, hV0, hVc, hVa, _, hchart, hgen⟩ := exists_converted_chart hι
    isMeasurableKilledDriving_coarse hE hEg hEtop hEae hs
    (measurable_recOf hDm hDreg (s : ℝ≥0∞)) (fun _ => rfl) hDreg hC.2.1 htr hcan
  dsimp only
  refine ⟨𝓑, V, (fun ω => qTr (fun t ω => (D ω).1 t) VL VR (fun ω => (D ω).2) s E
    (ω, Cond44Ref.cfHistory W' ζ' ω)), hR, (measurable_recordXL s _).comp (comap_measurable _),
    (measurable_recordXR s _).comp (comap_measurable _), ?_, ?_, ?_, ?_, hV0, hVc, hVa, ?_, hchart, ?_⟩
  · intro ω i
    exact recordXL_nonpos (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i) s _ i
  · intro ω j
    exact recordXR_nonneg (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j) s _ j
  · intro ω
    exact antitone_recordXL (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i)
      (isOrderedForceWord_qx_angle κ θ _ _ _ _).1 s _
  · intro ω
    exact monotone_recordXR (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j)
      (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.1 s _
  · intro ω
    have hπ := isHeightBounded44_of_strip hκ hκ4 hleft hright
      (show π / 2 ∈ Icc (-(π / 2)) (π / 2) from ⟨by linarith only [Real.pi_pos], le_rfl⟩)
    have hθb := RestartGen.cfThetaBounds_of_heights hκ hκ4 hb hπ θ
    have hc : -2 < 16 / κ / 2 - 2 := by
      have hp : 0 < 16 / κ / 2 := by positivity
      linarith only [hp]
    apply thr_eq_top_of_prefix hVc
      (fun ω => antitone_recordXL (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i)
        (isOrderedForceWord_qx_angle κ θ _ _ _ _).1 s _)
      (fun ω => monotone_recordXR (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j)
        (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.1 s _) hc hc
      (prefix_iwL_angle hκ hκ4 hθ.2 hθb) (prefix_iwR_angle hκ hκ4 hθ.1 hθb)
  · filter_upwards [hgen, ae_histLine_cfHistory_eq hcf hζ' hη₀] with ω hp heq
    obtain ⟨hg, ℓ, hc, hm, h0, hl⟩ := hp
    refine ⟨hg, ℓ, hc, hm, h0, fun u hu => ?_⟩
    simpa only [heq, Real.toNNReal_coe, toCoarse, Coarse] using hl u hu

end InteractingSLE.Sec5.CfConv
