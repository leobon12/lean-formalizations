/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedBaseCanon
import InteractingSLE.Spec.Wire.Thm12NightRestart

/-!
# The positive-time restart chart under the (4.4) heights, and the chart leaves in that form

Packet PROVE-QSCHED. `CfConv.exists_chartConst_omega` (the proved positive-time part of the restart chart) assumes
Aux. lemma 130's heights only to feed `CfChart.exists_chartCanon_omega` and to get the (4.4) heights at `π/2`.

* `exists_chartConst_omega44`: the same theorem under the (4.4) heights at `θ` and `π/2` (proof verbatim);
* `PositiveChartBase44Statement`, **`positiveChartBase44Statement`**: `Wire.Night.PositiveChartBaseStatement` under
  those heights, PROVED from Part A and the §4.2 reference;
* `Converted44IntegrableOn`, `Converted44ReductionOn`, `Converted44LocalOn`, `ZeroChart44Statement`: the four
  CfChart leaves of the Theorem 1.2 wiring under those heights;
* `CfGivenChart44UpStatement` (the chart form at the heights of the prefix angle) and `CfGivenChart44DownStatement`
  (its mirror image); **`cfGivenChart44Up_of_converted`** (the four leaves give the first) and
  **`cfGivenChart44Statement_of_up_down`**;
* **`counterflowGivenPrefix44Statement_of_leaves`**: the restart law at a switch from the four leaves (in the (4.4)
  form), the mirror-image chart form, Part A and the reference.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.QSched

open LawUnique CfGiven CfChart CfConv Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart Sec7.PocketTraversal Lemma47Angle
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps)

/-- **`CfConv.exists_chartConst_omega` under the (4.4) heights at `θ` and `π/2`** (its proof verbatim, through
`exists_chartCanon_omega44`). The positive-time chart conversion on the original probability space, with all driver,
mark, threshold, chart regularity and physical-clock requirements discharged. The separate
field-locality, field-integrability and reduced-word type requirements are not asserted here. -/
theorem exists_chartConst_omega44 {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
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
    exists_chartCanon_omega44 hA href hκ hκ4 hb hcf hθh hπh hθ hD hs
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
    have hπ := hπh
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


/-! ### The positive-time base and the chart leaves under the (4.4) heights -/

section Leaves

open Sec4 Restart.DomainMarkov Restart.DomainMarkov.K2 Wire.Night
open WangWu (negInv)

/-- `Wire.Night.PositiveChartBaseStatement` under the (4.4) heights at the prefix angle and at `π/2`. -/
def PositiveChartBase44Statement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (_hκ : 0 < κ) (_hκ4 : κ < 4) (_hb : IsPiecewiseConstantBoundaryData b J)
    (_hh : IsGFFWithBoundaryData P h b J),
    ∀ (_hcf : IsCenteredCounterflowDriver κ P h W' ζ') (_hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ (θ₀ : ℝ) (_hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)),
    ∀ (_hθh : IsHeightBounded44 κ b J θ₀) (_hπh : IsHeightBounded44 κ b J (π / 2)),
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (_hDm : Measurable D) (_hDreg : ∀ ω, IsRegularDriver (D ω))
    (_hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (_ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (_hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
    ∃ d, ChartBase κ P h (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) η d

/-- **The positive-time chart base under the (4.4) heights**, from Part A and the §4.2 reference
(`exists_chartConst_omega44`, as `Wire.Night.positiveChartBaseStatement`). -/
theorem positiveChartBase44Statement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : PositiveChartBase44Statement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη
  obtain ⟨𝓑, V, γ, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ :=
    exists_chartConst_omega44 hA href hκ hκ4 hb hcf hζ hθh hπh hθ hDm hDreg hD ht₀ hη
  exact ⟨⟨𝓑, _, _, _, _, _, _, V, γ⟩, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm,
    hV0, hVc, hVa, Eventually.of_forall hthr, hchart, hpath⟩

/-- `Wire.Night.ConvertedIntegrableOn` under the (4.4) heights. -/
def Converted44IntegrableOn : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (_hκ : 0 < κ) (_hκ4 : κ < 4) (_hb : IsPiecewiseConstantBoundaryData b J)
    (_hh : IsGFFWithBoundaryData P h b J),
    ∀ (_hcf : IsCenteredCounterflowDriver κ P h W' ζ') (_hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ (θ₀ : ℝ) (_hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)),
    ∀ (_hθh : IsHeightBounded44 κ b J θ₀) (_hπh : IsHeightBounded44 κ b J (π / 2)),
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (_hDm : Measurable D) (_hDreg : ∀ ω, IsRegularDriver (D ω))
    (_hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (_ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (_hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
    ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) P

/-- `Wire.Night.ConvertedReductionOn` under the (4.4) heights. -/
def Converted44ReductionOn (hBase : PositiveChartBase44Statement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)),
    ∀ (hθh : IsHeightBounded44 κ b J θ₀) (hπh : IsHeightBounded44 κ b J (π / 2)),
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
    let d := Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη)
    ChartReduction κ P d

/-- `Wire.Night.ConvertedLocalOn` under the (4.4) heights. -/
def Converted44LocalOn (hBase : PositiveChartBase44Statement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)),
    ∀ (hθh : IsHeightBounded44 κ b J θ₀) (hπh : IsHeightBounded44 κ b J (π / 2)),
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
    let d := Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη)
    HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver
      (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω))

/-- `Wire.Night.ZeroChartStatement` under the (4.4) heights. -/
def ZeroChart44Statement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → IsHeightBounded44 κ b J θ₀ → IsHeightBounded44 κ b J (π / 2) →
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (0 : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (0 : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (0 : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓐 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (0 : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf (0 : ℝ≥0∞) (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W'' (fun ω => imgField κ (recOf (0 : ℝ≥0∞) (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (0 : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- The chart form of Lemma 4.7's conditional law at the heights of the prefix angle (`CfGivenChart44Statement`,
first alternative). -/
def CfGivenChart44UpStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → IsHeightBounded44 κ b J θ₀ → IsHeightBounded44 κ b J (π / 2) →
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓐 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf (t₀ : ℝ≥0∞) (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W'' (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- The chart form of Lemma 4.7's conditional law at the mirror-image heights (`CfGivenChart44Statement`, second
alternative: the reflection `z ↦ −z̄` of the first). -/
def CfGivenChart44DownStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → IsHeightBounded44 κ (reflData b) (reflJumps J) (-θ₀) →
    IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2) →
    ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓐 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf (t₀ : ℝ≥0∞) (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W'' (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- **The chart form at the heights of the prefix angle from the four leaves** (as
`Wire.Night.cfGivenChart_of_converted`, with `Wire.Night.chart_of_base`, which uses no heights). -/
theorem cfGivenChart44Up_of_converted (hBase : PositiveChartBase44Statement.{u})
    (hInt : Converted44IntegrableOn.{u}) (hRed : Converted44ReductionOn hBase)
    (hLoc : Converted44LocalOn hBase) (hZero : ZeroChart44Statement.{u}) : CfGivenChart44UpStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ η hη
  by_cases hz : t₀ = 0
  · subst t₀
    exact hZero κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD η hη
  · have ht₀ : 0 < t₀ := lt_of_le_of_ne (zero_le : 0 ≤ t₀) (Ne.symm hz)
    exact chart_of_base (Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD
      t₀ ht₀ η hη))
      (Classical.choose_spec (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη))
      (hRed κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη)
      (hInt κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη)
      (hLoc κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hθh hπh D hDm hDreg hD t₀ ht₀ η hη)

/-- The chart form under the (4.4) heights from its two alternatives. -/
theorem cfGivenChart44Statement_of_up_down (hU : CfGivenChart44UpStatement.{u})
    (hDn : CfGivenChart44DownStatement.{u}) : CfGivenChart44Statement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ hhgt D hDm hDreg hD t₀ η hη
  rcases hhgt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hU κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ h1 h2 D hDm hDreg hD t₀ η hη
  · exact hDn κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ h1 h2 D hDm hDreg hD t₀ η hη

/-- **The restart law at a switch from the four chart leaves in the (4.4) form and the mirror-image chart form**,
with Part A and the §4.2 reference. -/
theorem counterflowGivenPrefix44Statement_of_leaves (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u})
    (hDn : CfGivenChart44DownStatement.{u}) : CounterflowGivenPrefix44Statement.{u} :=
  counterflowGivenPrefix44Statement_of_chart44
    (cfGivenChart44Statement_of_up_down (cfGivenChart44Up_of_converted _ hInt hRed hLoc hZero) hDn)

end Leaves

end InteractingSLE.Sec5.QSched
