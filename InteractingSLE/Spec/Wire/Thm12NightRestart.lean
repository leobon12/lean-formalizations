/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightInputs

/-!
# Restart from the positive-time converted chart and its remaining leaves

PROVE-WIRE-PARTA. CfConv proves the chart, regularity, marks, threshold and
physical clock. Only random-field integrability, reduced-word classification,
local member identities, and the zero-prefix case remain explicit.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Night
open Sec4 Sec5 Sec5.CfGiven Sec5.CfConv Sec5.CfChart Sec5.Lemma47Angle
open Restart Restart.DomainMarkov Exist Exist.Staged Exist.StagedLaw
open Restart.DomainMarkov.K2
open Sec7.PocketTraversal LawUnique WangWu

/-- A chart's data only. Its law, geometry and measurability are separate predicates. -/
structure ChartData (Ω : Type u) [mΩ : MeasurableSpace Ω] where
  filtration : Filtration ℝ≥0 mΩ
  nL : ℕ
  nR : ℕ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ
  left : Ω → Fin nL → ℝ
  right : Ω → Fin nR → ℝ
  driver : ℝ≥0 → Ω → ℝ
  trace : Ω → ℝ≥0 → ℂ

/-- Exactly the already proved part of the chart statement. -/
def ChartBase {Ω : Type u} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (R : Ω → RecData) (η : Ω → ℝ≥0 → ℂ)
    (d : ChartData Ω) : Prop :=
  MeasurableSpace.comap R inferInstance ≤ d.filtration 0 ∧
  Measurable[MeasurableSpace.comap R inferInstance] d.left ∧
  Measurable[MeasurableSpace.comap R inferInstance] d.right ∧
  (∀ ω i, d.left ω i ≤ 0) ∧ (∀ ω j, 0 ≤ d.right ω j) ∧
  (∀ ω, Antitone (d.left ω)) ∧ (∀ ω, Monotone (d.right ω)) ∧
  (∀ ω, d.driver 0 ω = 0) ∧ (∀ ω, Continuous fun t => d.driver t ω) ∧
  StronglyAdapted d.filtration d.driver ∧
  (∀ᵐ ω ∂P, FCDet.thr d.rhoL d.rhoR d.driver d.left d.right ω = ⊤) ∧
  Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) d.rhoL d.rhoR P d.filtration d.driver
    (geomLW d.driver d.left) (geomRW d.driver d.right) (fun _ => ⊤)
    (fun ω => cfChart (R ω)) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
  ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => d.driver t ω) ⊤ (d.trace ω) ∧
    ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
      ∀ v : ℝ≥0, 0 < v → negInv (d.trace ω v) ∈ H ∧
        negInv (η ω (ℓ v)) = (recChart (R ω)).2.1 (negInv (d.trace ω v))

/-- The zero-weight marks may be erased in their original order to obtain an actual flow word. -/
def ChartReduction {Ω : Type u} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω) (d : ChartData Ω) : Prop :=
  ∃ (kL kR : ℕ) (eL : Fin kL ↪ Fin d.nL) (eR : Fin kR ↪ Fin d.nR),
    StrictMono eL ∧ StrictMono eR ∧
    (∀ j, j ∉ range eL → d.rhoL j = 0) ∧ (∀ j, j ∉ range eR → d.rhoR j = 0) ∧
    ∀ᵐ ω ∂P, ∃ c : BoundaryWord,
      FCDet.IsFlowType (16 / κ) 0 c (d.left ω ∘ eL) (d.right ω ∘ eR) (d.rhoL ∘ eL) (d.rhoR ∘ eR)

/-- All positive-time instances of the already proved chart conversion. -/
def PositiveChartBaseStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ hleft : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ),
    ∀ hright : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)), ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω,
      IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
    ∃ d, ChartBase κ P h (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) η d

/-- CfConv's positive-time theorem, repackaged as data with the proved facts separate. -/
theorem positiveChartBaseStatement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : PositiveChartBaseStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη
  obtain ⟨𝓑, V, γ, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ :=
    CfConv.exists_chartConst_omega hA href hκ hκ4 hb hcf hζ hleft hright hθ hDm hDreg hD ht₀ hη
  exact ⟨⟨𝓑, _, _, _, _, _, _, V, γ⟩, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm,
    hV0, hVc, hVa, Eventually.of_forall hthr, hchart, hpath⟩

def ConvertedIntegrableOn : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ hleft : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ),
    ∀ hright : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)), ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω,
      IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => imgField κ ((fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) ω) (h ω) φ) P

def ConvertedReductionOn (hBase : PositiveChartBaseStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ hleft : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ),
    ∀ hright : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)), ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω,
      IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
let d := Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη);
    ChartReduction κ P d

def ConvertedLocalOn (hBase : PositiveChartBaseStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ hleft : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ),
    ∀ hright : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)), ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω,
      IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
let d := Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη);
    HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver (fun ω => imgField κ ((fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) ω)
      (h ω))

/-- The source restart chart at the still separate zero prefix. -/
def ZeroChartStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
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


/-- Assemble a converted chart using only the three missing positive-time facts.
The chart identity and threshold survive deletion of zero-weight marks. -/
theorem chart_of_base {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {R : Ω → RecData} {η : Ω → ℝ≥0 → ℂ}
    (d : ChartData Ω) (hbase : ChartBase κ P h R η d) (hred : ChartReduction κ P d)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => imgField κ (R ω) (h ω) φ) P)
    (hlocal : HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver
      (fun ω => imgField κ (R ω) (h ω))) :
    ∃ (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap R inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap R inferInstance] xL ∧
      Measurable[MeasurableSpace.comap R inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓐 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (R ω) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun _ => ⊤) (fun ω => cfChart (R ω)) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W'' (fun ω => imgField κ (R ω) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (R ω)).2.1 (negInv (η'' ω u))
 := by
  obtain ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ := hbase
  obtain ⟨kL, kR, eL, eR, heL, heR, hzeroL, hzeroR, hword⟩ := hred
  have hcan := (isChartCouplingCharFunConst_iff_canon (fun ω => isConformal_cfChart (R ω))
    (fun ω => (hVc ω).comp continuous_real_toNNReal)).1 hchart
  have hc := IsChartCanon.reindex_zero eL eR hzeroL hzeroR (fun ω => isConformal_cfChart (R ω))
    (fun ω => (hVc ω).comp continuous_real_toNNReal) hcan
  refine ⟨d.filtration, kL, kR, d.rhoL ∘ eL, d.rhoR ∘ eR,
    (fun ω => d.left ω ∘ eL), (fun ω => d.right ω ∘ eR), d.driver, d.trace, h𝒢, ?_, ?_,
    (fun ω i => hxL0 ω (eL i)), (fun ω j => hxR0 ω (eR j)),
    (fun ω => (hxLa ω).comp_monotone heL.monotone),
    (fun ω => (hxRm ω).comp heR.monotone), hV0, hVc, hVa, ?_, hword, hint, ?_, hlocal, hpath⟩
  · letI : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply (eL i)).comp hxL
  · letI : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun j => (measurable_pi_apply (eR j)).comp hxR
  · filter_upwards [hthr] with ω hω
    rw [thr_reindex_zero eL eR d.rhoL d.rhoR hzeroL hzeroR d.driver d.left d.right ω]
    exact hω
  · exact (isChartCouplingCharFunConst_iff_canon (fun ω => isConformal_cfChart (R ω))
      (fun ω => (hVc ω).comp continuous_real_toNNReal)).2 hc

/-- The complete restart chart from the newest residual leaves. -/
theorem cfGivenChart_of_converted (hBase : PositiveChartBaseStatement.{u})
    (hInt : ConvertedIntegrableOn.{u}) (hRed : ConvertedReductionOn hBase)
    (hLoc : ConvertedLocalOn hBase) (hZero : ZeroChartStatement.{u}) : CfGivenChartStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ η hη
  by_cases hz : t₀ = 0
  · subst t₀
    exact hZero κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD η hη
  · have ht₀ : 0 < t₀ := lt_of_le_of_ne (zero_le : 0 ≤ t₀) (Ne.symm hz)
    exact chart_of_base (Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD
      t₀ ht₀ η hη))
      (Classical.choose_spec (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη))
      (hRed κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη)
      (hInt κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη)
      (hLoc κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη)

end InteractingSLE.Wire.Night
