/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawIdent
import InteractingSLE.Spec.Sec5.CrossCondGenLawFlow

/-!
# The conditional general-angle image-word law

PROVE-CROSSCOND-GEN. The analytic assembly is complete conditional on the explicit
image construction/filtration and field inputs. `ImageWordFiltrationHypothesis`
records the stochastic image facts still needed beyond the compact geometric
construction. `ImageTimeUnionHypothesis` and `ImageMeanIdentificationHypothesis`
record the optional marked kernel and surviving-boundary identification.

`imageWordFiltGenStatement` derives mean martingales from the chart law;
`imageWordFiltGenStatement_of_unionLaw` derives that chart law from the marked union
inputs. `exists_isWordEntrance_of_genLaw` gives one Brownian motion until the
minimum of the available image lifetime and the word continuation threshold.
No source-facing unrestricted cross-conditioning theorem is asserted here.
The non-hitting π/2 case is an unconditional corollary of this analytic assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito WangWu WangWu.ImgDrv MartChar Sec7.Aux117 Word49 Theta
open Sec7.Lemma71D

/-- Exact construction and filtration facts needed for a relative image word.
The announcing sequence covers positive available lifetimes; a zero-life source
branch must be handled separately when constructing the image. -/
structure ImageWordFiltrationHypothesis {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {nL nR : ℕ} (𝓐 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (c : Ω → Chart) : Prop where
  contact : IsContactWord W VL VR T
  adaptedW : StronglyAdapted (usualAugmentation 𝓐 P) W
  adaptedL : ∀ i, StronglyAdapted (usualAugmentation 𝓐 P) (VL i)
  adaptedR : ∀ j, StronglyAdapted (usualAugmentation 𝓐 P) (VR j)
  lifetime : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝓐 P t] {ω | (T ω : ℝ≥0∞) ≤ t}
  announcing : Coupling.IsAnnouncingSeq (usualAugmentation 𝓐 P) P (fun ω => (T ω : ℝ≥0∞)) σ
  conformal : ∀ ω, (c ω).IsConformal
  continuousLift : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom
  initialDomain : ∀ z, MeasurableSet[usualAugmentation 𝓐 P 0] {ω | z ∈ (c ω).dom}
  initialFwd : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
    ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)
  initialLift : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
    ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)

/-- The explicit junction-weight image means are local martingales up to swallowing
or the available lifetime. Force labels are retained through allowed mergers. -/
def ImageWordFiltGenStatement {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}
    (κ θ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω)
    (𝓐 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) : Prop :=
  ∀ z ∈ H, IsLocalMartingaleBefore (usualAugmentation 𝓐 P) P
    (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
    (coupProc κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) W VL VR z)

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {c : Ω → Chart}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The general-angle contact-word martingale law, conditional on the named image
filtration facts and fixed-time chart field law. No `Cond44` or counterflow barrier
bounds occur; the field law can instead be supplied by `chartConst_of_unionLaw`. -/
theorem imageWordFiltGenStatement
    (hImage : ImageWordFiltrationHypothesis P 𝓐 W VL VR T σ c) (hh : Measurable h)
    (hChart : IsChartCouplingCharFunConst κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      P 𝓐 W VL VR (fun ω => (T ω : ℝ≥0∞)) c (2 * π * chiC κ) (chiC κ) h) :
    ImageWordFiltGenStatement κ θ ρL ρR P 𝓐 W VL VR T :=
  isLocalMartingaleBefore_coupProc_of_chartConst hImage.contact hImage.adaptedW hImage.adaptedL
    hImage.adaptedR hImage.lifetime hImage.announcing hImage.conformal hImage.continuousLift
    hImage.initialDomain hImage.initialFwd hImage.initialLift hh hChart

/-- The complete analytic passage from the marked union kernel and its surviving
word to the generalized image martingales. The hypotheses expose the remaining
boundary/optional-time facts instead of assuming the desired martingales. -/
theorem imageWordFiltGenStatement_of_unionLaw
    (hImage : ImageWordFiltrationHypothesis P 𝓐 W VL VR T σ c) (hh : Measurable h)
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {A : ℝ≥0 → Ω → Set ℂ} {v : ℝ≥0 → Ω → ℂ → ℝ}
    (hAH : ∀ t, 𝓐 t ≤ ℋ t) (hH : ∀ t, ℋ t ≤ mΩ)
    (hAvoid : ∀ t (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[𝓐 t] {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t})
    (hMeanMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartMean κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (W · ω)
          (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) (2 * π * chiC κ) (chiC κ) φ t))
    (hVarMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartVar (W · ω) (c ω) φ t))
    (hUnion : ImageTimeUnionHypothesis P W (fun ω => (T ω : ℝ≥0∞)) c h ℋ A v)
    (hMean : ImageMeanIdentificationHypothesis P κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) W VL VR
      (fun ω => (T ω : ℝ≥0∞)) c (2 * π * chiC κ) (chiC κ) v)
    (hCov : ∀ t (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t →
        QuantumZipper.zeroGFFTestCov (H \ LocalSets.relClosureH (A t ω)) φ φ =
          chartVar (W · ω) (c ω) φ t) :
    ImageWordFiltGenStatement κ θ ρL ρR P 𝓐 W VL VR T :=
  imageWordFiltGenStatement hImage hh (chartConst_of_unionLaw hImage.contact hImage.conformal hh
    hAH hH hAvoid hMeanMeas hVarMeas hUnion hMean hCov)

/-- One Brownian motion and the integrated image-word equations through admissible
force collisions, until available image lifetime or continuation threshold. -/
theorem exists_isWordEntrance_of_genLaw (hκ : 0 < κ)
    (hImage : ImageWordFiltrationHypothesis P 𝓐 W VL VR T σ c)
    (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
    (hLaw : ImageWordFiltGenStatement κ θ ρL ρR P 𝓐 W VL VR T) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (usualAugmentation 𝓐 P) 𝓦) Bi (P.prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧ ∀ᵐ p ∂(P.prod P₀),
        IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1)
          (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (W · p.1)
          (fun i t => VL i t p.1) (fun j t => VR j t p.1) (Bi · p)
          (min (T p.1 : ℝ≥0∞) (thresholdTime (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
            (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1))) :=
  exists_isWordEntrance_junctions hκ
    (fun _ hs h0 => measurableSet_usualAugmentation_of_null hs h0 0)
    hImage.contact hImage.adaptedW hImage.adaptedL hImage.adaptedR hImage.announcing.1
    hImage.announcing.2.1 hσT hImage.announcing.2.2.2 hLaw

end Main

end InteractingSLE.Sec5.CrossCond.Gen
