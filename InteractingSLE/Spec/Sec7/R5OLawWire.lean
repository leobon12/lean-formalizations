/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OLawRefInf

/-!
# Clause 4 of `R5Out.R5ClausesCompOn` for the shifted pocket chart of the outer R.5 inputs

Packet PROVE-R5-OUTERLAW (ruling R88). `R5Out.TwoSeedR5CompInput(Inf)On` (PROVE-R5-OUTER) asks for
`R5Out.R5ClausesCompOn` with the base chart `c = shiftChart (pChart A C ψ) n`. These corollaries give its clause 4 for
R5-REFCHART's reference family (`M q i = R5Ref.refEvent(Inf) … (refHull W' ζ') q i`, `old q i = R5Ref.refChart(Inf) c …
i`, `F = refHull W' ζ'`) on every outer test, with the base chart's facts discharged:

* **`r5ClausesCompOn_clause4_ref_outer_shift`** (bounded outer pocket, `HOuter.IsOuterCfg`);
* **`r5ClausesCompOn_clause4_ref_outerInf_shift`** (outer pocket opening at the flow seed, `HOuter.IsOuterCfgInf`).

A consumer proving `R5ClausesCompOn … (M q) (old q) q` for this family writes `⟨h1, h2, h3, h4, h5⟩` with
`h4 := r5ClausesCompOn_clause4_ref_outer(Inf)_shift … q`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5OLaw

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketTraversal PocketAdapt PocketStop PocketStopWallsFin PocketStopMarked
  PocketWordPerQ PocketUnionPt R5Phase LocalSets Sec6 R5Enl PocketSeedOpen

section Shift

open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c₀ : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **Clause 4 of `R5Out.R5ClausesCompOn` for the shifted pocket chart of `R5Out.TwoSeedR5CompInputOn`** (bounded
outer pocket): `r5ClausesCompOn_clause4_ref_outer` with `c = shiftChart (pChart A C ψ) n` and the base chart's facts
discharged (`R5Phase.shiftChart_dom_facts`). -/
theorem r5ClausesCompOn_clause4_ref_outer_shift
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (n : Ω → ℤ) (q : ℝ≥0) :
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (centredField h'' u₀') P g →
        ∀ i, HasOldChartIncrementLawOn P
          (R5Ref.refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChart
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ i)
          (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
            (travAll R L r η ψ) q) (gB i) g := by
  have hG' : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => hG ω (hAG hω)
  have hcd := shiftChart_dom_facts (A := A) (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket
    (hG' ω hω).changePocket_subset_H) (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) n
  exact r5ClausesCompOn_clause4_ref_outer hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hcfg hζA hψ hψm hηm (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1)
    (fun ω hω => (hcd ω hω).2.2) q

/-- **Clause 4 of `R5Out.R5ClausesCompOn` for the shifted pocket chart of `R5Out.TwoSeedR5CompInputInfOn`** (outer
pocket opening at the flow seed): `r5ClausesCompOn_clause4_ref_outerInf` with `c = shiftChart (pChart A C ψ) n` and
the base chart's facts discharged (`R5Phase.shiftChart_dom_facts`). -/
theorem r5ClausesCompOn_clause4_ref_outerInf_shift
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (n : Ω → ℤ) (q : ℝ≥0) :
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (centredField h'' u₀') P g →
        ∀ i, HasOldChartIncrementLawOn P
          (R5Ref.refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChartInf
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ i)
          (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
            (travAllInf R L r η ψ) q) (gB i) g := by
  have hG' : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => hG ω (hAG hω)
  have hcd := shiftChart_dom_facts (A := A) (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket
    (hG' ω hω).changePocket_subset_H) (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) n
  exact r5ClausesCompOn_clause4_ref_outerInf hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hcfg hζA hψ hψm hηm (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1)
    (fun ω hω => (hcd ω hω).2.2) q
end Shift

end InteractingSLE.Sec7.R5OLaw
