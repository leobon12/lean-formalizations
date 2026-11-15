/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitOuterWord
import InteractingSLE.Spec.Sec7.R5OutShared

/-!
# R5-OUTER's source cover with the ambient-half-disc outer lift word (rulings R88, R98)

Packet PROVE-R5-INIT (outer round). R5-OUTER's exposed outer cover (`R5Out.r5Cover_exposedOuter_of_ambientGeometry`)
reads the outer lift word only at the collar its ambient geometry selects, together with that collar's ambient
half-disc. This file re-runs R5-OUTER's proofs with the lift word in that form (`R7OuterLiftWordAmb`, proved on
outer pockets in `R5InitOuterWord`); the proofs are R5-OUTER's, only the lift-word premise changes:
* `r5Cover_exposedOuter_of_ambientGeometryAmb`, `r5Cover_source_of_ambientLiftWordAmb` (and `…Inf…`);
* the shared data `TwoSeedOuterLiftHeightAmbInputOn(Inf)` and `twoSeedR5CompInputOn_of_liftHeightAmb` (and `…Inf…`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Init

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ R5Ref R5Wall R5Out
open Wire.Current.SideTest (rationalOriginalTime)

section Covers

variable {Ω : Type*}

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
  {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R5-OUTER's exposed-wall reference heights with the ambient-half-disc lift word**
(`R5Out.r5Cover_exposedOuter_of_ambientGeometry` with `R7OuterLiftWordAmb`: the lift word is read only at the collar
the geometry selects, with its half-disc). -/
theorem r5Cover_exposedOuter_of_ambientGeometryAmb
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ}
    {X : Ω → Set ℂ} {q : ℝ≥0}
    (hGeom : R7OuterAmbientGeometry P A R L r η ψ xL xR c W' ζ' VL VR X q)
    (hLW : R7OuterLiftWordAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q) := by
  intro gB hgB
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hH := ae_tendsto_harmRep_refHull_ambient_halfDisc hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hGeom, hLW] with ω hHω hgeo hlw hωA hlive ξ hξ hXξ hS
  obtain ⟨i, x, ε, x', ρ, hM, hv, hcol, hpK, hland, hρ, hfree, hjump, hcur, hold⟩ :=
    hgeo hωA hlive ξ hξ hXξ hS
  obtain ⟨d, hd, hword⟩ := hlw hωA hlive ξ hξ (fun h => hXξ (Or.inr h)) hS i x ε x' hM hv hcol hpK hjump hcur hold
    ρ hρ hfree
  have hSpec := refEvent_spec hcfg hψ hc hdom heq (refHull W' ζ') q i ω hM
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ)
    (hγ ω hωA) hlive (hc ω hωA)
  have hNowRaw : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω :=
    hSpec.2.2.2.1.trans hSpec.2.2.2.2
  have hFraw := eventually_nhdsWithin_of_forall (a := (ξ : ℂ)) fun y hy => hNowRaw (hNow.inv_mem_dom hy)
  have hb := hHω hωA i _ ξ x' ρ hjump hρ (hfree.trans hNowRaw) hFraw hcur
  obtain ⟨hb', hd'⟩ := tendsto_refLift_of_lift_sub (c := c) (γ := travAll R L r η ψ)
    (p := (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal) (q := q) (hc ω hωA) (hγ ω hωA) hlive
    hM.2.2.2.1 hcol.1 hcol.2.1 hcol.2.2.1
    (f := harmRep (gB i ω) (H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ' i) 0 ω)) (g := u₀') (ℓ := ambLift W' i ω) hb hd
  exact ⟨i, x, ε, _, 0, hM, hcol.1, hcol.2.1, hcol.2.2.1, hb', hd', by rw [mul_zero, add_zero, hword]⟩


/-- **`r5Cover_exposedOuter_of_ambientGeometryAmb` for outer pockets opening at the flow seed**. -/
theorem r5Cover_exposedOuter_of_ambientGeometryInfAmb
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ}
    {X : Ω → Set ℂ} {q : ℝ≥0}
    (hGeom : R7OuterAmbientGeometryInf P A R L r η ψ xL xR c W' ζ' VL VR X q)
    (hLW : R7OuterLiftWordInfAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q) := by
  intro gB hgB
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hH := ae_tendsto_harmRep_refHull_ambient_halfDisc hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hGeom, hLW] with ω hHω hgeo hlw hωA hlive ξ hξ hXξ hS
  obtain ⟨i, x, ε, x', ρ, hM, hv, hcol, hpK, hland, hρ, hfree, hjump, hcur, hold⟩ :=
    hgeo hωA hlive ξ hξ hXξ hS
  obtain ⟨d, hd, hword⟩ := hlw hωA hlive ξ hξ (fun h => hXξ (Or.inr h)) hS i x ε x' hM hv hcol hpK hjump hcur hold
    ρ hρ hfree
  have hSpec := refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q i ω hM
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ)
    (hγ ω hωA) hlive (hc ω hωA)
  have hNowRaw : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω :=
    hSpec.2.2.2.1.trans hSpec.2.2.2.2
  have hFraw := eventually_nhdsWithin_of_forall (a := (ξ : ℂ)) fun y hy => hNowRaw (hNow.inv_mem_dom hy)
  have hb := hHω hωA i _ ξ x' ρ hjump hρ (hfree.trans hNowRaw) hFraw hcur
  obtain ⟨hb', hd'⟩ := tendsto_refLift_of_lift_sub (c := c) (γ := travAllInf R L r η ψ)
    (p := (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal) (q := q) (hc ω hωA) (hγ ω hωA) hlive
    hM.2.2.2.1 hcol.1 hcol.2.1 hcol.2.2.1
    (f := harmRep (gB i ω) (H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ' i) 0 ω)) (g := u₀') (ℓ := ambLift W' i ω) hb hd
  exact ⟨i, x, ε, _, 0, hM, hcol.1, hcol.2.1, hcol.2.2.1, hb', hd', by rw [mul_zero, add_zero, hword]⟩


/-- **R5-OUTER's full source cover with the ambient-half-disc outer lift word**
(`R5Out.r5Cover_source_of_ambientLiftWord` with `R7OuterLiftWordAmb`). -/
theorem r5Cover_source_of_ambientLiftWordAmb
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hLW : R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuterExc : ∀ ω ∈ A, outerExc R L r η ψ q ω ⊆ X ω)
    (hOuterWord : R7OuterLiftWordAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (fun _ _ => True) := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hHull := r5Cover_ref_hull_of_liftWord hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hζA hLW
  have hWall := r5Cover_wall (F := refHull W' ζ') (δ := δ) (X := fun ω => refExc R L r η ψ q ω ∪ X ω)
    (M := refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (old := refChart c R L r η ψ)
    hγ hc hcExt hxL hxR (refHull_eqv_zero W' ζ')
    (fun ω hω => refChart_eqv_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω))
    (fun ω hω hq => mem_refEvent_eqv_zero hω hq (hcfg ω hω) (hψ ω hω))
    (fun ω => (hX₀ ω).trans subset_union_right) hInit
  have hGeom := r7OuterAmbientGeometry hC.1.2.2.2.2 hcfg hψ hc hdom heq hζA
    (fun ω _ => hxL ω 0) (fun ω _ => hxR ω 0) hOuterExc
  have hOuter := r5Cover_exposedOuter_of_ambientGeometryAmb hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc
    hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hGeom hOuterWord
  exact R5Cover.of_three hHull hWall hOuter


/-- **`r5Cover_source_of_ambientLiftWordAmb` for outer pockets opening at the flow seed**. -/
theorem r5Cover_source_of_ambientLiftWordInfAmb
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hLW : R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuterExc : ∀ ω ∈ A, outerExcInf R L r η ψ q ω ⊆ X ω)
    (hOuterWord : R7OuterLiftWordInfAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (fun _ _ => True) := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hHull := r5Cover_ref_hull_of_liftWordInf hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hζA hLW
  have hWall := r5Cover_wall (F := refHull W' ζ') (δ := δ) (X := fun ω => refExcInf R L r η ψ q ω ∪ X ω)
    (M := refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (old := refChartInf c R L r η ψ)
    hγ hc hcExt hxL hxR (refHull_eqv_zero W' ζ')
    (fun ω hω => refChartInf_eqv_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω))
    (fun ω hω hq => mem_refEventInf_eqv_zero hω hq (hcfg ω hω) (hψ ω hω))
    (fun ω => (hX₀ ω).trans subset_union_right) hInit
  have hGeom := r7OuterAmbientGeometryInf hC.1.2.2.2.2 hcfg hψ hc hdom heq hζA
    (fun ω _ => hxL ω 0) (fun ω _ => hxR ω 0) hOuterExc
  have hOuter := r5Cover_exposedOuter_of_ambientGeometryInfAmb hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc
    hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hGeom hOuterWord
  exact R5Cover.of_three hHull hWall hOuter


end Covers

section Data

variable {Ω : Type*}

/-- **`R5Out.TwoSeedOuterLiftHeightInputOn` with the ambient-half-disc outer lift word** (`R7OuterLiftWordAmb`). -/
def TwoSeedOuterLiftHeightAmbInputOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
    ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ),
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω);
      ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧
        (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
          ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
        R7AmbientLiftWord κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7OuterLiftWordAmb κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
          (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (X q) ∧
        (∀ ω ∈ A, outerExc R L r η ψ q ω ⊆ X q ω)

/-- **`R5Out.TwoSeedOuterLiftHeightInputOn` with the ambient-half-disc outer lift word** (`R7OuterLiftWordAmb`). -/
def TwoSeedOuterLiftHeightAmbInputInfOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
    ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ),
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω);
      ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧
        (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
          ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
        R7AmbientLiftWordInf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7OuterLiftWordInfAmb κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
          (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (X q) ∧
        (∀ ω ∈ A, outerExcInf R L r η ψ q ω ⊆ X q ω)

end Data

section Comp

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R5Phase OuterCont R5Enl R5Ref

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R5Enl.TwoSeedR5CompInputOn` from the ambient-half-disc shared data** (`R5Out.twoSeedR5CompInputOn_of_liftHeight`
with `TwoSeedOuterLiftHeightAmbInputOn`). -/
theorem twoSeedR5CompInputOn_of_liftHeightAmb [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hin : TwoSeedOuterLiftHeightAmbInputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL ρR W' ζ' VL VR) :
    TwoSeedR5CompInputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a₀, δ, X, hData⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω => by
    have hc := hcfg ω (hAG hω)
    have hp := hc.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    exact Or.inl ⟨cfPt (openPt (R ω) (L ω) r), cfPt (closePt (R ω) (L ω) r), hp.isBounded,
      hc.conf.cfPt_openPt_notMem, hψ ω hω⟩
  obtain ⟨hcA, hcExt, hcInf⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hcd := shiftChart_dom_facts hCo hCH hψc n

  refine ⟨n, hn, a₀, δ, (fun q ω => refExc R L r η ψ q ω ∪ X q ω),
    (fun _ i ω => (refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      R L r η ψ i ω).2.2),
    (fun q => refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q),
    (fun _ => refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ),
    fun q => ?_⟩
  obtain ⟨hXf, hLat, hLW, hOW, hInit, hExc⟩ := hData q
  have hCover := r5Cover_source_of_ambientLiftWordAmb hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) hψ
    (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
    (fun ω hω => hζG ω (hAG hω)) hcExt (fun _ _ => rfl) (fun _ _ => rfl)
    hLW hInit (fun _ => Subset.rfl) hExc hOW
  refine ⟨(fun ω => (refExc_finite R L r η ψ q ω).union (hXf ω)), hLat,
    refEvent_spec (fun ω hω => hcfg ω (hAG hω)) hψ
      (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
      (refHull W' ζ') q,
    R5OLaw.r5ClausesCompOn_clause4_ref_outer_shift hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
      hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω))
      (fun ω hω => hζG ω (hAG hω)) hψ hψm hηm n q,
    (R5Wall.r5Cover_true_iff).1 hCover⟩

/-- **`twoSeedR5CompInputOn_of_liftHeightAmb` for outer pockets opening at the flow seed**. -/
theorem twoSeedR5CompInputInfOn_of_liftHeightAmb [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hin : TwoSeedOuterLiftHeightAmbInputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL ρR W' ζ' VL VR) :
    TwoSeedR5CompInputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ') := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a₀, δ, X, hData⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω =>
    Or.inr ⟨cfPt (closePt (R ω) (L ω) r), hψ ω hω⟩
  obtain ⟨hcA, hcExt, hcInf⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hcd := shiftChart_dom_facts hCo hCH hψc n

  refine ⟨n, hn, a₀, δ, (fun q ω => refExcInf R L r η ψ q ω ∪ X q ω),
    (fun _ i ω => (refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      R L r η ψ i ω).2.2),
    (fun q => refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q),
    (fun _ => refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ),
    fun q => ?_⟩
  obtain ⟨hXf, hLat, hLW, hOW, hInit, hExc⟩ := hData q
  have hCover := r5Cover_source_of_ambientLiftWordInfAmb hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) hψ
    (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
    (fun ω hω => hζG ω (hAG hω)) hcExt (fun _ _ => rfl) (fun _ _ => rfl)
    hLW hInit (fun _ => Subset.rfl) hExc hOW
  refine ⟨(fun ω => (refExcInf_finite R L r η ψ q ω).union (hXf ω)), hLat,
    refEventInf_spec (fun ω hω => hcfg ω (hAG hω)) hψ
      (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
      (refHull W' ζ') q,
    R5OLaw.r5ClausesCompOn_clause4_ref_outerInf_shift hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
      hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω))
      (fun ω hω => hζG ω (hAG hω)) hψ hψm hηm n q,
    (R5Wall.r5Cover_true_iff).1 hCover⟩

end Comp

end InteractingSLE.Sec7.R5Init
