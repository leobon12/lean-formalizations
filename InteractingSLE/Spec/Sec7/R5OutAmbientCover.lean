import InteractingSLE.Spec.Sec7.R5OutAmbientGeometry
import InteractingSLE.Spec.Sec7.R5OutRefDecay

/-! # The source exposed-wall cover from ambient half-disc decay (R98) -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ R5Ref R5Wall
open Theorem14.SB.FinRel (freeNear)
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
  {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- Exposed-wall reference heights, conditional on the precise incident geometry. -/
theorem r5Cover_exposedOuter_of_ambientGeometry
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
    (hLW : R7OuterLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q) := by
  intro gB hgB
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hH := ae_tendsto_harmRep_refHull_ambient_halfDisc hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hGeom, hLW] with ω hHω hgeo hlw hωA hlive ξ hξ hXξ hS
  obtain ⟨i, x, ε, x', ρ, hM, hv, hcol, hpK, hland, hρ, hfree, hjump, hcur, hold⟩ :=
    hgeo hωA hlive ξ hξ hXξ hS
  obtain ⟨d, hd, hword⟩ := hlw hωA hlive ξ hξ (fun h => hXξ (Or.inr h)) hS i x ε x' hM hv hcol hpK hjump hcur hold
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


/-- The component comparison for seed-opening outer pockets. -/
theorem r5Cover_exposedOuter_of_ambientGeometryInf
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
    (hLW : R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q) := by
  intro gB hgB
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hH := ae_tendsto_harmRep_refHull_ambient_halfDisc hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hGeom, hLW] with ω hHω hgeo hlw hωA hlive ξ hξ hXξ hS
  obtain ⟨i, x, ε, x', ρ, hM, hv, hcol, hpK, hland, hρ, hfree, hjump, hcur, hold⟩ :=
    hgeo hωA hlive ξ hξ hXξ hS
  obtain ⟨d, hd, hword⟩ := hlw hωA hlive ξ hξ (fun h => hXξ (Or.inr h)) hS i x ε x' hM hv hcol hpK hjump hcur hold
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


end InteractingSLE.Sec7.R5Out
