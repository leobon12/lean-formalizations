import InteractingSLE.Spec.Sec7.R5OutSourceCover
import InteractingSLE.Spec.Sec7.R5OutAmbientCover

/-! # The full source outer cover with only the shared lift and initial-height data (R98) -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ R5Ref R5Wall
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
  {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- Full source cover from the shared lift words and initial wall heights. -/
theorem r5Cover_source_of_ambientLiftWord
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
    (hOuterWord : R7OuterLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
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
  have hOuter := r5Cover_exposedOuter_of_ambientGeometry hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc
    hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hGeom hOuterWord
  exact R5Cover.of_three hHull hWall hOuter


/-- The same full source cover for a seed-opening outer pocket. -/
theorem r5Cover_source_of_ambientLiftWordInf
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
    (hOuterWord : R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
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
  have hOuter := r5Cover_exposedOuter_of_ambientGeometryInf hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc
    hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hψ hc hdom heq hGeom hOuterWord
  exact R5Cover.of_three hHull hWall hOuter


end InteractingSLE.Sec7.R5Out
