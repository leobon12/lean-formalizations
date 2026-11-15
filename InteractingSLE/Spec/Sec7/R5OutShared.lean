import InteractingSLE.Spec.Sec7.R5OutSharedData
import InteractingSLE.Spec.Sec7.R5OutWire

/-! # Source outer R.5 from the permitted shared lift and height data -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R5Out

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R5Phase OuterCont R5Enl R5Ref

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem twoSeedR5CompInputOn_of_liftHeight [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedOuterLiftHeightInputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL ρR W' ζ' VL VR) :
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
    (fun _ i ω => (refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ i ω).2.2),
    (fun q => refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q),
    (fun _ => refChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ), fun q => ?_⟩
  obtain ⟨hXf, hLat, hLW, hOW, hInit, hExc⟩ := hData q
  have hCover := r5Cover_source_of_ambientLiftWord hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
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

theorem twoSeedR5CompInputInfOn_of_liftHeight [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedOuterLiftHeightInputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' ρL ρR W' ζ' VL VR) :
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
    (fun _ i ω => (refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ i ω).2.2),
    (fun q => refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q),
    (fun _ => refChartInf (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) R L r η ψ), fun q => ?_⟩
  obtain ⟨hXf, hLat, hLW, hOW, hInit, hExc⟩ := hData q
  have hCover := r5Cover_source_of_ambientLiftWordInf hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0
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

end InteractingSLE.Sec7.R5Out
