/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutAmbDecay
import InteractingSLE.Spec.Sec7.R5EnlWalls
import InteractingSLE.Spec.Sec7.R5PhaseRef

/-! # R98's ambient half-disc comparison for the original raw pocket references -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C R5Phase PocketUnionPt R5Same

variable {Ω : Type*}

variable {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- The source raw reference height from an empty ambient-chart half-disc. -/
theorem ae_tendsto_harmRep_ref_ambient_halfDisc
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
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
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (s : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0)
      (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ (F : ℂ → ℂ) (ξ : ℝ) (x d : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) →
      0 < d →
      QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) s '' (H ∩ ball (x : ℂ) d) ⊆
        H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω →
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), F y ∈ H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) s (F y)).im) (𝓝[H] (ξ : ℂ))
        (𝓝 (forceBoundaryData κ' ρL ρR (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) x)) := by
  have hA' : MeasurableSet[refInfo P hX R L s] A := wallsSigma_le_refInfo hX R L s _ hA
  have hPre := locPrefixSigma_zero_of_driven hA' hγ
  have hRef := pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hγ s
  obtain ⟨E, hEm, hEloc, hEeq⟩ := hRef
  have hLive := measurableSet_live (𝓦 := refInfo P hX R L s) A γ 0
  rw [hPre] at hEloc hLive
  have hRawLocal := isHistoryAvoidanceLocal_liveExt hLive hEloc hEeq
  have hRawMeas := R5Enl.measurable_refSet_refInfo hC hκ' hX hζ hRc hLc hGm hG hA hAG hγ s
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    PocketJordan.isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hRawReg := liveExt_regular (γ := γ) (q := 0) hCo (fun ω _ => isOpen_H_diff_regHull W' ζ' s ω)
  have hSub : ∀ ω, regHull W' ζ' s ω ∩ H ⊆
      liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω := by
    intro ω z hz
    unfold liveExt
    split_ifs
    · exact ⟨hz.2, Or.inr hz.1⟩
    · exact hz.2
  have hCmp := ae_tendsto_rawMean_sub_ambient_of_marked hC hκ' hu₀' hX hζ s
    (refInfo_le hX hRm hLm s) le_sup_right hRawMeas hRawReg hRawLocal hSub hg
  filter_upwards [hCmp, hg.2.1, ae_regHull_eq hC hζ, hC.1.2.2.2.2, hζ]
    with ω hCmp hRep hHull hp hLife hω F ξ x d hx hd hDisc hF hLim
  have hWc : Continuous fun t : ℝ≥0 => W' t ω := by
    have he : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ' ω} = univ := by simp [hLife]
    exact continuousOn_univ.1 (he ▸ hp.2.2.2.1)
  have hWr := Chart.continuous_rpath_of_continuous hWc
  have hGE := isBoundedHarmonicExtension_wordExt κ' ρL ρR VL VR W' s ω
  obtain ⟨hv, hPair⟩ := harmRep_spec hRep
  have h0 := hCmp (wordExt κ' ρL ρR VL VR W' s ω) hGE _ hv hPair ξ x d F hd hDisc hF hLim
  have hWithin : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y))
      (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hLim, hF.mono fun y hy => ?_⟩
    have hyK : F y ∈ H \ regHull W' ζ' s ω :=
      ⟨hy.1, fun hyK => hy.2 (hSub ω ⟨hyK, hy.1⟩)⟩
    rw [hHull s] at hyK
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWr s.coe_nonneg hyK
  have h1 := (hGE.2.2 x hx).comp hWithin
  have h2 := h0.add h1
  rw [zero_add] at h2
  exact h2.congr fun y => by dsimp only [Function.comp_apply]; ring

/-- The ambient half-disc comparison simultaneously at all source rational references. -/
theorem ae_tendsto_harmRep_refHull_ambient_halfDisc
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
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
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {gB : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
      (centredField h'' u₀') P (gB i)) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ i : ℕ, ∀ (F : ℂ → ℂ) (ξ : ℝ) (x d : ℝ),
      x ∉ forceJumpSet (fun j => VL j (Wire.Current.SideTest.rationalOriginalTime i) ω - W' (Wire.Current.SideTest.rationalOriginalTime i) ω) (fun j => VR j (Wire.Current.SideTest.rationalOriginalTime i) ω - W' (Wire.Current.SideTest.rationalOriginalTime i) ω) →
      0 < d →
      QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) (Wire.Current.SideTest.rationalOriginalTime i) '' (H ∩ ball (x : ℂ) d) ⊆
        H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω →
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), F y ∈ H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (Wire.Current.SideTest.rationalOriginalTime i) (F y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (Wire.Current.SideTest.rationalOriginalTime i) (F y)).im) (𝓝[H] (ξ : ℂ))
        (𝓝 (forceBoundaryData κ' ρL ρR (fun j => VL j (Wire.Current.SideTest.rationalOriginalTime i) ω - W' (Wire.Current.SideTest.rationalOriginalTime i) ω) (fun j => VR j (Wire.Current.SideTest.rationalOriginalTime i) ω - W' (Wire.Current.SideTest.rationalOriginalTime i) ω) x)) := by
  have hAll := ae_all_iff.2 fun i => ae_tendsto_harmRep_ref_ambient_halfDisc hT' hTr hu₀ hh hC hκ'
    hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hγ
    (Wire.Current.SideTest.rationalOriginalTime i) (hgB i)
  filter_upwards [hAll] with ω hω hAω i
  exact hω i hAω

end InteractingSLE.Sec7.R5Out
