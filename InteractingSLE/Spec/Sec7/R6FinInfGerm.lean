/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinInfPocket
import InteractingSLE.Spec.Sec7.R6FinWalls
import InteractingSLE.Spec.Sec7.R6FinCert

/-!
# R.6's locality and germ comparisons for pockets opening at the flow seed

PROVE-R6-CERT2. The `…Inf` counterparts of PROVE-R6-CERT's `isLocalSet_activeCompl_outer`, `_cf` and
`ae_r6Germ_outer_cf`, from the stop pockets of `R6FinInfPocket`:

* `isLocalSet_of_stopPocket_two`: a stop pocket of two walls' histories is a local set (the single-pocket
  walls–hull law at its marked stop);
* `isLocalSet_activeCompl_outerInf`, `isLocalSet_activeCompl_cfInf`: the active complements of the two pocket kinds
  opening at the flow seed are local, with unbounded lower-union components;
* `ae_r6Germ_four`: the germ comparison for any two stop pockets of the four walls' histories;
* `ae_r6Germ_outerInf_cf`, `ae_r6Germ_outerInf_cfInf`: an outer pocket opening at the flow seed with a nested
  bounded, resp. seed-opening, contained pocket.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fin

open R6Cert PocketStopWallsFin PocketStopWalls PocketStop PocketCoupling PocketUnionPt PocketStopSide LocalSets
  WholeField PocketTraversal Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketStopField
  PocketWordPerQ PocketStopMarked PocketSeedOpen

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A stop pocket of two walls' histories is a local set** of the centred counterflow field. -/
theorem isLocalSet_of_stopPocket_two {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hWR : IsWallData P (centredField h u₀) R) (hWL : IsWallData P (centredField h u₀) L)
    {T : Ω → ℝ≥0∞} {E : Ω → Set ℂ}
    (hP : IsStopPocket (drivingFiltration P hX) (fullHist ![R, L]) (regHull W' ζ')
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) ℳ T E)
    (hreg : ∀ᵐ ω ∂P, E ω ⊆ H ∧ IsOpen (H \ E ω)) :
    Measurable[mΩ, hittingSigma] E ∧ IsLocalSet E (centredField h'' u₀') P := by
  obtain ⟨hc2, h02, hm2, hdet2, hloc2⟩ := two_walls_data hWR.cont hWL.cont hWR.zero hWL.zero hWR.meas hWL.meas
    hWR.det hWL.det hWR.loc hWL.loc
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe] at hP
  have hℳ : ℳ ≤ mΩ := fun M hM =>
    (sup_le (measurable_fullHist hm2).comap_le (iSup_le fun t => (drivingFiltration P hX).le t)) M (hP.marks_le M hM)
  exact isLocalSet_of_isStopPocket hC hκ' hu₀' hX hζ (measurable_fullHist hm2) (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    hP hℳ hreg

/-! ### Locality of the seed-opening active complements -/
section Loc

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ}
  {G A : Set Ω}

/-- **The outer pocket opening at the flow seed: its active complement at relative time `q` is local**, with
unbounded lower-union components. -/
theorem isLocalSet_activeCompl_outerInf (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hWR : IsWallData P (centredField h u₀) R) (hWL : IsWallData P (centredField h u₀) L)
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[wallsSigma P R L] n) (q : ℝ≥0) :
    Measurable[mΩ, hittingSigma] (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) ∧
      IsLocalSet (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (centredField h'' u₀') P ∧
      ∀ ω, ∀ z ∈ lowerUnion (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q ω),
        ¬ IsBounded (connectedComponentIn (lowerUnion (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q ω)) z) := by
  have hRm' := measurable_right_wallsSigma (P := P) hWR.cont hWL.cont
  have hLm' := measurable_left_wallsSigma (P := P) hWR.cont hWL.cont
  have h𝓦m : wallsSigma P R L ≤ mΩ := wallsSigma_le hWR.meas hWL.meas
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP := isStopPocket_outerInf (X := fullHist ![R, L]) h𝓦m (wallsSigma_le_drivingFiltration hX R L) hWad hRm'
    hLm' hGm hcfg hA hAG hζA hψ hψm hηm hn q
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hpch := isPocketChartOn_pChart (mΩ := wallsSigma P R L) hA hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hcc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hcOn.1 ω hω).1
  obtain ⟨hm, hloc⟩ := isLocalSet_of_stopPocket_two hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hWR hWL hP
    (Eventually.of_forall (activeCompl_regular_of_driven hγ hcc))
  exact ⟨hm, hloc, fun ω => not_isBounded_lowerUnion_activeCompl hγ hcc ω⟩

/-- **A contained pocket opening at the flow seed: its active complement at relative time `q` is local**, with
unbounded lower-union components. -/
theorem isLocalSet_activeCompl_cfInf (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hWR : IsWallData P (centredField h u₀) R) (hWL : IsWallData P (centredField h u₀) L)
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[wallsSigma P R L] n) (q : ℝ≥0) :
    Measurable[mΩ, hittingSigma] (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) ∧
      IsLocalSet (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (centredField h'' u₀') P ∧
      ∀ ω, ∀ z ∈ lowerUnion (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q ω),
        ¬ IsBounded (connectedComponentIn (lowerUnion (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q ω)) z) := by
  have hRm' := measurable_right_wallsSigma (P := P) hWR.cont hWL.cont
  have hLm' := measurable_left_wallsSigma (P := P) hWR.cont hWL.cont
  have h𝓦m : wallsSigma P R L ≤ mΩ := wallsSigma_le hWR.meas hWL.meas
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP := isStopPocket_cfInf (X := fullHist ![R, L]) h𝓦m (wallsSigma_le_drivingFiltration hX R L) hWad hRm'
    hLm' hGm hcfg hA hAG hζA hψ hψm hηm hn q
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hpch := isPocketChartOn_pChart (mΩ := wallsSigma P R L) hA hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hcc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hcOn.1 ω hω).1
  obtain ⟨hm, hloc⟩ := isLocalSet_of_stopPocket_two hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hWR hWL hP
    (Eventually.of_forall (activeCompl_regular_of_driven hγ hcc))
  exact ⟨hm, hloc, fun ω => not_isBounded_lowerUnion_activeCompl hγ hcc ω⟩

end Loc

/-! ### Germ comparisons -/

section Germ

/-- **R.6's germ comparison for two stop pockets of the four walls' histories** (the tail of
`R6Cert.ae_r6Germ_outer_cf`, for any two stop pockets read with the joined information of `![R, L, R', L']`). -/
theorem ae_r6Germ_four {ℳ₁ ℳ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L R' L' : Ω → ℝ≥0 → ℂ} (hWR : IsWallData P (centredField h u₀) R) (hWL : IsWallData P (centredField h u₀) L)
    (hWR' : IsWallData P (centredField h u₀) R') (hWL' : IsWallData P (centredField h u₀) L')
    {T₁ T₂ : Ω → ℝ≥0∞} {EC EU : Ω → Set ℂ}
    (hP₁ : IsStopPocket (drivingFiltration P hX) (fullHist ![R, L, R', L']) (regHull W' ζ')
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) ℳ₁ T₁ EC)
    (hP₂ : IsStopPocket (drivingFiltration P hX) (fullHist ![R, L, R', L']) (regHull W' ζ')
      (fun ω => negInv '' (range (R' ω) ∪ range (L' ω))) ℳ₂ T₂ EU)
    (hCm : Measurable[mΩ, hittingSigma] EC) (hCloc : IsLocalSet EC (centredField h'' u₀') P)
    (hCunb : ∀ ω, ∀ z ∈ lowerUnion (EC ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EC ω)) z))
    (hUm : Measurable[mΩ, hittingSigma] EU) (hUloc : IsLocalSet EU (centredField h'' u₀') P)
    (hUunb : ∀ ω, ∀ z ∈ lowerUnion (EU ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EU ω)) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens} (hgC : IsLocalSetMean EC (centredField h'' u₀') P gC)
    (hgU : IsLocalSetMean EU (centredField h'' u₀') P gU) :
    ∀ᵐ ω ∂P, ∀ v vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ EC ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω → gC ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vI (H \ EU ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω → gU ω φ = ∫ z, vI z * φ z) →
      GermAt (EC ω) (EU ω) v vI := by
  have hc4 : ∀ i ω, Continuous ((![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω) := by
    intro i ω; fin_cases i
    exacts [hWR.cont ω, hWL.cont ω, hWR'.cont ω, hWL'.cont ω]
  have h04 : ∀ i ω, (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 4 → ℂ) i := by
    intro i ω; fin_cases i
    exacts [hWR.zero ω, hWL.zero ω, hWR'.zero ω, hWL'.zero ω]
  have hm4 : ∀ i t, Measurable fun ω => (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω t := by
    intro i t; fin_cases i
    exacts [hWR.meas t, hWL.meas t, hWR'.meas t, hWL'.meas t]
  have hdet4 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) := by
    intro i t; fin_cases i
    exacts [hWR.det t, hWL.det t, hWR'.det t, hWL'.det t]
  have hloc4 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i)
      (centredField h u₀) P := by
    intro i; fin_cases i
    exacts [hWR.loc, hWL.loc, hWR'.loc, hWL'.loc]
  have e4 := fun ω => congrFun (walls_union_eq_four R L R' L') ω
  have hΓ : Measurable[mΩ, hittingSigma] (fun ω => negInv '' (range (R ω) ∪ range (L ω)) ∪
      negInv '' (range (R' ω) ∪ range (L' ω))) := by
    rw [walls_union_eq_four]; exact measurable_negInv_walls hc4 hm4
  refine ae_r6Germ_of_stopPockets hC hκ' hu₀' hX hζ (measurable_fullHist hm4) hΓ ?_ hP₁ hP₂ hCm hUm hCloc hUloc
    (Eventually.of_forall hCunb) (Eventually.of_forall hUunb) hgC hgU
  intro U G hUH hG hd B hB
  have hW := walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc4 h04 hm4 hdet4 hloc4 U G hUH hG hd B hB
  simp only [← e4] at hW
  exact hW

end Germ

end InteractingSLE.Sec7.R6Fin
