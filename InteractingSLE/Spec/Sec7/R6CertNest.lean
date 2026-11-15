/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertWalls

/-!
# R.6's field-level germ comparison for the R.7 outer pocket and a nested contained pocket

PROVE-R6-CERT. Supplement pp. 475–477 (R.5's "nested marked local-set law to the enlarged stop", R.6's "the all-stop
collar argument identifies each local germ with that same ambient germ in its own chart"). The outer pocket `C` of
the walls `(R, L)` (a bounded mixed or outer pocket, `HOuter.IsOuterCfg`) is read at its deterministic relative time
`q`; a nested contained pocket `U` of the walls `(R', L')` (`IsCfPocketConfig`, Aux. 131's pocket, e.g. R.6's
`β_R`–`γ` pocket in the mixed case) is read at **its own deterministic relative time `q'`**. Both active complements
are local (`isLocalSet_activeCompl_outer`, `isLocalSet_activeCompl_cf`), and their local-set means have the physical
germ comparison of R.6 at every locally shared boundary point (`ae_r6Germ_outer_cf`): the joint walls–hull law of the
four walls at `T_C⁰(q) ∨ T_U⁰(q')` (`R6Cert.ae_r6Germ_of_stopPockets`). In particular the inner R.5 word is needed
only at deterministic inner relative times, where it is the landed input (`R6Rel.inner_side_of_word`).

The walls are versions (continuous at every sample) that are determined by and entrance-history local for the
centred flow-chart field — the hypotheses of `PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open PocketStopWallsFin PocketStopWalls PocketStop PocketCoupling PocketUnionPt PocketStopSide LocalSets WholeField
  PocketTraversal Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketStopField
  PocketWordPerQ PocketStopMarked

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The two-wall data packaged as a `Fin 2` family. -/
theorem two_walls_data [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {u₀ : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hR0 : ∀ ω, R ω 0 = 0) (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P) :
    (∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω)) ∧
      (∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i) ∧
      (∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) ∧
      (∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω)) ∧
      ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
  ⟨Fin.forall_fin_two.2 ⟨hRc, hLc⟩, Fin.forall_fin_two.2 ⟨hR0, hL0⟩, Fin.forall_fin_two.2 ⟨hRm, hLm⟩,
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩, Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩⟩

/-- **The outer pocket's active complement at relative time `q` is local**, with unbounded lower-union components:
the single-pocket walls–hull law at `T⁰(q)` with the outer walls' histories. -/
theorem isLocalSet_activeCompl_outer [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[wallsSigma P R L] n) (q : ℝ≥0) :
    let E := activeCompl A (travAll R L r η ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q
    Measurable[mΩ, hittingSigma] E ∧ IsLocalSet E (centredField h'' u₀') P ∧
      ∀ ω, ∀ z ∈ lowerUnion (E ω), ¬ IsBounded (connectedComponentIn (lowerUnion (E ω)) z) := by
  intro E
  obtain ⟨hc2, h02, hm2, hdet2, hloc2⟩ := two_walls_data hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦m : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP := isStopPocket_outer (X := fullHist ![R, L]) h𝓦m (wallsSigma_le_drivingFiltration hX R L) hWad hRm' hLm'
    hGm hcfg hA hAG hζA hψ hψm hηm hn q
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe] at hP
  have hℳ : locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤ mΩ := fun M hM =>
    (sup_le (measurable_fullHist hm2).comap_le (iSup_le fun t => (drivingFiltration P hX).le t)) M (hP.marks_le M hM)
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hpch := isPocketChartOn_pChart (mΩ := wallsSigma P R L) hA hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hcc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hcOn.1 ω hω).1
  obtain ⟨hm, hloc⟩ := isLocalSet_of_isStopPocket hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    hP hℳ (Eventually.of_forall (activeCompl_regular_of_driven hγ hcc))
  exact ⟨hm, hloc, fun ω => not_isBounded_lowerUnion_activeCompl hγ hcc ω⟩

/-- **A contained pocket's active complement at relative time `q` is local**, with unbounded lower-union components:
the single-pocket walls–hull law at `T⁰(q)` with the pocket's walls' histories. -/
theorem isLocalSet_activeCompl_cf [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[wallsSigma P R L] n) (q : ℝ≥0) :
    let E := activeCompl A (travAll R L r η ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q
    Measurable[mΩ, hittingSigma] E ∧ IsLocalSet E (centredField h'' u₀') P ∧
      ∀ ω, ∀ z ∈ lowerUnion (E ω), ¬ IsBounded (connectedComponentIn (lowerUnion (E ω)) z) := by
  intro E
  obtain ⟨hc2, h02, hm2, hdet2, hloc2⟩ := two_walls_data hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦m : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP := isStopPocket_cf (X := fullHist ![R, L]) h𝓦m (wallsSigma_le_drivingFiltration hX R L) hWad hRm' hLm'
    hGm hcfg hA hAG hζA hψ hψm hηm hn q
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe] at hP
  have hℳ : locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤ mΩ := fun M hM =>
    (sup_le (measurable_fullHist hm2).comap_le (iSup_le fun t => (drivingFiltration P hX).le t)) M (hP.marks_le M hM)
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hpch := isPocketChartOn_pChart (mΩ := wallsSigma P R L) hA hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hcc : ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal :=
    fun ω hω => (hcOn.1 ω hω).1
  obtain ⟨hm, hloc⟩ := isLocalSet_of_isStopPocket hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    hP hℳ (Eventually.of_forall (activeCompl_regular_of_driven hγ hcc))
  exact ⟨hm, hloc, fun ω => not_isBounded_lowerUnion_activeCompl hγ hcc ω⟩

end InteractingSLE.Sec7.R6Cert
