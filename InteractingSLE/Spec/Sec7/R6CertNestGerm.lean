/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertNest

/-!
# R.6's germ comparison: the outer pocket at `q`, a nested contained pocket at `q'`

PROVE-R6-CERT. The field-level item 5 of the R.6 certificate (`R6Rel.R6Cert`) for the actual R.7 sets: the active
complement `pocketSet A R L r η ψ n q` of the outer pocket of `(R, L)` at its relative time `q` (the set of
`R6Rel.TwoSeedNestCertInput`) and the active complement of a nested contained pocket of `(R', L')` at its own
relative time `q'`. Almost surely, for all harmonic representatives of their local-set means, all nested conformal
charts on the two complements, collars and landings, local agreement of the two sets at the landing point gives
`R6Rel.R6Germ` (`ae_r6Germ_outer_cf`). The proof is the joint walls–hull law of the four walls at
`T_C⁰(q) ∨ T_U⁰(q')` (`R6Cert.ae_r6Germ_of_stopPockets`); no time is shared between the two pockets.

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

/-- **The active complement of the change pocket of `(R, L)` at relative time `q`**, in the shifted canonical chart
(the set whose local-set mean carries R.5's word in `R6Rel.TwoSeedNestCertInput`). -/
def pocketSet (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (n : Ω → ℤ)
    (q : ℝ≥0) : Ω → Set ℂ :=
  activeCompl A (travAll R L r η ψ) (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q

/-- **R.6's germ comparison between the outer pocket at `q` and a nested contained pocket at `q'`** (item 5 of
`R6Rel.R6Cert`): the frozen counterflow coupling of the centred field, the outer walls `(R, L)` with a bounded mixed
or outer pocket on `G`, the nested walls `(R', L')` with a bounded contained pocket on `G'` (all four walls versions
determined by and entrance-history local for the centred flow-chart field), tests `A ⊆ G`, `A' ⊆ G'` with Jordan
coordinates and branches, and local-set means `gC`, `gU` of the two active complements. -/
theorem ae_r6Germ_outer_cf [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L R' L' : Ω → ℝ≥0 → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    (hR'c : ∀ ω, Continuous (R' ω)) (hL'c : ∀ ω, Continuous (L' ω)) (hR'0 : ∀ ω, R' ω 0 = 0)
    (hL'0 : ∀ ω, L' ω 0 = 0) (hR'm : ∀ t, Measurable fun ω => R' ω t) (hL'm : ∀ t, Measurable fun ω => L' ω t)
    (hdetR' : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R' ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL' : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L' ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR' : Sec6.IsEntranceHistoryLocal R' (centredField h u₀) P)
    (hlocL' : Sec6.IsEntranceHistoryLocal L' (centredField h u₀) P)
    {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {r : ℝ≥0} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hn : Measurable[wallsSigma P R L] n) (q : ℝ≥0)
    {r' : ℝ≥0} {ψ' : Ω → ℂ → ℂ} {n' : Ω → ℤ} {G' A' : Set Ω}
    (hGm' : MeasurableSet[wallsSigma P R' L'] G')
    (hcfg' : ∀ ω ∈ G', IsCfPocketConfig (R' ω) (L' ω) r' (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA' : MeasurableSet[wallsSigma P R' L'] A') (hAG' : A' ⊆ G') (hζA' : ∀ ω ∈ A', ζ' ω = ⊤)
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω))
    (hψm' : @IsPointMeasurable Ω (wallsSigma P R' L') R' L' r' G' ψ')
    (hn' : Measurable[wallsSigma P R' L'] n') (q' : ℝ≥0)
    {gC gU : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (pocketSet A R L r η ψ n q) (centredField h'' u₀') P gC)
    (hgU : IsLocalSetMean (pocketSet A' R' L' r' η ψ' n' q') (centredField h'' u₀') P gU) :
    ∀ᵐ ω ∂P, ∀ v vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ pocketSet A R L r η ψ n q ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ pocketSet A R L r η ψ n q ω →
        gC ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vI (H \ pocketSet A' R' L' r' η ψ' n' q' ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ pocketSet A' R' L' r' η ψ' n' q' ω →
        gU ω φ = ∫ z, vI z * φ z) →
      ∀ outer inner : Chart, outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
        (outer.dom : Set ℂ) = H \ pocketSet A R L r η ψ n q ω →
        (inner.dom : Set ℂ) = H \ pocketSet A' R' L' r' η ψ' n' q' ω →
        ∀ (p : ℂ) (ξ ρ : ℝ), p ∈ pocketSet A R L r η ψ n q ω ∪ {z : ℂ | z.im = 0} →
          p ∈ pocketSet A' R' L' r' η ψ' n' q' ω ∪ {z : ℂ | z.im = 0} →
          (∃ ε > 0, pocketSet A' R' L' r' η ψ' n' q' ω ∩ ball p ε ⊆ pocketSet A R L r η ψ n q ω) →
          (∃ ε > 0, pocketSet A R L r η ψ n q ω ∩ ball p ε ⊆ pocketSet A' R' L' r' η ψ' n' q' ω) → 0 < ρ →
          H ∩ ball (ξ : ℂ) ρ ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
          Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → R6Rel.R6Germ outer v vI ξ := by
  have hc4 : ∀ i ω, Continuous ((![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω) := by
    intro i ω; fin_cases i
    exacts [hRc ω, hLc ω, hR'c ω, hL'c ω]
  have h04 : ∀ i ω, (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 4 → ℂ) i := by
    intro i ω; fin_cases i
    exacts [hR0 ω, hL0 ω, hR'0 ω, hL'0 ω]
  have hm4 : ∀ i t, Measurable fun ω => (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω t := by
    intro i t; fin_cases i
    exacts [hRm t, hLm t, hR'm t, hL'm t]
  have hdet4 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) := by
    intro i t; fin_cases i
    exacts [hdetR t, hdetL t, hdetR' t, hdetL' t]
  have hloc4 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i)
      (centredField h u₀) P := by
    intro i; fin_cases i
    exacts [hlocR, hlocL, hlocR', hlocL']
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP₁ := isStopPocket_outer (X := fullHist ![R, L, R', L']) (wallsSigma_le hRm hLm)
    (wallsSigma_le_four_left hX R L R' L') hWad (measurable_right_wallsSigma (P := P) hRc hLc)
    (measurable_left_wallsSigma (P := P) hRc hLc) hGm hcfg hA hAG hζA hψ hψm hηm hn q
  have hP₂ := isStopPocket_cf (X := fullHist ![R, L, R', L']) (wallsSigma_le hR'm hL'm)
    (wallsSigma_le_four_right hX R L R' L') hWad (measurable_right_wallsSigma (P := P) hR'c hL'c)
    (measurable_left_wallsSigma (P := P) hR'c hL'c) hGm' hcfg' hA' hAG' hζA' hψ' hψm' hηm hn' q'
  have e4 := fun ω => congrFun (walls_union_eq_four R L R' L') ω
  have hΓ : Measurable[mΩ, hittingSigma] (fun ω => negInv '' (range (R ω) ∪ range (L ω)) ∪
      negInv '' (range (R' ω) ∪ range (L' ω))) := by
    rw [walls_union_eq_four]; exact measurable_negInv_walls hc4 hm4
  obtain ⟨hCm, hCloc, hCunb⟩ := isLocalSet_activeCompl_outer hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL hGm hcfg hA hAG hζA hψ hψm hηm hn q
  obtain ⟨hUm, hUloc, hUunb⟩ := isLocalSet_activeCompl_cf hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hR'c hL'c hR'0 hL'0
    hR'm hL'm hdetR' hdetL' hlocR' hlocL' hGm' hcfg' hA' hAG' hζA' hψ' hψm' hηm hn' q'
  refine ae_r6Germ_of_stopPockets hC hκ' hu₀' hX hζ (measurable_fullHist hm4) hΓ ?_ hP₁ hP₂ hCm hUm hCloc hUloc
    (Eventually.of_forall hCunb) (Eventually.of_forall hUunb) hgC hgU
  intro U G hUH hG hd B hB
  have hW := walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc4 h04 hm4 hdet4 hloc4 U G hUH hG hd B hB
  simp only [← e4] at hW
  exact hW

end InteractingSLE.Sec7.R6Cert
