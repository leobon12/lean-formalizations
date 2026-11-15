/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseConst
import InteractingSLE.Spec.Sec7.HOuterStop
import InteractingSLE.Spec.Sec7.HOuterMarkedStop
import InteractingSLE.Spec.Sec7.HOuterMarkedInf

/-!
# Outer-pocket retained phase means from the phase word

PROVE-R7-OUTERPHASE continuation. Reuse the phase conditional-law pipeline on
outer pockets. The marked stop is the left erasure-fibre endpoint, while the
active sets are the relative hull sets. R.5 up to a constant phase remains an
explicit named input; this file proves its retained-mean consequence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.OuterPhNext

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The outer-pocket phase word and its constant positive-time phase give
retained phase means, using the outer marked union law and relative hulls. -/
theorem twoSeedPhaseMeansInput_of_const_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedPhaseConstInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    PhaseSide.TwoSeedPhaseMeansInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, c₀, hside, hconst⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- The outer traversal and its relative hulls supply the pocket geometry.
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAll R L r η ψ ω u ∈ H ∧ M < ‖travAll R L r η ψ ω u‖ := fun ω hω =>
    ⟨((hcfg ω (hAG hω)).props (hψ ω hω)).1, ((hcfg ω (hAG hω)).props (hψ ω hω)).2.1⟩
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAll_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  exact ⟨n, hn, PhaseClause.twoSeedPhaseMeansAt_of_stop (κ := κ)
    (F := fun q ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) q)
    hκ h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun q ω hω hq => HOuter.isOpen_H_diff_relHull
      (isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1.1.continuousOn (hdrive ω hω).1 hq)
    (fun q ω hω _ => HOuter.image_inter_H_diff_relHull
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1 (travAll R L r η ψ ω) q)
    (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => HOuter.pocketStopUnionLaw_outer h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm
      (hpre q) (hwalls q)) hside hconst⟩

/-- Retained phase means for the outer pocket opening at the flow seed, using
the outer marked stop and relative hull geometry. -/
theorem twoSeedPhaseMeansInputInf_of_const_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedPhaseConstInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    PhaseSide.TwoSeedPhaseMeansInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, c₀, hside, hconst⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0Inf_marked
    hT' hTr hu₀ hh hC hκ hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- The outer traversal and its relative hulls supply the pocket geometry.
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAllInf R L r η ψ ω u ∈ H ∧ M < ‖travAllInf R L r η ψ ω u‖ := fun ω hω =>
    ⟨((hcfg ω (hAG hω)).props (hψ ω hω)).1, ((hcfg ω (hAG hω)).props (hψ ω hω)).2.1⟩
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    HOuter.measurable_travAllInf_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  exact ⟨n, hn, PhaseClause.twoSeedPhaseMeansAt_of_stop (κ := κ)
    (F := fun q ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAllInf R L r η ψ ω) q)
    hκ h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun q ω hω hq => HOuter.isOpen_H_diff_relHull
      (isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1.1.continuousOn (hdrive ω hω).1 hq)
    (fun q ω hω _ => HOuter.image_inter_H_diff_relHull
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1 (travAllInf R L r η ψ ω) q)
    (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => HOuter.pocketStopUnionLaw_outerInf h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm
      (hpre q) (hwalls q)) hside hconst⟩


end InteractingSLE.Sec7.OuterPhNext
