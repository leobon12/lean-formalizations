/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseContR7
import InteractingSLE.Spec.Sec7.OuterPhNextMeans
import InteractingSLE.Spec.Sec7.R6RelInner

/-!
# Theorem 1.2's R.7, outer pockets: the continuity of the phase from R.5 up to phase alone

Packet PROVE-OUTER-CONT. PROVE-R7-OUTERPHASE reduced the outer pockets' side field (`k/2 − 4 < max rL rR`) to the
named input `OuterPhNext.R7OuterPhaseContRemaining`: on every outer R.7 pocket test (`HOuter.IsOuterCfg(Inf)`),
(1) R.5 up to a lattice phase `δ` and (2) the continuity of `δ` on the positive relative lifetime. PROVE-PHASECONT
proved (2) from (1) for the extremal pockets (`PhaseCont.r7PhaseContRemaining_of_word`). Here the same is done for
the outer pockets: the per-test constancy theorem `PhaseCont.exists_const_phase_of_stop` is generic in the pocket
geometry, and the outer pockets supply its geometric data through their relative hulls (`HOuter.relHull`, as in
`OuterPhNext.twoSeedPhaseMeansInput_of_const_outer`) and their marked walls' law at the left fibre endpoint
(`PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked`, R67).

## Main results

* **`twoSeedPhaseConstInput_of_word_outer`**, **`twoSeedPhaseConstInputInf_of_word_outer`**: on an event of outer
  configurations, R.5 up to phase gives a phase that is almost surely one constant on the positive lifetime;
* `R7OuterPhaseWordMRemaining` (**named input**: (1) alone on every outer R.7 configuration, at margins `c, c'`; the
  premises of `R6Rel.R7OuterPhaseContMRemaining` verbatim) and `R7OuterPhaseWordRemaining` (its instance at the
  Theorem 1.2 margins `(πχ(16/k), 0)`); `r7OuterPhaseWordMRemaining_of_contM`, `r7OuterPhaseWordRemaining_of_cont`
  (the new inputs are weaker);
* **`r7OuterPhaseContMRemaining_of_word`**, **`r7OuterPhaseContRemaining_of_word`**: (1) and (2) from (1) alone;
* **`hOuterCont_of_word`**: Theorem 1.2's binder `hOuterCont` from the word-only binder.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.OuterCont

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont

universe u

/-! ### The constant phase on an event of outer configurations -/

section Wire

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The constant phase from R.5 up to phase on outer pockets** (bounded change pocket): the outer walls' marked union
law at `T⁰(q)` (`PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked`), the relative hulls as the pocket's
exterior sets (`HOuter.isOpen_H_diff_relHull`, `HOuter.image_inter_H_diff_relHull`, `HOuter.pocketStopUnionLaw_outer`),
exactly as in `OuterPhNext.twoSeedPhaseMeansInput_of_const_outer`, and the walls-measurability of the pocket-inclusion
events (`Lemma725RefMarks.measurableSet_subset_cfPocket`); then `PhaseCont.exists_const_phase_of_stop` on each test. -/
theorem twoSeedPhaseConstInput_of_word_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 4 < κ)
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
    (hin : TwoSeedPhaseWordInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    TwoSeedPhaseConstInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, hside⟩ := hin A hA hAG hPA ψ hψ hψm
  have hκ0 : 0 < κ := by linarith
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the outer walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ0
    hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm'
    hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the outer traversal and its relative hulls supply the pocket geometry
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAll_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hdrive hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  obtain ⟨c₀, hconst⟩ := exists_const_phase_of_stop (κ := κ)
    (F := fun q ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) q)
    hκ h𝓦 hA hPA hdrive hγm
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin
    (fun q ω hω hq => HOuter.isOpen_H_diff_relHull
      (isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1.1.continuousOn (hdrive ω hω) hq)
    (fun q ω hω _ => HOuter.image_inter_H_diff_relHull
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1 (travAll R L r η ψ ω) q)
    (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => HOuter.pocketStopUnionLaw_outer h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm (hpre q) (hwalls q)) hside
  exact ⟨n, hn, a', δ, c₀, hside, hconst⟩

/-- **The constant phase from R.5 up to phase on outer pockets** (pocket opening at the flow seed; as
`twoSeedPhaseConstInput_of_word_outer`, with the walls' law and geometry of
`OuterPhNext.twoSeedPhaseMeansInputInf_of_const_outer`). -/
theorem twoSeedPhaseConstInputInf_of_word_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 4 < κ)
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
    (hin : TwoSeedPhaseWordInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    TwoSeedPhaseConstInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, hside⟩ := hin A hA hAG hPA ψ hψ hψm
  have hκ0 : 0 < κ := by linarith
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the outer walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀ hh hC
    hκ0 hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm'
    hLm' hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the outer traversal and its relative hulls supply the pocket geometry
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    HOuter.measurable_travAllInf_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hdrive hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  obtain ⟨c₀, hconst⟩ := exists_const_phase_of_stop (κ := κ)
    (F := fun q ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAllInf R L r η ψ ω) q)
    hκ h𝓦 hA hPA hdrive hγm
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin
    (fun q ω hω hq => HOuter.isOpen_H_diff_relHull
      (isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1.1.continuousOn (hdrive ω hω) hq)
    (fun q ω hω _ => HOuter.image_inter_H_diff_relHull
      (PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
      (hψ ω hω).2.2.2.1 (travAllInf R L r η ψ ω) q)
    (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => HOuter.pocketStopUnionLaw_outerInf h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm (hpre q) (hwalls q)) hside
  exact ⟨n, hn, a', δ, c₀, hside, hconst⟩

end Wire

/-! ### Every outer R.7 configuration -/

section Remaining

open R7Outer R7Leaves StripPocketConfig RefWire HOuter

/-- **R.5 up to phase on every outer R.7 configuration, at margins `c, c'`** (named input replacing
`R6Rel.R7OuterPhaseContMRemaining`): the premises are exactly those of `R6Rel.R7OuterPhaseContMRemaining` (hence of
`OuterPhNext.R7OuterPhaseContRemaining` at `(πχ(16/k), 0)`); the conclusion asks, on every outer pocket test, only
for R.5's phase word (1), without the continuity of the phase (2), which is proved
(`r7OuterPhaseContMRemaining_of_word`). This is the outer counterpart of `PhaseCont.R7PhaseWordRemaining` (pocket
premises `IsOuterCfg(Inf)` instead of `IsCfPocketConfig(Inf)`). -/
def R7OuterPhaseWordMRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedPhaseWordInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseWordInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **R.5 up to phase on every outer R.7 configuration** at Theorem 1.2's margins `(πχ(16/k), 0)` (named input
replacing `OuterPhNext.R7OuterPhaseContRemaining`). -/
def R7OuterPhaseWordRemaining (k rL rR : ℝ) : Prop :=
  R7OuterPhaseWordMRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- `R6Rel.R7OuterPhaseContMRemaining` ((1) and (2)) implies `R7OuterPhaseWordMRemaining` ((1)): the new named input
is weaker. -/
theorem r7OuterPhaseWordMRemaining_of_contM {k rL rR c c' : ℝ}
    (h : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c') : R7OuterPhaseWordMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h₁ W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := h P h₁ W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedPhaseWordInput_of_cont hs, twoSeedPhaseWordInputInf_of_cont hsI⟩

/-- `OuterPhNext.R7OuterPhaseContRemaining` implies `R7OuterPhaseWordRemaining`. -/
theorem r7OuterPhaseWordRemaining_of_cont {k rL rR : ℝ}
    (h : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR) : R7OuterPhaseWordRemaining.{u} k rL rR :=
  r7OuterPhaseWordMRemaining_of_contM (R6Rel.r7OuterPhaseContMRemaining_of_std h)

/-- **(1) and (2) on every outer R.7 configuration from R.5 up to phase alone, at margins `c, c' ≥ 0`**: the walls'
data are derived from the configuration exactly as in `OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared` (and
`PhaseCont.r7PhaseConstRemaining_of_word`), then `twoSeedPhaseConstInput(Inf)_of_word_outer` on the two kinds of
change pockets and `PhaseCont.twoSeedPhaseContInput(Inf)_of_const`. -/
theorem r7OuterPhaseContMRemaining_of_word {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hword : R7OuterPhaseWordMRemaining.{u} k rL rR c c') : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hword P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedPhaseContInput_of_const (twoSeedPhaseConstInput_of_word_outer hk4 hT' hTr hu₀.1 hh0 hC hu₀' hX
      hζ hV.R_cont hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp
      (fun ω hω => hcfgP ω hω.1 hω.2) (fun ω hω => hζG ω hω.1) hs),
    twoSeedPhaseContInputInf_of_const (twoSeedPhaseConstInputInf_of_word_outer hk4 hT' hTr hu₀.1 hh0 hC hu₀' hX
      hζ hV.R_cont hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI'
      (fun ω hω => hζG ω hω.1) hsI)⟩

/-- **`OuterPhNext.R7OuterPhaseContRemaining` from R.5 up to phase alone** (Theorem 1.2's margins
`(πχ(16/k), 0)`, `πχ(16/k) ≥ 0`): the continuity of the phase (2) is proved. -/
theorem r7OuterPhaseContRemaining_of_word {k rL rR : ℝ} (hk4 : 4 < k)
    (hword : R7OuterPhaseWordRemaining.{u} k rL rR) : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR :=
  R6Rel.r7OuterPhaseContRemaining_of_marg (r7OuterPhaseContMRemaining_of_word hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)).le)
    le_rfl hword)

/-- **Theorem 1.2's binder `hOuterCont` from the word-only binder**: for the outer pairs (`k/2 − 4 < max rL rR`),
R.5 up to phase on every outer R.7 configuration gives `OuterPhNext.R7OuterPhaseContRemaining`. -/
theorem hOuterCont_of_word
    (hOuterWord : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterPhaseWordRemaining.{u} k rL rR) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR :=
  fun k hk4 rL rR hL hR hmax => r7OuterPhaseContRemaining_of_word hk4 (hOuterWord k hk4 rL rR hL hR hmax)

end Remaining

end InteractingSLE.Sec7.OuterCont
