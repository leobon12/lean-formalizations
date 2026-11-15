/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseClauses
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefTimes

/-!
# Lemma R.5 on the two-seed change-pocket tests of a walls' event

Packet PROVE-R5-PHASE. For the change pocket of two walls traversed by the counterflow, R.5's phase word
(`PhaseCont.TwoSeedPhaseWordInput(Inf)`, the conclusion of `PhaseCont.R7PhaseWordRemaining`) follows from R.5's
remaining clauses (`R5Clauses`) against the old references of the countable original-time family
`Current.SideTest.rationalOriginalTime` (the pocket exterior with the counterflow's hull at each rational original
time):

* `TwoSeedR5Input`, `TwoSeedR5InputInf` (defs): on every test of the walls' event, a walls-measurable chart branch,
  an offset, a phase and, at every relative capacity, `R5Clauses` for the two-seed word;
* **`twoSeedPhaseWordInput_of_r5`**, **`twoSeedPhaseWordInputInf_of_r5`**: the phase word on every test. The raw
  reference laws (`pocketStopUnionLaw_ref`), the base chart's analytic data (`shiftChart_aux29Facts`), the
  hitting measurability of the active complement (`PhaseCont.measurable_activeCompl_locPrefixSigma`) and the
  zero-boundary field are discharged from the walls' data.

No margin or weight restriction. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Phase

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont

universe u

/-- The old references of Lemma R.5: the counterflow's regularized hull at the rational original times. -/
def refHull {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (i : ℕ) : Ω → Set ℂ :=
  regHull W ζ (Wire.Current.SideTest.rationalOriginalTime i)

section Defs

variable {Ω : Type*}

/-- **Lemma R.5's remaining clauses on every test of a walls' event** (bounded change pocket): in a walls-measurable
chart branch `n`, with an offset `a`, a phase `δ_q`, exceptional sets `X_q`, reference lifts, pair events and
reference charts, `R5Clauses` holds at every relative capacity for the two-seed word, against the references
`F`. -/
def TwoSeedR5Input (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (F : ℕ → Ω → Set ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (liftB : ℝ≥0 → ℕ → Ω → ℂ → ℝ) (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5Clauses κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (fun ω => cfPocket (R ω) (L ω) r) F (δ q) (X q) (liftB q) (M q) (old q) q

/-- **Lemma R.5's remaining clauses on every test of a walls' event** (pocket opening at the flow seed). -/
def TwoSeedR5InputInf (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (F : ℕ → Ω → Set ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (liftB : ℝ≥0 → ℕ → Ω → ℂ → ℝ) (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5Clauses κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (fun ω => cfPocket (R ω) (L ω) r) F (δ q) (X q) (liftB q) (M q) (old q) q

end Defs


/-! ### R.5's phase word on every test from the remaining clauses -/

section Wire

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's phase word on every test of a walls' event from its remaining clauses** (bounded change pocket): the raw
reference laws at the rational original times, the base chart's analytic data, the hitting measurability of the
active complement and the zero-boundary field are discharged from the walls' data (those of
`PhaseCont.twoSeedPhaseConstInput_of_word`). -/
theorem twoSeedPhaseWordInput_of_r5 [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedR5Input κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ')) :
    TwoSeedPhaseWordInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, X, liftB, M, old, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨n, hn, a', δ, fun q => ?_⟩
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm' hLm' hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
      hψm
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
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  have hKm := (measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψc hCm hψm' hCin hcd q).mono
    (locPrefixSigma_le h𝓦 hA hγ hγm q) le_rfl
  have hpre : ∀ i, locPrefixSigma (refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) A
      (travAll R L r η ψ) 0 ≤ mΩ := fun i => by
    rw [PocketStopSide.locPrefixSigma_zero_of_driven (wallsSigma_le_refInfo hX R L _ _ hA) hγ]
    exact refInfo_le hX hRm hLm _
  exact pocketStopPhaseSideLimit_of_r5Clauses
    (ℳ := fun i => refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) hκ
    (isZeroBoundaryGFF_centredField hC hu₀') hpre hCo (fun i ω _ => isOpen_H_diff_regHull W' ζ' _ ω)
    (fun i => pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL hGm hG hA hAG hγ _) hγ hcA hcExt hcInf hKm hu₀'.1 hu₀'.2.1 (hcl q)

/-- **R.5's phase word on every test of a walls' event from its remaining clauses** (pocket opening at the flow
seed; as `twoSeedPhaseWordInput_of_r5`). -/
theorem twoSeedPhaseWordInputInf_of_r5 [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedR5InputInf κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ')) :
    TwoSeedPhaseWordInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, X, liftB, M, old, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨n, hn, a', δ, fun q => ?_⟩
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travSubInf h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω =>
    Or.inr ⟨cfPt (closePt (R ω) (L ω) r), hψ ω hω⟩
  obtain ⟨hcA, hcExt, hcInf⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hcd := shiftChart_dom_facts hCo hCH hψc n
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  have hKm := (measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψc hCm hψm' hCin hcd q).mono
    (locPrefixSigma_le h𝓦 hA hγ hγm q) le_rfl
  have hpre : ∀ i, locPrefixSigma (refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) A
      (travAllInf R L r η ψ) 0 ≤ mΩ := fun i => by
    rw [PocketStopSide.locPrefixSigma_zero_of_driven (wallsSigma_le_refInfo hX R L _ _ hA) hγ]
    exact refInfo_le hX hRm hLm _
  exact pocketStopPhaseSideLimit_of_r5Clauses
    (ℳ := fun i => refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) hκ
    (isZeroBoundaryGFF_centredField hC hu₀') hpre hCo (fun i ω _ => isOpen_H_diff_regHull W' ζ' _ ω)
    (fun i => pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL hGm hG hA hAG hγ _) hγ hcA hcExt hcInf hKm hu₀'.1 hu₀'.2.1 (hcl q)

end Wire

end InteractingSLE.Sec7.R5Phase
