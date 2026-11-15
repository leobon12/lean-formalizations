/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseR7
import InteractingSLE.Spec.Sec7.R5EnlCollar

/-!
# Theorem 1.2's R.7 from Lemma R.5's clauses with the conditioned increment laws

Packet PROVE-R5-ENLARGED. PROVE-R5-PHASE's chain `R5Clauses → TwoSeedR5Input(Inf) → R7R5Remaining →
PhaseCont.R7PhaseWordRemaining` uses the unconditioned `HasOldChartIncrementLaw`, which R.5's references cannot
supply off the reference event (`R5EnlCond.lean`). The same chain with `R5ClausesOn` (`R5EnlCollar.lean`):

* `TwoSeedR5InputOn`, `TwoSeedR5InputInfOn`, **`twoSeedPhaseWordInput_of_r5On`**,
  **`twoSeedPhaseWordInputInf_of_r5On`**;
* `R7R5RemainingOn` (named input, premises those of `PhaseCont.R7PhaseWordRemaining`) and
  **`r7PhaseWordRemaining_of_r5On`** (`4 < k`, `0 ≤ c`, `0 ≤ c'`);
* `twoSeedR5InputOn_of_twoSeedR5Input`, `twoSeedR5InputInfOn_of_twoSeedR5InputInf`,
  `r7R5RemainingOn_of_r7R5Remaining`: the old forms imply the new ones, so `R7R5RemainingOn` is the weaker target.

The proofs are PROVE-R5-PHASE's, with `R5Enl.pocketStopPhaseSideLimit_of_r5ClausesOn` in place of
`R5Phase.pocketStopPhaseSideLimit_of_r5Clauses`. Conditional helpers with distinct names; nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` (R43, R48).
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

namespace InteractingSLE.Sec7.R5Enl

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R7Outer R7Leaves StripPocketConfig RefWire R5Phase

universe u

section Defs

variable {Ω : Type*}

/-- **Lemma R.5's conditioned clauses on every test of a walls' event** (bounded change pocket): in a walls-measurable
chart branch `n`, with an offset `a`, a phase `δ_q`, exceptional sets `X_q`, reference lifts, pair events and
reference charts, `R5ClausesOn` holds at every relative capacity for the two-seed word, against the references
`F`. -/
def TwoSeedR5InputOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (F : ℕ → Ω → Set ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (liftB : ℝ≥0 → ℕ → Ω → ℂ → ℝ) (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5ClausesOn κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (fun ω => cfPocket (R ω) (L ω) r) F (δ q) (X q) (liftB q) (M q) (old q) q

/-- **Lemma R.5's conditioned clauses on every test of a walls' event** (pocket opening at the flow seed). -/
def TwoSeedR5InputInfOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (F : ℕ → Ω → Set ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ)
        (liftB : ℝ≥0 → ℕ → Ω → ℂ → ℝ) (M : ℝ≥0 → ℕ → Set Ω) (old : ℝ≥0 → ℕ → Ω → Chart),
        ∀ q : ℝ≥0, R5ClausesOn κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (fun ω => cfPocket (R ω) (L ω) r) F (δ q) (X q) (liftB q) (M q) (old q) q

end Defs


/-! ### R.5's phase word on every test from the conditioned clauses -/

section Wire

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's phase word on every test of a walls' event from its conditioned clauses** (bounded change pocket): the raw
reference laws at the rational original times, the base chart's analytic data, the hitting measurability of the
active complement and the zero-boundary field are discharged from the walls' data (those of
`PhaseCont.twoSeedPhaseConstInput_of_word`). -/
theorem twoSeedPhaseWordInput_of_r5On [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedR5InputOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ')) :
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
  exact pocketStopPhaseSideLimit_of_r5ClausesOn
    (ℳ := fun i => refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) hκ
    (isZeroBoundaryGFF_centredField hC hu₀') hpre hCo (fun i ω _ => isOpen_H_diff_regHull W' ζ' _ ω)
    (fun i => pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL hGm hG hA hAG hγ _) hγ hcA hcExt hcInf hKm hu₀'.1 hu₀'.2.1 (hcl q)

/-- **R.5's phase word on every test of a walls' event from its conditioned clauses** (pocket opening at the flow
seed; as `twoSeedPhaseWordInput_of_r5On`). -/
theorem twoSeedPhaseWordInputInf_of_r5On [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedR5InputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀' (refHull W' ζ')) :
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
  exact pocketStopPhaseSideLimit_of_r5ClausesOn
    (ℳ := fun i => refInfo P hX R L (Wire.Current.SideTest.rationalOriginalTime i)) hκ
    (isZeroBoundaryGFF_centredField hC hu₀') hpre hCo (fun i ω _ => isOpen_H_diff_regHull W' ζ' _ ω)
    (fun i => pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL hGm hG hA hAG hγ _) hγ hcA hcExt hcInf hKm hu₀'.1 hu₀'.2.1 (hcl q)

end Wire

/-- **Lemma R.5's conditioned clauses on every R.7 configuration** (named input; margins `c`, `c′`): the premises are
exactly those of `PhaseCont.R7PhaseWordRemaining`; the conclusion is `TwoSeedR5InputOn(Inf)` against the old
references at the rational original times of the counterflow. -/
def R7R5RemainingOn (k rL rR c c' : ℝ) : Prop :=
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
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedR5InputOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' (refHull W' ζ') ∧
        TwoSeedR5InputInfOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' (refHull W' ζ')

/-- **`PhaseCont.R7PhaseWordRemaining` at all margins from Lemma R.5's conditioned clauses**: the walls' data are
derived from the configuration exactly as in `PhaseCont.r7PhaseConstRemaining_of_word`, then
`twoSeedPhaseWordInput(Inf)_of_r5` on the two kinds of change pockets. -/
theorem r7PhaseWordRemaining_of_r5On {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7R5RemainingOn.{u} k rL rR c c') : R7PhaseWordRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hr5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
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
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedPhaseWordInput_of_r5On hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2) hs,
    twoSeedPhaseWordInputInf_of_r5On hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' hsI⟩

section Implications

variable {Ω : Type*}

/-- The unconditioned per-test clauses imply the conditioned ones (bounded change pocket). -/
theorem twoSeedR5InputOn_of_twoSeedR5Input [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {F : ℕ → Ω → Set ℂ}
    (h : TwoSeedR5Input κ rL rR P R L r η G h₀ u F) : TwoSeedR5InputOn κ rL rR P R L r η G h₀ u F := by
  intro A hA hAG hPA ψ hψ hpt
  obtain ⟨n, hn, a, δ, X, liftB, M, old, hcl⟩ := h A hA hAG hPA ψ hψ hpt
  exact ⟨n, hn, a, δ, X, liftB, M, old, fun q => r5ClausesOn_of_r5Clauses (hcl q)⟩

/-- The unconditioned per-test clauses imply the conditioned ones (pocket opening at the flow seed). -/
theorem twoSeedR5InputInfOn_of_twoSeedR5InputInf [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {F : ℕ → Ω → Set ℂ}
    (h : TwoSeedR5InputInf κ rL rR P R L r η G h₀ u F) : TwoSeedR5InputInfOn κ rL rR P R L r η G h₀ u F := by
  intro A hA hAG hPA ψ hψ hpt
  obtain ⟨n, hn, a, δ, X, liftB, M, old, hcl⟩ := h A hA hAG hPA ψ hψ hpt
  exact ⟨n, hn, a, δ, X, liftB, M, old, fun q => r5ClausesOn_of_r5Clauses (hcl q)⟩

end Implications

/-- `R7R5Remaining` implies its conditioned form `R7R5RemainingOn`. -/
theorem r7R5RemainingOn_of_r7R5Remaining {k rL rR c c' : ℝ} (h : R7R5Remaining.{u} k rL rR c c') :
    R7R5RemainingOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h0 W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := h P h0 W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedR5InputOn_of_twoSeedR5Input hs, twoSeedR5InputInfOn_of_twoSeedR5InputInf hsI⟩

end InteractingSLE.Sec7.R5Enl
