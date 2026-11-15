/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCapacity
import InteractingSLE.Spec.Sec7.R5OutWire
import InteractingSLE.Spec.Sec7.HOuterMarkedInf

/-!
# Outer continuity from relative incident-reference covers

PROVE-R5-OUTER, R88. This is a replacement interface for `hOuterR5`:
only reference collar/height geometry and retained-chart measurability remain.
The relative hull laws and conditioned increment laws are derived from the
original coupling and walls data, then fed into the component R.5 engine.
-/

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
  PhaseCont R5Phase OuterCont R5Enl PhaseSel

universe u

section Defs

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The remaining collar, reference-height and forward-chart data for relative incident references.
No local-set law or old-chart increment law is an input. -/
def TwoSeedR5RelativeCoverInputOn (κ rL rR : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
        ∀ q : ℝ≥0, ∃ (p : ℕ → ℝ≥0) (X : Ω → Set ℂ),
          let γ := travAll R L r η ψ;
          let C := fun ω => cfPocket (R ω) (L ω) r;
          let c := fun ω => shiftChart (pChart A C ψ ω) (n ω);
          (∀ i, p i ≤ q) ∧ (∀ ω, (X ω).Finite) ∧
          (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
          (∀ i z, Measurable[germSigma (activeCompl A γ c (p i)) h₀ ⊔
            locPrefixSigma (wallsSigma P R L) A γ (p i)]
            (({ω | ω ∈ A ∧ (p i : ℝ≥0∞) < capLife (γ ω)} ∩
              {ω | z ∈ (relChart c γ (p i) ω).dom}).indicator fun ω => (relChart c γ (p i) ω).1 z)) ∧
          R5Wall.R5Cover κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u C
            (fun i => activeCompl A γ c (p i)) (δ q) X (fun i ω => (relChart c γ (p i) ω).2.2)
            (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)})
            (fun i => relChart c γ (p i)) q (fun _ _ => True)

/-- The remaining collar, reference-height and forward-chart data for relative incident references.
No local-set law or old-chart increment law is an input. -/
def TwoSeedR5RelativeCoverInputInfOn (κ rL rR : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
        ∀ q : ℝ≥0, ∃ (p : ℕ → ℝ≥0) (X : Ω → Set ℂ),
          let γ := travAllInf R L r η ψ;
          let C := fun ω => cfPocket (R ω) (L ω) r;
          let c := fun ω => shiftChart (pChart A C ψ ω) (n ω);
          (∀ i, p i ≤ q) ∧ (∀ ω, (X ω).Finite) ∧
          (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
          (∀ i z, Measurable[germSigma (activeCompl A γ c (p i)) h₀ ⊔
            locPrefixSigma (wallsSigma P R L) A γ (p i)]
            (({ω | ω ∈ A ∧ (p i : ℝ≥0∞) < capLife (γ ω)} ∩
              {ω | z ∈ (relChart c γ (p i) ω).dom}).indicator fun ω => (relChart c γ (p i) ω).1 z)) ∧
          R5Wall.R5Cover κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u C
            (fun i => activeCompl A γ c (p i)) (δ q) X (fun i ω => (relChart c γ (p i) ω).2.2)
            (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)})
            (fun i => relChart c γ (p i)) q (fun _ _ => True)

end Defs

section Wire

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Outer phase word from relative reference covers and the original coupling. -/
theorem twoSeedPhaseWordInput_of_relativeCover_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedR5RelativeCoverInputOn κ rL rR P R L r η G (centredField h'' u₀') u₀') :
    TwoSeedPhaseWordInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨n, hn, a', δ, fun q => ?_⟩
  obtain ⟨p, X, hpq, hXf, hLattice, hfwd, hCover⟩ := hcl q
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAll_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
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
  have hU : ∀ s, PocketStopUnionLaw (wallsSigma P R L) P A (travAll R L r η ψ)
      (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) s)
      (centredField h'' u₀') s := by
    intro s
    have hWs := PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0_marked
      hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      (PocketWordPerQ.wallsSigma_le_drivingFiltration (P := P) hX R L) hRm' hLm' hGm hG hA hAG
      (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm s
    exact HOuter.pocketStopUnionLaw_outer h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm
      (locPrefixSigma_le h𝓦 hA hγ hγm s) hWs
  exact pocketStopPhaseSideLimit_of_relativeCover (isZeroBoundaryGFF_centredField hC hu₀') h𝓦 hA hγ hγm
    hCo hCH hψc hCm hψm' hCin hcd hU hpq hfwd hXf hLattice hCover hκ
    (fun ω hω => (hcA ω hω).2) hcExt hcInf hu₀'.1 hu₀'.2.1

/-- Seed-opening outer phase word from relative reference covers. -/
theorem twoSeedPhaseWordInputInf_of_relativeCover_outer [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
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
    (hin : TwoSeedR5RelativeCoverInputInfOn κ rL rR P R L r η G (centredField h'' u₀') u₀') :
    TwoSeedPhaseWordInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, hcl⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨n, hn, a', δ, fun q => ?_⟩
  obtain ⟨p, X, hpq, hXf, hLattice, hfwd, hCover⟩ := hcl q
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    HOuter.measurable_travAllInf_outer h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
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
  have hU : ∀ s, PocketStopUnionLaw (wallsSigma P R L) P A (travAllInf R L r η ψ)
      (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAllInf R L r η ψ ω) s)
      (centredField h'' u₀') s := by
    intro s
    have hWs := PocketStopMarked.Outer.pocketStopWallsLaw_stopHull0Inf_marked
      hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      (PocketWordPerQ.wallsSigma_le_drivingFiltration (P := P) hX R L) hRm' hLm' hGm hG hA hAG
      (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm s
    exact HOuter.pocketStopUnionLaw_outerInf h𝓦 hRm' hLm' hGm hcfg hA hAG hψ hψm
      (locPrefixSigma_le h𝓦 hA hγ hγm s) hWs
  exact pocketStopPhaseSideLimit_of_relativeCover (isZeroBoundaryGFF_centredField hC hu₀') h𝓦 hA hγ hγm
    hCo hCH hψc hCm hψm' hCin hcd hU hpq hfwd hXf hLattice hCover hκ
    (fun ω hω => (hcA ω hω).2) hcExt hcInf hu₀'.1 hu₀'.2.1

end Wire

section Remaining

open R7Outer R7Leaves StripPocketConfig RefWire HOuter

/-- **Lemma R.5's conditioned clauses on every outer R.7 configuration** (named input; margins `c`, `c′`): the
premises are exactly those of `R7OuterPhaseWordMRemaining` (hence of `R6Rel.R7OuterPhaseContMRemaining`); the
conclusion is `R5Enl.TwoSeedR5Input(Inf)On` against the old references at the rational original times of the
counterflow (`R5Phase.refHull`) — the same clause form as the extremal pockets' `R5Enl.R7R5RemainingOn`, with the
pocket premises `IsOuterCfg(Inf)` instead of `IsCfPocketConfig(Inf)`. -/
def R7OuterRelativeCoverMRemaining (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedR5RelativeCoverInputOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedR5RelativeCoverInputInfOn k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **Lemma R.5's conditioned clauses on every outer R.7 configuration** at Theorem 1.2's margins `(πχ(16/k), 0)`. -/
def R7OuterRelativeCoverRemaining (k rL rR : ℝ) : Prop :=
  R7OuterRelativeCoverMRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- **`R7OuterPhaseWordMRemaining` at all margins `c, c' ≥ 0` from Lemma R.5's conditioned clauses**: the walls' data
are derived from the configuration exactly as in `R5Enl.r7PhaseWordRemaining_of_relativeCover`, then
`twoSeedPhaseWordInput(Inf)_of_relativeCover_outer` on the two kinds of outer change pockets. -/
theorem r7OuterPhaseWordMRemaining_of_relativeCover {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7OuterRelativeCoverMRemaining.{u} k rL rR c c') : R7OuterPhaseWordMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hr5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
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
  exact ⟨twoSeedPhaseWordInput_of_relativeCover_outer hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2) (fun ω hω => hζG ω hω.1) hs,
    twoSeedPhaseWordInputInf_of_relativeCover_outer hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1) hsI⟩

/-- **R.5 up to phase and its continuity on every outer R.7 configuration at margins `c, c' ≥ 0` from Lemma R.5's
remaining clauses** (`r7OuterPhaseWordMRemaining_of_relativeCover`, then `r7OuterPhaseContMRemaining_of_word`). -/
theorem r7OuterPhaseContMRemaining_of_relativeCover {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hr5 : R7OuterRelativeCoverMRemaining.{u} k rL rR c c') : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseContMRemaining_of_word hk4 hc hc' (r7OuterPhaseWordMRemaining_of_relativeCover hk4 hc hc' hr5)

/-- **`OuterPhNext.R7OuterPhaseContRemaining` from Lemma R.5's conditioned clauses on the outer configurations**
(Theorem 1.2's margins `(πχ(16/k), 0)`). -/
theorem r7OuterPhaseContRemaining_of_relativeCover {k rL rR : ℝ} (hk4 : 4 < k) (hr5 : R7OuterRelativeCoverRemaining.{u} k rL rR) :
    OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR :=
  r7OuterPhaseContRemaining_of_word hk4 (r7OuterPhaseWordMRemaining_of_relativeCover hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)).le)
    le_rfl hr5)

/-- **Theorem 1.2's binder `hOuterCont` from Lemma R.5's conditioned clauses on the outer configurations**. -/
theorem hOuterCont_of_relativeCover
    (hOuterCover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterRelativeCoverRemaining.{u} k rL rR) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR :=
  fun k hk4 rL rR hL hR hmax => r7OuterPhaseContRemaining_of_relativeCover hk4 (hOuterCover k hk4 rL rR hL hR hmax)

end Remaining

end InteractingSLE.Sec7.R5Out
