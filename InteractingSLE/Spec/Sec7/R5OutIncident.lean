/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutRefs
import InteractingSLE.Spec.Sec7.HOuterStop

/-!
# Conditioned increments in the outer incident component

PROVE-R5-OUTER, R88. The active-domain identity is with the relative
hull, and the reference record is an earlier relative prefix. The only
chart measurability input is the same retained forward-map input `hfwd`
as in the existing enlarged-law argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketTraversal PocketAdapt PocketCoupling PocketUnionPt
  PocketStopSide PocketStop R5Enl PocketStopField R5Phase Lemma71C
  PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketMarks
  PocketStopWallsFin Lemma725RefMarks

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Relative hull union laws give the conditioned law between incident-component charts. -/
theorem hasOldChartIncrementLawOn_relHull
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (hU : ∀ s, PocketStopUnionLaw 𝓦 P A γ C
      (fun ω => HOuter.relHull (C ω) (ψ ω) (γ ω) s) h₀ s)
    {p q : ℝ≥0} (hpq : p ≤ q)
    (hfwd : ∀ z, Measurable[germSigma (activeCompl A γ c p) h₀ ⊔ locPrefixSigma 𝓦 A γ p]
      (({ω | ω ∈ A ∧ (p : ℝ≥0∞) < capLife (γ ω)} ∩
        {ω | z ∈ (relChart c γ p ω).dom}).indicator fun ω => (relChart c γ p ω).1 z)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (activeCompl A γ c p) h₀ P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A γ c q) h₀ P gNow →
        HasOldChartIncrementLawOn P {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}
          (relChart c γ p) (relChart c γ q) gOld gNow := by
  have hact : ∀ (s : ℝ≥0) ω, ω ∈ A → (s : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c s ω = C ω ∩ (H \ HOuter.relHull (C ω) (ψ ω) (γ ω) s) := by
    intro s ω hω hs
    rw [activeDom_eq_relChart_dom hω hs (hγ ω hω) (hc ω hω).1,
      current_dom_eq_relHull hω hs (hγ ω hω) (hc ω hω).1 (hc ω hω).2.1
        (hc ω hω).2.2 (hCH ω hω) (hψ ω hω),
      HOuter.H_diff_relHull (hCH ω hω), ← inter_assoc, inter_self]
  exact hasOldChartIncrementLawOn_relative hh₀ hγ (fun ω hω => (hc ω hω).1) hCo
    (fun s ω hω hs => HOuter.isOpen_H_diff_relHull (hCo ω hω) (hCH ω hω)
      (hψ ω hω).1.continuousOn (hγ ω hω) hs) hact
    (locPrefixSigma_le h𝓦 hA hγ hγm) hU hpq
    (PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc p) hfwd

/-- The conditioned increment law in the target-incident component of an outer pocket. -/
theorem hasOldChartIncrementLawOn_outer
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G A : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∧
      EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hW : ∀ s, PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ)
      (fun ω => WangWu.negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r W η ψ s) h₀ s)
    {p q : ℝ≥0} (hpq : p ≤ q)
    (hfwd : ∀ z, Measurable[germSigma (activeCompl A (travAll R L r η ψ) c p) h₀ ⊔
      locPrefixSigma 𝓦 A (travAll R L r η ψ) p]
      (({ω | ω ∈ A ∧ (p : ℝ≥0∞) < capLife (travAll R L r η ψ ω)} ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) p ω).dom}).indicator
          fun ω => (relChart c (travAll R L r η ψ) p ω).1 z)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (activeCompl A (travAll R L r η ψ) c p) h₀ P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) h₀ P gNow →
        HasOldChartIncrementLawOn P {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)}
          (relChart c (travAll R L r η ψ) p) (relChart c (travAll R L r η ψ) q) gOld gNow := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAll_outer h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH
  exact hasOldChartIncrementLawOn_relHull hh₀ h𝓦 hA hγ hγm hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin hc
    (fun s => HOuter.pocketStopUnionLaw_outer h𝓦 hRm hLm hGm hcfg hA hAG hψ hψm
      (locPrefixSigma_le h𝓦 hA hγ hγm s) (hW s)) hpq hfwd

/-- The conditioned increment law in the target-incident component of an outer pocket. -/
theorem hasOldChartIncrementLawOn_outerInf
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G A : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∧
      EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hW : ∀ s, PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ)
      (fun ω => WangWu.negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r W η ψ s) h₀ s)
    {p q : ℝ≥0} (hpq : p ≤ q)
    (hfwd : ∀ z, Measurable[germSigma (activeCompl A (travAllInf R L r η ψ) c p) h₀ ⊔
      locPrefixSigma 𝓦 A (travAllInf R L r η ψ) p]
      (({ω | ω ∈ A ∧ (p : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)} ∩
        {ω | z ∈ (relChart c (travAllInf R L r η ψ) p ω).dom}).indicator
          fun ω => (relChart c (travAllInf R L r η ψ) p ω).1 z)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (activeCompl A (travAllInf R L r η ψ) c p) h₀ P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAllInf R L r η ψ) c q) h₀ P gNow →
        HasOldChartIncrementLawOn P {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)}
          (relChart c (travAllInf R L r η ψ) p) (relChart c (travAllInf R L r η ψ) q) gOld gNow := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAllInf_outer h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      subset_closure hω.2
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH
  exact hasOldChartIncrementLawOn_relHull hh₀ h𝓦 hA hγ hγm hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin hc
    (fun s => HOuter.pocketStopUnionLaw_outerInf h𝓦 hRm hLm hGm hcfg hA hAG hψ hψm
      (locPrefixSigma_le h𝓦 hA hγ hγm s) (hW s)) hpq hfwd

end InteractingSLE.Sec7.R5Out
