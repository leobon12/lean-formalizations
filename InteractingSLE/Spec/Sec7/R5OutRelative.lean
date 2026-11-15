/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutKernel
import InteractingSLE.Spec.Sec7.PhaseContKernel

/-!
# R.5 increment laws between relative incident components

PROVE-R5-OUTER, R88. At deterministic relative capacities `p ≤ q`,
the earlier incident component is retained by the later relative history.
Adding its germ to the later marked union law gives the reference-to-current
increment law. No identity with the whole ambient pocket domain is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketTraversal PocketAdapt PocketCoupling PocketUnionPt
  PocketStopSide PocketStop R5Enl PocketStopField R5Phase Lemma71C

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The conditioned law from an earlier relative reference to the current incident component. -/
theorem hasOldChartIncrementLawOn_relative
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C : Ω → Set ℂ}
    {F : ℝ≥0 → Ω → Set ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ (s : ℝ≥0) ω, ω ∈ A → (s : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F s ω))
    (hact : ∀ (s : ℝ≥0) ω, ω ∈ A → (s : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c s ω = C ω ∩ (H \ F s ω))
    (hpre : ∀ s, locPrefixSigma 𝓦 A γ s ≤ mΩ)
    (hU : ∀ s, PocketStopUnionLaw 𝓦 P A γ C (F s) h₀ s)
    {p q : ℝ≥0} (hpq : p ≤ q)
    (hBm : Measurable[locPrefixSigma 𝓦 A γ p, hittingSigma] (activeCompl A γ c p))
    (hfwd : ∀ z, Measurable[germSigma (activeCompl A γ c p) h₀ ⊔ locPrefixSigma 𝓦 A γ p]
      (({ω | ω ∈ A ∧ (p : ℝ≥0∞) < capLife (γ ω)} ∩
        {ω | z ∈ (relChart c γ p ω).dom}).indicator fun ω => (relChart c γ p ω).1 z)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (activeCompl A γ c p) h₀ P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A γ c q) h₀ P gNow →
        HasOldChartIncrementLawOn P {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}
          (relChart c γ p) (relChart c γ q) gOld gNow := by
  have hBeq : activeCompl A γ c p = liveExt A γ C (F p) p :=
    activeCompl_eq_liveExt (hact p)
  have hKeq : activeCompl A γ c q = liveExt A γ C (F q) q :=
    activeCompl_eq_liveExt (hact q)
  have hBreg : ∀ ω, activeCompl A γ c p ω ⊆ H ∧
      IsOpen (H \ activeCompl A γ c p ω) :=
    activeCompl_regular (hact p) hCo (hFo p)
  have hKreg : ∀ ω, activeCompl A γ c q ω ⊆ H ∧
      IsOpen (H \ activeCompl A γ c q ω) :=
    activeCompl_regular (hact q) hCo (hFo q)
  obtain ⟨Ep, hEpm, hEploc, hEpeq⟩ := hU p
  have hBloc : IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ p)
      (activeCompl A γ c p) h₀ P := by
    rw [hBeq]
    exact isHistoryAvoidanceLocal_liveExt (measurableSet_live A γ p) hEploc hEpeq
  obtain ⟨g₀, hg₀, hHarm₀, hK₀⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hh₀ (hBm.mono (hpre p) le_rfl) (hpre p) hBloc (Eventually.of_forall hBreg)
  have hBmq : Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] (activeCompl A γ c p) :=
    hBm.mono (PhaseCont.locPrefixSigma_mono 𝓦 A γ hpq) le_rfl
  have hU' := pocketStopUnionLaw_sup_germSigma hh₀ (hpre q) hBmq
    (fun ω hω hq => by
      have hK := PhaseCont.activeCompl_mono (A := A) (γ := γ) (c := c) hpq ω
      rw [hKeq, liveExt_of_live ⟨hω, hq⟩] at hK
      exact fun z hz => hK hz.1) (hU q)
  have hpre' : locPrefixSigma (𝓦 ⊔ germSigma (activeCompl A γ c p) h₀) A γ q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le (hpre q) (germSigma_le (hBm.mono (hpre p) le_rfl) hh₀.measurable)
  obtain ⟨Eq, hEqm, hEqloc, hEqeq⟩ := hU'
  have hKloc : IsHistoryAvoidanceLocal
      (locPrefixSigma (𝓦 ⊔ germSigma (activeCompl A γ c p) h₀) A γ q)
      (activeCompl A γ c q) h₀ P := by
    rw [hKeq]
    exact isHistoryAvoidanceLocal_liveExt (measurableSet_live A γ q) hEqloc hEqeq
  have hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q) := by
    rw [hKeq]
    exact measurable_liveExt (hpre' _ (measurableSet_live A γ q)) hEqm hEqeq
  have hInfo : germSigma (activeCompl A γ c p) h₀ ⊔ locPrefixSigma 𝓦 A γ p ≤
      germSigma (activeCompl A γ c q) h₀ ⊔
        locPrefixSigma (𝓦 ⊔ germSigma (activeCompl A γ c p) h₀) A γ q := by
    rw [locPrefixSigma_sup_info]
    exact sup_le (le_sup_right.trans le_sup_right)
      ((PhaseCont.locPrefixSigma_mono 𝓦 A γ hpq).trans (le_sup_left.trans le_sup_right))
  have hG : MeasurableSet[germSigma (activeCompl A γ c p) h₀ ⊔ locPrefixSigma 𝓦 A γ p]
      {ω | ω ∈ A ∧ (p : ℝ≥0∞) < capLife (γ ω)} :=
    (show locPrefixSigma 𝓦 A γ p ≤
      germSigma (activeCompl A γ c p) h₀ ⊔ locPrefixSigma 𝓦 A γ p from le_sup_right)
      _ (measurableSet_live A γ p)
  refine hasOldChartIncrementLawOn_of_enlarged_marked_fwd hh₀ le_sup_left hg₀ hHarm₀ hK₀
    hpre' hpre' hKm (Eventually.of_forall hKreg) hKloc hKm
    (Eventually.of_forall hKreg) hKloc hInfo
    (E := Set.univ) MeasurableSet.univ MeasurableSet.univ (fun _ _ => rfl) rfl hG
    (fun ω hω => isConformal_relChart_of_driven (hγ ω hω.1) hω.2 (hc ω hω.1)) hfwd
    (fun ω hω => (H_diff_activeCompl_eq_relChart_dom hω.1 hω.2 (hγ ω hω.1)
      (hc ω hω.1)).symm)
    (fun ω _ => (hBreg ω).2) (fun ω _ => (hKreg ω).2)
    (fun ω _ => sdiff_subset_sdiff_right (PhaseCont.activeCompl_mono hpq ω))
    (fun ω hω => ⟨hω.1, lt_of_le_of_lt (by exact_mod_cast hpq) hω.2⟩)
    (subset_univ _) (fun ω hω =>
      (H_diff_activeCompl_eq_relChart_dom hω.1 hω.2 (hγ ω hω.1) (hc ω hω.1)).symm)

end InteractingSLE.Sec7.R5Out
