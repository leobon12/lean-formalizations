/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutKernel

/-!
# The enlarged-stop increment law in an incident reference component

PROVE-R5-OUTER, R88. Keep the existing current/enlarged record comparison
and the uniqueness of local-set means. Only the old chart domain changes:
it is a clopen component of the reference complement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketStopSide R5Enl

variable {Ω : Type*} {ℋ₀ ℋ₁ ℋK ℋ' ℋc : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω}

/-- Retained enlarged kernels imply the component increment law for every version of both means. -/
theorem hasOldChartIncrementLawOn_of_enlarged_component_kernels [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {B K K' : Ω → Set ℂ} {g₀ g₁ gK : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) (hg₁ : Measurable[ℋ₁] g₁)
    (hHarm₁ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₁ ω) (H \ K' ω))
    (hK₁ : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => H \ K' ω) fun ω => h ω - g₁ ω)
    (hKK : germSigma K h ≤ ℋK) (hℋK : ℋK ≤ mΩ) (hgK : Measurable[germSigma K h] gK)
    (hKKer : IsCondZeroBoundaryGFF P ℋK (fun ω => H \ K ω) fun ω => h ω - gK ω)
    {E : Set Ω} (hE : MeasurableSet[ℋK] E)
    (htrace : ∀ t, MeasurableSet[ℋK] (E ∩ t) ↔ MeasurableSet[ℋ₁] (E ∩ t))
    (hKE : ∀ᵐ ω ∂P, ω ∈ E → K ω = K' ω)
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ B ω)
    (hBo : ∀ ω ∈ G, IsOpen (H \ B ω))
    (hCut : ∀ ω ∈ G, IsOpen ((H \ B ω) \ (old ω).dom))
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ (old ω).dom)
    (hAdded : Measurable[ℋ₁, hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  intro gOld hgOld gNow hgNow
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  -- step 1: the two-step construction in the reference chart, conditioned on `G`
  have hL := hasOldChartIncrementLawOn_of_component_kernels (P := P) hInfo hℋ₁ hG hOld hdom hfwd
    (U := fun ω => H \ K' ω) hK'o hNest hh
    ((hg₀.mono hB₀ le_rfl).mono hInfo le_rfl) hg₁
    (by filter_upwards [hHarm₀] with ω hω hG'; exact IsHarmonicDistOn.mono hω (hOldDom ω hG'))
    (hHarm₁.mono fun ω hω _ => hω) (Uold := fun ω => H \ B ω)
    hBo (fun _ _ => sdiff_subset) hCut hOldDom hK₀ hK₁ hAdded hMG
    (current := curOn G fun ω => H \ K' ω)
    (fun ω hM => dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM))
      ((hNest ω (hMG hM)).trans (hOld ω (hMG hM)).dom_subset))
  -- step 3: every version of the means is the retained one, and the enlarged mean is the current one on `E`
  have hOldEq : gOld =ᵐ[P] g₀ := ae_eq_of_isLocalSetMean_of_retained hh hgOld hB₀ hℋ₀ hg₀ hK₀
  have hNowEq : gNow =ᵐ[P] gK := ae_eq_of_isLocalSetMean_of_retained hh hgNow hKK hℋK hgK hKKer
  have hEnl : ∀ᵐ ω ∂P, ω ∈ E → gK ω = g₁ ω :=
    ae_eq_of_isCondZeroBoundaryGFF_of_trace hℋK hℋ₁ hE htrace hh (hgK.mono hKK le_rfl) hg₁ hKKer hK₁
      (by filter_upwards [hKE] with ω hω hωE; rw [hω hωE])
  refine hL.congr_on ?_
  filter_upwards [hOldEq, hNowEq, hEnl, hKE] with ω e0 eN eE eK hM
  refine ⟨rfl, ?_, e0.symm, ?_⟩
  · rw [dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM)) ((hNest ω (hMG hM)).trans (hOld ω (hMG hM)).dom_subset),
      hcur ω hM, eK (hME hM)]
  · rw [eN, eE (hME hM)]

/-- The same law derived from the marked local-set laws and the current/enlarged record comparison. -/
theorem hasOldChartIncrementLawOn_of_enlarged_component_marked [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {B K K' : Ω → Set ℂ} {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hℋ' : ℋ' ≤ mΩ) (hℋc : ℋc ≤ mΩ)
    (hK'm : Measurable[mΩ, hittingSigma] K') (hK'reg : ∀ᵐ ω ∂P, K' ω ⊆ H ∧ IsOpen (H \ K' ω))
    (hK'loc : IsHistoryAvoidanceLocal ℋ' K' h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKreg : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hKloc : IsHistoryAvoidanceLocal ℋc K h P)
    (hInfo : ℋ₀ ≤ germSigma K' h ⊔ ℋ')
    {E : Set Ω} (hE : MeasurableSet[germSigma K h ⊔ ℋc] E) (hE' : MeasurableSet[germSigma K' h ⊔ ℋ'] E)
    (hKE : ∀ ω ∈ E, K ω = K' ω)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) ℋc = MeasurableSpace.comap ((↑) : E → Ω) ℋ')
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ B ω)
    (hBo : ∀ ω ∈ G, IsOpen (H \ B ω))
    (hCut : ∀ ω ∈ G, IsOpen ((H \ B ω) \ (old ω).dom))
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ (old ω).dom)
    (hAdded : Measurable[germSigma K' h ⊔ ℋ', hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  obtain ⟨g₁, hg₁, hHarm₁, hK₁⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hK'm hℋ' hK'loc hK'reg
  obtain ⟨gK, hgK, -, hKKer⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hKm hℋc hKloc hKreg
  exact hasOldChartIncrementLawOn_of_enlarged_component_kernels hh.measurable hB₀ hg₀ hHarm₀ hK₀ hInfo
    (sup_le (germSigma_le hK'm hh.measurable) hℋ') (hg₁.mono le_sup_left le_rfl) hHarm₁ hK₁ le_sup_left
    (sup_le (germSigma_le hKm hh.measurable) hℋc) hgK hKKer hE
    (measurableSet_inter_germSigma_sup_iff hKE hmarks hE hE')
    (Eventually.of_forall hKE) hG hOld hdom hfwd hOldDom hBo hCut hK'o hNest hAdded hMG hME hcur

end InteractingSLE.Sec7.R5Out
