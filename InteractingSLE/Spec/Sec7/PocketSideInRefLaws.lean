/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideEndLaws
import InteractingSLE.Spec.Sec7.PocketStopSideLimCover
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofCover

/-!
# Reference locality and means from raw stopped laws

PROVE-POCKET-SIDEIN. Reference sets are normalized at their own fixed relative
level, before selecting a later visit. A raw union law supplies their marked
locality. Open complements supply regularity, hence locality and actual means.
Filling a simply connected pocket preserves unbounded complementary components.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal Lemma71C PocketStop PocketStopField
  PocketUnionPt PocketCoupling

variable {Ω : Type*} {ℳ ℳ₁ ℳ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit mΩ in
/-- Regularity of a reference normalized on its own live event. -/
theorem liveExt_regular {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, IsOpen (H \ F ω)) (ω : Ω) :
    liveExt A γ C F q ω ⊆ H ∧ IsOpen (H \ liveExt A γ C F q ω) := by
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl]
    refine ⟨inter_subset_left, ?_⟩
    have he : H \ extHullSet (C ω) (F ω) = C ω ∩ (H \ F ω) := by
      ext z
      simp only [Set.mem_sdiff, extHullSet, mem_inter_iff, mem_union, mem_compl_iff]
      tauto
    rw [he]
    exact (hCo ω hl.1).inter (hFo ω hl.1)
  · rw [liveExt_of_not_live hl, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

/-- A raw reference law gives hitting measurability, locality and an actual
version of its mean. These conclusions are not separate source assumptions. -/
theorem referenceFacts_of_unionLaw
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hpre : locPrefixSigma ℳ A γ q ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, IsOpen (H \ F ω))
    (hRaw : PocketStopUnionLaw ℳ P A γ C F h q) :
    Measurable[mΩ, hittingSigma] (liveExt A γ C F q) ∧
      IsLocalSet (liveExt A γ C F q) h P ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A γ C F q) h P g := by
  obtain ⟨E, hEm, hEloc, hEq⟩ := hRaw
  have hLive := measurableSet_live (𝓦 := ℳ) A γ q
  have hm := measurable_liveExt (hpre _ hLive) hEm hEq
  have hloc := isHistoryAvoidanceLocal_liveExt hLive hEloc hEq
  have hlocal : IsLocalSet (liveExt A γ C F q) h P :=
    ((isLocalSet_tfae hh hm (Eventually.of_forall (liveExt_regular hCo hFo))).out 1 4).1
      hloc.isAvoidanceLocal
  exact ⟨hm, hlocal, IsLocalSet.exists_isLocalSetMean hh hm hlocal⟩

/-- The smaller-germ theorem enlarges the raw reference law before selecting
its mean; no exterior-enlarged law is an additional premise. -/
theorem referenceFacts_of_unionLaw_with_germ
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F E₀ : Ω → Set ℂ} {q : ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hpre : locPrefixSigma ℳ A γ q ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, IsOpen (H \ F ω))
    (hE₀ : Measurable[locPrefixSigma ℳ A γ q, hittingSigma] E₀)
    (hsub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      E₀ ω ∩ H ⊆ extHullSet (C ω) (F ω))
    (hRaw : PocketStopUnionLaw ℳ P A γ C F h q) :
    PocketStopUnionLaw (ℳ ⊔ germSigma E₀ h) P A γ C F h q ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (liveExt A γ C F q) h P g := by
  have hRaw' := pocketStopUnionLaw_sup_germSigma hh hpre hE₀ hsub hRaw
  have hpre' : locPrefixSigma (ℳ ⊔ germSigma E₀ h) A γ q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le hpre (germSigma_le (hE₀.mono hpre le_rfl) hh.measurable)
  exact ⟨hRaw', (referenceFacts_of_unionLaw hh hpre' hCo hFo hRaw').2.2⟩

/-- The nested Proposition 3.9 applies directly to raw normalized reference
laws. Equal complementary-domain covariance forces equality of a test pairing;
no independence between the references is assumed. -/
theorem ae_reference_pairing_eq_of_covariance_eq
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F₁ F₂ : Ω → Set ℂ} {q₁ q₂ : ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hpre₁ : locPrefixSigma ℳ₁ A γ q₁ ≤ mΩ)
    (hpre₂ : locPrefixSigma ℳ₂ A γ q₂ ≤ mΩ)
    (hinfo : locPrefixSigma ℳ₁ A γ q₁ ≤ locPrefixSigma ℳ₂ A γ q₂)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo₁ : ∀ ω ∈ A, IsOpen (H \ F₁ ω))
    (hFo₂ : ∀ ω ∈ A, IsOpen (H \ F₂ ω))
    (hRaw₁ : PocketStopUnionLaw ℳ₁ P A γ C F₁ h q₁)
    (hRaw₂ : PocketStopUnionLaw ℳ₂ P A γ C F₂ h q₂)
    (hsub : ∀ᵐ ω ∂P, liveExt A γ C F₁ q₁ ω ⊆ liveExt A γ C F₂ q₂ ω)
    (hrecord : MeasurableSpace.comap (liveExt A γ C F₁ q₁) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (liveExt A γ C F₂ q₂) hittingSigma ⊔
        locPrefixSigma ℳ₂ A γ q₂) P)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (liveExt A γ C F₁ q₁) h P g₁)
    (hg₂ : IsLocalSetMean (liveExt A γ C F₂ q₂) h P g₂)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P,
      QuantumZipper.zeroGFFTestCov (H \ liveExt A γ C F₁ q₁ ω) φ φ =
        QuantumZipper.zeroGFFTestCov (H \ liveExt A γ C F₂ q₂ ω) φ φ →
      g₁ ω φ = g₂ ω φ := by
  obtain ⟨E₁, hE₁, hl₁, he₁⟩ := hRaw₁
  obtain ⟨E₂, hE₂, hl₂, he₂⟩ := hRaw₂
  have hL₁ := measurableSet_live (𝓦 := ℳ₁) A γ q₁
  have hL₂ := measurableSet_live (𝓦 := ℳ₂) A γ q₂
  exact FlatClockProof.IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hh
    (measurable_liveExt (hpre₁ _ hL₁) hE₁ he₁)
    (measurable_liveExt (hpre₂ _ hL₂) hE₂ he₂) hpre₁ hpre₂ hinfo
    (isHistoryAvoidanceLocal_liveExt hL₁ hl₁ he₁)
    (isHistoryAvoidanceLocal_liveExt hL₂ hl₂ he₂)
    (Eventually.of_forall (liveExt_regular hCo hFo₁))
    (Eventually.of_forall (liveExt_regular hCo hFo₂)) hsub hrecord hg₁ hg₂ φ

omit [IsProbabilityMeasure P] in
/-- A simply connected pocket and an ordinary hull reference supply the
unbounded-component input of the germ comparison. -/
theorem reference_unbounded_of_chart {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {C F : Ω → Set ℂ} {q : ℝ≥0} {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = C ω)
    (hF : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ lowerUnion (F ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (F ω)) z)) :
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (liveExt A γ C F q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (liveExt A γ C F q ω)) z) := by
  filter_upwards [hF] with ω hω
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl]
    have hCo : IsOpen (C ω) := hdom ω hl.1 ▸ (c ω).dom.isOpen
    have hsc : IsSimplyConnected (C ω) := hdom ω hl.1 ▸
      isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
        (hc ω hl.1).isConformalBijection isSimplyConnected_H
    exact not_isBounded_lowerUnion_extHullSet hCo hsc (hω hl.1)
  · rw [liveExt_of_not_live hl]
    have hH : lowerUnion H = univ := by
      ext z
      simp only [lowerUnion, H, mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact lt_or_ge 0 z.im
    rw [hH]
    intro z _
    rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    exact NormedSpace.unbounded_univ ℝ ℂ

end InteractingSLE.Sec7.PocketStopSide
