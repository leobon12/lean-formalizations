import InteractingSLE.Spec.Sec5.GlueCondTopo
import InteractingSLE.Spec.Sec7.Lemma71EDomain

/-!
# The retained component at an original own-time restart

Packet PROVE-AUX61-R1; ruling R71. The entire old flow prefix is retained,
including every earlier excursion and contact. The base point selecting the
component is part of the retained history (in the application, it selects the
original right-target component). It is not chosen from the future curve.

The construction uses the existing simple-connectivity and measurable Riemann
mapping results. No boundary regularity of the old kissing set is required.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open LocalSets

/-- The open domain remaining after the retained hull and the entire own past
through the original time `r` have been removed. -/
def retainedDomain (K : Set ℂ) (η : ℝ → ℂ) (r : ℝ) : Set ℂ :=
  H \ (K ∪ η '' Icc 0 r)

/-- The component selected by the retained history's interior base point. -/
def restartComponent (K : Set ℂ) (η : ℝ → ℂ) (r : ℝ) (b : ℂ) : Set ℂ :=
  connectedComponentIn (retainedDomain K η r) b

/-- Unbounded complementary components are preserved on adjoining two retained
sets; no disjointness or independence assumption is needed. -/
theorem not_isBounded_lowerUnion_union {K A : Set ℂ}
    (hK : ∀ z ∈ lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion K) z))
    (hA : ∀ z ∈ lowerUnion A,
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion A) z)) :
    ∀ z ∈ lowerUnion (K ∪ A),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ∪ A)) z) := by
  intro z hz hb
  have hKsub : lowerUnion K ⊆ lowerUnion (K ∪ A) :=
    union_subset_union_left _ subset_union_left
  have hAsub : lowerUnion A ⊆ lowerUnion (K ∪ A) :=
    union_subset_union_left _ subset_union_right
  rcases hz with (hzK | hzA) | hzlow
  · exact hK z (Or.inl hzK) (hb.subset (connectedComponentIn_mono z hKsub))
  · exact hA z (Or.inl hzA) (hb.subset (connectedComponentIn_mono z hAsub))
  · exact hK z (Or.inr hzlow) (hb.subset (connectedComponentIn_mono z hKsub))

/-- A continuous finite prefix attached to the real boundary has no bounded
component after the lower half-plane is adjoined. -/
theorem not_isBounded_lowerUnion_prefix {η : ℝ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0) :
    ∀ z ∈ lowerUnion (η '' Icc 0 r),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (η '' Icc 0 r)) z) := by
  apply not_isBounded_of_isPreconnected_union_real
  have hreal : {z : ℂ | z.im = 0} = range (fun x : ℝ => (x : ℂ)) := by
    ext z
    exact ⟨fun hz => ⟨z.re, Complex.ext rfl (by simpa using hz.symm)⟩,
      by rintro ⟨x, rfl⟩; exact ofReal_im x⟩
  refine (isPreconnected_Icc.image η hc).union 0
    ⟨0, ⟨le_rfl, hr⟩, h0⟩ (by simp only [mem_ofPred_eq, zero_im]) ?_
  rw [hreal]
  exact isPreconnected_range continuous_ofReal

/-- Openness of the retained domain. -/
theorem isOpen_retainedDomain {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ}
    (hK : IsOpen (H \ K)) (hc : ContinuousOn η (Icc 0 r)) :
    IsOpen (retainedDomain K η r) := by
  change IsOpen (H \ (K ∪ η '' Icc 0 r))
  rw [← sdiff_sdiff]
  exact hK.sdiff (isCompact_Icc.image_of_continuousOn hc).isClosed

/-- Every nonempty selected retained component is an open simply connected
domain. Earlier excursions stay in the removed set throughout. -/
theorem restartComponent_properties {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ}
    (hr : 0 ≤ r) (hKo : IsOpen (H \ K))
    (hKu : ∀ z ∈ lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion K) z))
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0)
    (hb : b ∈ retainedDomain K η r) :
    IsOpen (restartComponent K η r b) ∧ IsConnected (restartComponent K η r b) ∧
      IsSimplyConnected (restartComponent K η r b) ∧ restartComponent K η r b ⊆ H := by
  have ho := isOpen_retainedDomain hKo hc
  exact ⟨ho.connectedComponentIn, isConnected_connectedComponentIn_iff.2 hb,
    isSimplyConnected_connectedComponentIn_compl ho
      (not_isBounded_lowerUnion_union hKu (not_isBounded_lowerUnion_prefix hr hc h0)) hb,
    (connectedComponentIn_subset _ _).trans sdiff_subset⟩

/-- The entire pre-contact continuation lies in the selected component as soon
as its initial access is in that component. Injectivity excludes the entire own
past, rather than only its last excursion. -/
theorem image_preContact_subset_component {K : Set ℂ} {η : ℝ → ℂ} {r T : ℝ} {b : ℂ}
    (hr : 0 ≤ r) (hc : ContinuousOn η (Icc 0 T)) (hi : InjOn η (Icc 0 T))
    (hnew : MapsTo η (Ioo r T) (H \ K))
    (haccess : (η '' Ioo r T ∩ restartComponent K η r b).Nonempty) :
    η '' Ioo r T ⊆ restartComponent K η r b := by
  obtain ⟨z, hznew, hzC⟩ := haccess
  rw [restartComponent, connectedComponentIn_eq hzC]
  refine (isPreconnected_Ioo.image η (hc.mono ?_)).subset_connectedComponentIn hznew ?_
  · intro u hu
    exact ⟨hr.trans hu.1.le, hu.2.le⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨(hnew hu).1, ?_⟩
    rintro (hK | ⟨v, hv, hvu⟩)
    · exact (hnew hu).2 hK
    · have heq := hi ⟨hv.1, hv.2.trans (hu.1.trans hu.2).le⟩
        ⟨hr.trans hu.1.le, hu.2.le⟩ hvu
      exact (not_le.2 hu.1) (heq ▸ hv.2)

end InteractingSLE.Sec5.Aux61Restart
