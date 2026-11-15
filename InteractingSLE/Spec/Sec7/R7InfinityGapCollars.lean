/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapVisits

/-!
# Outer collars give proper-arm attachment constancy

PROVE-R7-GAPEQ. No positive outer-arm point is visited on a pocket gap. Thus its
last-visit parameter stays constant, without an outer reverse-order hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 PocketJordan R7StopIn R7GapEq

/-- The outer arm's attachment constancy follows from exterior collars and the
no-interval assertion. No field comparison is needed on this arm. -/
theorem outer_attachConstInf_of_collars {η A : ℝ → ℂ} {C F K : Set ℂ} {τ : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hAc : ContinuousOn A (Ici 0))
    (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hτ0 : 0 ≤ τ) (hτ : η τ = A 0)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (houter : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A v)) :
    BarrierAttachConstInf η C A τ := by
  intro a b hτa hab hgap
  rcases eq_or_lt_of_le hab with hab | hab
  · rw [hab]
  have ha0 := hτ0.trans hτa
  have hcpt := fun t => isCompact_Icc.image_of_continuousOn
    (hη.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ ht => ht.1))
  have hy : A 0 ∈ η '' Icc 0 a := ⟨τ, ⟨hτ0, hτa⟩, hτ⟩
  have hu0 := le_lastVisit (R := fun t => η '' Icc 0 t) hAt (hcpt a).isBounded self_mem_Ici hy
  have hm := lastVisit_mem (R := fun t => η '' Icc 0 t) hAc hAt (hcpt b)
    ⟨0, self_mem_Ici, monotone_image_Icc hab.le hy⟩
  refine le_antisymm ?_ (lastVisit_mono hAt monotone_image_Icc hab.le (hcpt b).isBounded
    ⟨0, self_mem_Ici, hy⟩)
  by_contra hn
  have hu := lt_of_not_ge hn
  obtain ⟨t, ht, he⟩ := hm.2
  by_cases hta : t ≤ a
  · exact (not_le.2 hu) (le_lastVisit (R := fun t => η '' Icc 0 t) hAt (hcpt a).isBounded
      hm.1 ⟨t, ⟨ht.1, hta⟩, he⟩)
  · obtain ⟨U, hU, hpU, hcov⟩ := houter _ (hu0.trans_lt hu)
    rw [← he] at hpU
    exact not_mem_collar_at_gap hη h42 havoid ha0 hab hgap
      ⟨(not_le.1 hta).le, ht.2⟩ hU hcov hpU

/-- Every physical boundary contact on a gap lies on the contained arm; the
outer seed is the same contained seed, and positive outer parameters have collars. -/
theorem gap_contact_on_contained {η A₁ A₂ : ℝ → ℂ} {C F K : Set ℂ} {a b t : ℝ}
    (hC : IsCfPocketInf C A₁ A₂) (hη : ContinuousOn η (Ici 0))
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (houter : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₂ v))
    (ha : 0 ≤ a) (hab : a < b) (hgap : ∀ u ∈ Icc a b, η u ∉ C)
    (ht : t ∈ Icc a b) (htcl : η t ∈ closure C) : η t ∈ A₁ '' Ici 0 := by
  have hfr : η t ∈ frontier C := by
    rw [hC.isOpen.frontier_eq]
    exact ⟨htcl, hgap t ht⟩
  rcases hC.frontier_eq ▸ hfr with hfr | ⟨v, hv, he⟩
  · exact hfr
  · rcases eq_or_lt_of_le (show 0 ≤ v from hv) with hv0 | hv0
    · have he0 : A₂ 0 = η t := by simpa only [← hv0] using he
      exact ⟨0, self_mem_Ici, hC.seed.symm.trans he0⟩
    · obtain ⟨U, hU, hpU, hcov⟩ := houter v hv0
      rw [he] at hpU
      exact False.elim (not_mem_collar_at_gap hη h42 havoid ha hab hgap ht hU hcov hpU)

end InteractingSLE.Sec7.R7InfinityGap
