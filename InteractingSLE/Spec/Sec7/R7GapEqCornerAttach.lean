/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoGap
import InteractingSLE.Spec.Sec7.R7GapEqGeoMapped

/-!
# Outer attachment constancy and unvisited incoming prefixes

PROVE-R7-GAPEQ. The exterior collars exclude a new open-arm visit on a closed no-pocket
gap. Consequently the first-visit attachment is constant even for an outer arm, without
reverse visit order or continuity of that attachment. An unvisited prefix remains unvisited
on a gap once this attachment is constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn R7GapEq R7GapEqGeo

/-- **Outer attachment constancy from the proved exterior collars.** Neither reverse visit
order nor continuity of the outer attachment is a premise. A strict attachment decrease
would first visit an open side point during the gap, which its collar excludes. -/
theorem barrierAttachConst_of_outerCollars {η A : ℝ → ℂ} {C F K : Set ℂ} {τ σ : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hAc : ContinuousOn A (Icc 0 1))
    (hτ0 : 0 ≤ τ) (hτ : η τ = A 1) (hxf : A 0 ∉ η '' Ico 0 σ)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hcollar : ∀ v ∈ Ioo (0 : ℝ) 1, HasExteriorCollar C F K (A v)) :
    BarrierAttachConst η C A τ σ := by
  intro a b hτa hab hbσ hgap
  have hseen : ∀ t, a ≤ t → ∃ v ∈ Icc (0 : ℝ) 1, A v ∈ η '' Icc 0 t :=
    fun t ht => ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτa.trans ht⟩, hτ⟩
  have hmem : ∀ t, a ≤ t → firstVisit (fun s => η '' Icc 0 s) A t ∈ Icc (0 : ℝ) 1 ∧
      A (firstVisit (fun s => η '' Icc 0 s) A t) ∈ η '' Icc 0 t := fun t ht =>
    firstVisit_mem hAc
      (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed (hseen t ht)
  by_contra hne
  have hlt : firstVisit (fun s => η '' Icc 0 s) A b <
      firstVisit (fun s => η '' Icc 0 s) A a :=
    lt_of_le_of_ne (firstVisit_anti monotone_image_Icc hab (hseen a le_rfl)) hne
  have hab' : a < b := lt_of_le_of_ne hab fun he => by rw [he] at hlt; exact lt_irrefl _ hlt
  let v := firstVisit (fun s => η '' Icc 0 s) A b
  obtain ⟨c, hc, he⟩ := (hmem b hab).2
  have hac : a < c := by
    by_contra hn
    have hv := firstVisit_le (R := fun s => η '' Icc 0 s) (hmem b hab).1
      (show A v ∈ η '' Icc 0 a from ⟨c, ⟨hc.1, (not_lt.1 hn)⟩, he⟩)
    exact (not_le.2 hlt) hv
  have hv0 : 0 < v := lt_of_le_of_ne (hmem b hab).1.1 fun hv => by
    apply hxf
    exact ⟨c, ⟨hc.1, hc.2.trans_lt hbσ⟩, he.trans (congrArg A hv.symm)⟩
  have hv1 : v < 1 := hlt.trans_le (hmem a le_rfl).1.2
  obtain ⟨U, hU, hpU, hcov⟩ := hcollar v ⟨hv0, hv1⟩
  exact not_mem_collar_at_gap hη h42 havoid (hτ0.trans hτa) hab' hgap
    ⟨hac.le, hc.2⟩ hU hcov (he.symm ▸ hpU)

/-- An attachment constant across a gap excludes all physical contacts strictly before that
attachment. This uses the minimum property alone, so also applies to outer attachments. -/
theorem avoid_prefix_of_attachment_const {η A : ℝ → ℂ} {C : Set ℂ} {τ σ a b : ℝ}
    (hAC : BarrierAttachConst η C A τ σ) (hτa : τ ≤ a) (hbσ : b < σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) :
    ∀ t ∈ Icc a b, ∀ v ∈ Icc (0 : ℝ) 1,
      v < firstVisit (fun s => η '' Icc 0 s) A a → 0 ≤ t → η t ≠ A v := by
  intro t ht v hv hvu ht0 he
  have hconst := hAC a t hτa ht.1 (ht.2.trans_lt hbσ)
    (fun s hs => hgap s ⟨hs.1, hs.2.trans ht.2⟩)
  have hmin : firstVisit (fun s => η '' Icc 0 s) A t ≤ v :=
    firstVisit_le hv ⟨t, ⟨ht0, le_rfl⟩, he⟩
  rw [hconst] at hmin
  exact (not_le.2 hvu) hmin

end InteractingSLE.Sec7.R7GapEqCorner
