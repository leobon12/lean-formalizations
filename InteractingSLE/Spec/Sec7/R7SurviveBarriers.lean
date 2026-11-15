/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7SurviveComponents
import InteractingSLE.Spec.Sec7.R7LocalFaceActual

/-!
# Target adherence from reverse-visited barriers

PROVE-R7-GAPEQ. An allowed component either meets the forbidden frontier or exits the
bounded pocket inside the ambient domain. Both points lie on a surviving barrier prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec7.R7Survive

open Sec6

/-- If a point of a reverse-visited arc survives, its entire preceding prefix survives.
The endpoint at parameter one is already visited, so the prefix stays in the half-plane. -/
theorem reverse_prefix_domain {W : ℝ → ℝ} {η A : ℝ → ℂ} {s v : ℝ}
    (hη : IsLoewnerTrace W η) (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Icc 0 1)) (hAH : ∀ w ∈ Ico (0 : ℝ) 1, A w ∈ H)
    (hrev : R16.IsReverseVisitOrder A fun t => η '' Icc 0 t)
    (hxD : A 0 ∈ H \ fwdHull W s) (hy : A 1 ∈ η '' Icc 0 s)
    (hv : v ∈ Icc (0 : ℝ) 1) (hvD : A v ∈ H \ fwdHull W s) :
    A '' Icc 0 v ⊆ H \ fwdHull W s := by
  have hvnot : A v ∉ η '' Icc 0 s := fun hvis => notMem_domain_of_mem_trace hη hs hvis hvD
  have hv1 : v < 1 := lt_of_le_of_ne hv.2 fun he => hvnot (he.symm ▸ hy)
  have hsub : Icc 0 v ⊆ Icc (0 : ℝ) 1 := fun _ hw => ⟨hw.1, hw.2.trans hv.2⟩
  apply subset_domain_of_isPreconnected hη hs (isPreconnected_Icc.image _ (hAc.mono hsub))
    (by rintro _ ⟨w, hw, rfl⟩; exact hAH w ⟨hw.1, hw.2.trans_lt hv1⟩) ?_
    ⟨0, ⟨le_rfl, hv.1⟩, rfl⟩ hxD
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨w, hw, rfl⟩ hvis
  exact hvnot (hrev s w (hsub hw) v hv hw.2 hvis)

/-- A bounded pocket's allowed surviving components adhere to the target when every
surviving barrier point connects to it through the surviving closed pocket. -/
theorem target_adherence_of_prefixes {C D F K : Set ℂ} {x z : ℂ}
    (hCo : IsOpen C) (hCb : IsBounded C) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDb : ¬ IsBounded D)
    (hloc : ∀ p ∈ closure C, IsLocConnWithin C p) (hFo : IsOpen F)
    (hfr : frontier C ⊆ F ∪ K) (hFfr : closure C ∩ frontier F ∩ D ⊆ K)
    (hprefix : ∀ p ∈ K ∩ D, ∃ S : Set ℂ, IsPreconnected S ∧
      S ⊆ closure C ∩ D ∧ x ∈ S ∧ p ∈ S)
    (hz : z ∈ C ∩ D) (hzF : z ∉ F) :
    x ∈ closure (connectedComponentIn (C ∩ D) z) := by
  let Q := connectedComponentIn (C ∩ D) z
  have hzQ : z ∈ Q := mem_connectedComponentIn hz
  have hQsub : Q ⊆ C ∩ D := connectedComponentIn_subset _ _
  have hex : ∃ p ∈ K ∩ D, p ∈ closure Q := by
    by_cases hmeet : (Q ∩ F).Nonempty
    · have hn : ¬ Disjoint Q (frontier F) := by
        intro hd
        exact hzF (subset_of_isPreconnected_of_disjoint_frontier
          isPreconnected_connectedComponentIn hFo hmeet hd hzQ)
      obtain ⟨p, hpQ, hpfr⟩ := Set.not_disjoint_iff_nonempty_inter.1 hn
      have hp := hQsub hpQ
      exact ⟨p, ⟨hFfr ⟨⟨subset_closure hp.1, hpfr⟩, hp.2⟩, hp.2⟩, subset_closure hpQ⟩
    · have hd : Disjoint Q F := Set.disjoint_iff_inter_eq_empty.2
        (Set.not_nonempty_iff_eq_empty.1 hmeet)
      obtain ⟨p, hp, hpQ⟩ := exists_frontier_adherent hCo hCb hDo hDc hDb hz
      have hpF : p ∉ F := fun hpF => Set.disjoint_left.1 (hd.closure_left hFo) hpQ hpF
      exact ⟨p, ⟨(hfr hp.1).resolve_left hpF, hp.2⟩, hpQ⟩
  obtain ⟨p, hp, hpQ⟩ := hex
  obtain ⟨S, hS, hSsub, hxS, hpS⟩ := hprefix p hp
  exact subset_closure_component hDo hloc hS hSsub ⟨p, hpS, hpQ⟩ hxS

/-- The two reverse-visited barrier arcs suffice for physical target adherence.
Neither global connectedness of the surviving pocket nor absence of forbidden bulges is
required. -/
theorem target_adherence_of_barriers {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C F : Set ℂ} {s : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hCo : IsOpen C) (hCb : IsBounded C)
    (hloc : ∀ p ∈ closure C, IsLocConnWithin C p) (hFo : IsOpen F)
    (hAc₁ : ContinuousOn A₁ (Icc 0 1)) (hAc₂ : ContinuousOn A₂ (Icc 0 1))
    (hAH₁ : ∀ w ∈ Ico (0 : ℝ) 1, A₁ w ∈ H)
    (hAH₂ : ∀ w ∈ Ico (0 : ℝ) 1, A₂ w ∈ H)
    (hAcl₁ : A₁ '' Icc 0 1 ⊆ closure C) (hAcl₂ : A₂ '' Icc 0 1 ⊆ closure C)
    (hrev₁ : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (hrev₂ : R16.IsReverseVisitOrder A₂ fun t => η '' Icc 0 t)
    (hj : A₂ 0 = A₁ 0) (hxD : A₁ 0 ∈ H \ fwdHull W s)
    (hy₁ : A₁ 1 ∈ η '' Icc 0 s) (hy₂ : A₂ 1 ∈ η '' Icc 0 s)
    (hfr : frontier C ⊆ F ∪ (A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1))
    (hFfr : closure C ∩ frontier F ∩ H ⊆ A₁ '' Icc 0 1 ∪ A₂ '' Icc 0 1) :
    ∀ z ∈ C ∩ (H \ fwdHull W s), z ∉ F →
      A₁ 0 ∈ closure (connectedComponentIn (C ∩ (H \ fwdHull W s)) z) := by
  intro z hz hzF
  refine target_adherence_of_prefixes hCo hCb
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs)
    (QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 hs)
    (not_isBounded_domain hη hs) hloc hFo hfr
    (fun _ hp => hFfr ⟨hp.1, hp.2.1⟩) ?_ hz hzF
  rintro p ⟨hp, hpD⟩
  rcases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · refine ⟨A₁ '' Icc 0 v, isPreconnected_Icc.image _ (hAc₁.mono (Icc_subset_Icc_right hv.2)),
      ?_, ⟨0, ⟨le_rfl, hv.1⟩, rfl⟩, ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩⟩
    exact fun q hq => ⟨hAcl₁ (image_mono (Icc_subset_Icc_right hv.2) hq),
      reverse_prefix_domain hη hs hAc₁ hAH₁ hrev₁ hxD hy₁ hv hpD hq⟩
  · refine ⟨A₂ '' Icc 0 v, isPreconnected_Icc.image _ (hAc₂.mono (Icc_subset_Icc_right hv.2)),
      ?_, ⟨0, ⟨le_rfl, hv.1⟩, hj⟩, ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩⟩
    exact fun q hq => ⟨hAcl₂ (image_mono (Icc_subset_Icc_right hv.2) hq),
      reverse_prefix_domain hη hs hAc₂ hAH₂ hrev₂ (hj ▸ hxD) hy₂ hv hpD hq⟩

end InteractingSLE.Sec7.R7Survive
