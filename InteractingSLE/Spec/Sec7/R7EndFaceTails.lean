/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceComponents
import InteractingSLE.Spec.Sec7.R7StopInMixedInf
import InteractingSLE.Spec.Sec6.DrivingSimple

/-!
# Surviving proper barrier tails

PROVE-R7-GAPEQ. Reverse visits and properness put every surviving barrier tail in
the ambient domain. These tails force every allowed pocket component to be unbounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec7.R7EndFace

open Sec6

/-- A surviving point on a proper reverse-visited barrier has a surviving unbounded
tail. This uses no assertion that the outer wall itself is reverse-visited. -/
theorem reverse_tail_domain {W : ℝ → ℝ} {η A : ℝ → ℂ} {s v : ℝ}
    (hη : IsLoewnerTrace W η) (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Ici 0)) (hAt : Tendsto (fun w => ‖A w‖) atTop atTop)
    (hAH : ∀ w ∈ Ioi (0 : ℝ), A w ∈ H)
    (hrev : IsReverseVisitOrderInf A fun t => η '' Icc 0 t)
    (hy : A 0 ∈ η '' Icc 0 s) (hv : 0 ≤ v) (hvD : A v ∈ H \ fwdHull W s) :
    IsPreconnected (A '' Ici v) ∧ ¬ IsBounded (A '' Ici v) ∧
      A '' Ici v ⊆ H \ fwdHull W s := by
  have hvnot : A v ∉ η '' Icc 0 s := fun hvis => notMem_domain_of_mem_trace hη hs hvis hvD
  have hv0 : 0 < v := lt_of_le_of_ne hv fun he => hvnot (he ▸ hy)
  have hpre : IsPreconnected (A '' Ici v) := isPreconnected_Ici.image _
    (hAc.mono (Ici_subset_Ici.2 hv))
  have hunb : ¬ IsBounded (A '' Ici v) :=
    not_isBounded_image_of_tendsto (tendsto_norm_atTop_iff_cobounded.1 hAt) (Ici_mem_atTop v)
  refine ⟨hpre, hunb, subset_domain_of_not_isBounded hη hs hpre ?_ ?_ hunb⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hAH w (hv0.trans_le hw)
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hvis
    exact hvnot (hrev s v hv w (hv.trans hw) hw hvis)

/-- Two proper reverse-visited barriers supply unbounded allowed components in the
infinite-end pocket. Forbidden surviving components may still be bounded. -/
theorem unbounded_component_of_proper_barriers {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C F : Set ℂ} {s : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hCo : IsOpen C) (hloc : ∀ p ∈ closure C, IsLocConnWithin C p) (hFo : IsOpen F)
    (hAc₁ : ContinuousOn A₁ (Ici 0)) (hAc₂ : ContinuousOn A₂ (Ici 0))
    (hAt₁ : Tendsto (fun w => ‖A₁ w‖) atTop atTop)
    (hAt₂ : Tendsto (fun w => ‖A₂ w‖) atTop atTop)
    (hAH₁ : ∀ w ∈ Ioi (0 : ℝ), A₁ w ∈ H) (hAH₂ : ∀ w ∈ Ioi (0 : ℝ), A₂ w ∈ H)
    (hAcl₁ : A₁ '' Ici 0 ⊆ closure C) (hAcl₂ : A₂ '' Ici 0 ⊆ closure C)
    (hrev₁ : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hrev₂ : IsReverseVisitOrderInf A₂ fun t => η '' Icc 0 t)
    (hy₁ : A₁ 0 ∈ η '' Icc 0 s) (hy₂ : A₂ 0 ∈ η '' Icc 0 s)
    (hfr : frontier C ⊆ F ∪ (A₁ '' Ici 0 ∪ A₂ '' Ici 0))
    (hFfr : closure C ∩ frontier F ∩ H ⊆ A₁ '' Ici 0 ∪ A₂ '' Ici 0) :
    ∀ z ∈ C ∩ (H \ fwdHull W s), z ∉ F →
      ¬ IsBounded (connectedComponentIn (C ∩ (H \ fwdHull W s)) z) := by
  intro z hz hzF
  refine unbounded_component_of_barrier_tails hCo
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs)
    (QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 hs)
    (not_isBounded_domain hη hs) hloc hFo hfr
    (fun _ hp => hFfr ⟨hp.1, hp.2.1⟩) ?_ hz hzF
  rintro p ⟨hp, hpD⟩
  rcases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · obtain ⟨hpre, hunb, hD⟩ := reverse_tail_domain hη hs hAc₁ hAt₁ hAH₁ hrev₁ hy₁ hv hpD
    exact ⟨A₁ '' Ici v, hpre, fun _ hw =>
      ⟨hAcl₁ (image_mono (Ici_subset_Ici.2 hv) hw), hD hw⟩, hunb, ⟨v, mem_Ici.2 le_rfl, rfl⟩⟩
  · obtain ⟨hpre, hunb, hD⟩ := reverse_tail_domain hη hs hAc₂ hAt₂ hAH₂ hrev₂ hy₂ hv hpD
    exact ⟨A₂ '' Ici v, hpre, fun _ hw =>
      ⟨hAcl₂ (image_mono (Ici_subset_Ici.2 hv) hw), hD hw⟩, hunb, ⟨v, mem_Ici.2 le_rfl, rfl⟩⟩

end InteractingSLE.Sec7.R7EndFace
