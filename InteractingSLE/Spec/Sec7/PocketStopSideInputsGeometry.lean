/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCoverGeometry
import InteractingSLE.Spec.Sec7.Aux37Witness
import InteractingSLE.Spec.Sec7.CounterflowProb2Hull

/-!
# Finite-time inverse landings and separation inside the pocket

PROVE-STRIPSYS38. A traversal with local drivers has an inverse boundary extension
at every live capacity time. Composing it with an incoming pocket inverse extension
gives the physical landing. The latter extension must still be supplied for the
chosen Jordan coordinate, including the exclusion of its real or infinite corners.

Only separation inside the pocket is needed when the pocket exterior is filled in
both reference sets. Aux. 37's no-visit identity proves this for ranges. Passing
from ranges to filled hulls is a separate planar obligation, not an application of
that identity. A connected pocket avoiding a whole prefix is treated below using
the existing connected-component criterion for filling.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop PocketStopField

/-- Finite-time Carathéodory extension from a continuous generating prefix. The
path need not have been parametrized by half-plane capacity. -/
theorem exists_inverse_extension_of_filling {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ≥0} {η : ℝ → ℂ} {s : ℝ}
    (hη : ContinuousOn η (Icc 0 s))
    (hfill : fwdHull W q = fillH (η '' Icc 0 s)) :
    ∃ F : ℂ → ℂ, EqOn F (fwdMapInv W q) H ∧ ContinuousOn F Hbar ∧
      MapsTo F Hbar Hbar := by
  let ηH := fun t => clipH (η t)
  have hηH : ContinuousOn ηH (Icc 0 s) := continuous_clipH.comp_continuousOn hη
  have hfillH : fillH (ηH '' Icc 0 s) = fwdHull W q := by
    rw [hfill]
    apply fillH_congr
    rw [(isCompact_Icc.image_of_continuousOn hηH).isClosed.closure_eq,
      (isCompact_Icc.image_of_continuousOn hη).isClosed.closure_eq]
    change (clipH ∘ η) '' Icc 0 s ∩ H = η '' Icc 0 s ∩ H
    rw [image_comp, image_clipH_inter_H]
  have hconf : SupercriticalConformalCovariance.IsConformalBijection
      (fwdMapInv W q) H (H \ fillH (ηH '' Icc 0 s)) := by
    rw [hfillH]
    exact isConformalBijection_fwdMapInv hW hW0 q.coe_nonneg
  obtain ⟨F, he, hc, -, -⟩ := exists_continuousOn_extension_of_path_of_tendsto hηH
    (fun _ _ => clipH_mem_Hbar _) hconf (tendsto_fwdMapInv_cobounded hW hW0 q.coe_nonneg)
  refine ⟨F, he, hc, fun x hx => ?_⟩
  have hxcl : x ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hx
  have : NeBot (𝓝[H] x) := mem_closure_iff_nhdsWithin_neBot.1 hxcl
  apply QuantumZipper.isClosed_Hbar.mem_of_tendsto
    (((hc x hx).mono QuantumZipper.H_subset_Hbar).tendsto)
  exact eventually_nhdsWithin_of_forall fun y hy =>
    he hy ▸ QuantumZipper.H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)

/-- The relative inverse has a continuous boundary extension once the incoming
pocket inverse has one. The traversal's own extension is proved from its local
drivers and its continuous prefixes. -/
theorem exists_relative_inverse_extension {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) {E : ℂ → ℂ}
    (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) :
    ∃ F : ℂ → ℂ, EqOn F (relChart c γ q ω).2.1 H ∧ ContinuousOn F Hbar ∧
      MapsTo F Hbar (E '' Hbar) := by
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (γ ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hfill : fwdHull W q = fillH (γ ω '' Icc 0 (capInv (γ ω) q)) := by
    rw [← fwdHull_eq_of_eqOn q.coe_nonneg hqq' hWeq]
    exact hγ.fwdHull_segDriver q.coe_nonneg hq'
  obtain ⟨F, hF, hFc, hFH⟩ := exists_inverse_extension_of_filling hW hW0
    (hγ.continuousOn.mono Icc_subset_Ici_self) hfill
  refine ⟨E ∘ F, fun y hy => ?_, hEc.comp hFc hFH, fun x hx => ⟨F x, hFH hx, rfl⟩⟩
  rw [hrel]
  change E (F y) = (c ω).2.1 (fwdMapInv W q y)
  rw [hF hy, hE (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)]

/-- Physical finite interior landings, when the incoming inverse extension takes
the closed half-plane into `H`. For a pocket meeting the real boundary the corner
exclusion must instead be checked at the selected boundary points. -/
theorem exists_relative_inverse_landing {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) {E : ℂ → ℂ}
    (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) (hEH : MapsTo E Hbar H) :
    ∀ ξ : ℝ, ∃ p ∈ H, Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
  obtain ⟨F, hF, hFc, hFH⟩ := exists_relative_inverse_extension hγ hq hE hEc
  intro ξ
  have hξ : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨p, hp, he⟩ := hFH hξ
  refine ⟨F ξ, he ▸ hEH hp, ?_⟩
  exact (((hFc _ hξ).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
    (eventually_nhdsWithin_of_forall fun _ hy => hF hy)

/-- Without assuming the entire closed pocket lies in `H`, every finite relative
coordinate lands in the closed pocket. This also applies to pockets with a real
corner; the force-mark argument must exclude that corner at the selected points. -/
theorem exists_relative_inverse_landing_in_closure {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hc : (c ω).IsConformal) {E : ℂ → ℂ}
    (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) :
    ∀ ξ : ℝ, ∃ p ∈ closure ((c ω).dom : Set ℂ),
      Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
  obtain ⟨F, hF, hFc, -⟩ := exists_relative_inverse_extension hγ hq hE hEc
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  intro ξ
  have hξ : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hξcl : (ξ : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hξ
  have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 hξcl
  have ht := (((hFc _ hξ).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
    (eventually_nhdsWithin_of_forall fun _ hy => hF hy)
  refine ⟨F ξ, isClosed_closure.mem_of_tendsto ht ?_, ht⟩
  refine eventually_nhdsWithin_of_forall fun y hy => subset_closure ?_
  rw [hrel]
  exact hc.inv_mem_dom (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)

/-- Filling the common exterior only requires separation of the extra hull on
the pocket side of the physical boundary point. -/
theorem extHullSet_inter_ball_eq_of_pocket {C F G : Set ℂ} (hGF : G ⊆ F)
    {p : ℂ} {r : ℝ} (haway : Disjoint (C ∩ (F \ G)) (ball p r)) :
    PocketUnionPt.extHullSet C F ∩ ball p r = PocketUnionPt.extHullSet C G ∩ ball p r := by
  ext z
  constructor
  · rintro ⟨⟨hzH, hzC | hzF⟩, hzb⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzb⟩
    · by_cases hzC : z ∈ C
      · have hzG : z ∈ G := by
          by_contra hn
          exact disjoint_left.1 haway ⟨hzC, hzF, hn⟩ hzb
        exact ⟨⟨hzH, Or.inr hzG⟩, hzb⟩
      · exact ⟨⟨hzH, Or.inl hzC⟩, hzb⟩
  · rintro ⟨⟨hzH, hzC | hzG⟩, hzb⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzb⟩
    · exact ⟨⟨hzH, Or.inr (hGF hzG)⟩, hzb⟩

/-- Aux. 37's no-visit identity gives equality after filling the pocket exterior
for trace ranges. The statement deliberately uses ranges, not filled hulls. -/
theorem extHullSet_range_eq_of_avoid {η : ℝ → ℂ} {C : Set ℂ} {r s t : ℝ}
    (havoid : ∀ u ∈ Icc r s, η u ∉ C) (ht : t ∈ Icc r s) :
    PocketUnionPt.extHullSet C (η '' Icc 0 t) =
      PocketUnionPt.extHullSet C (η '' Icc 0 r) := by
  have he := Aux37Witness.inter_image_eq_of_avoid havoid ht
  ext z
  by_cases hzC : z ∈ C
  · have hz : z ∈ η '' Icc 0 t ↔ z ∈ η '' Icc 0 r := by
      exact ⟨fun h => (he ▸ (show z ∈ C ∩ η '' Icc 0 t from ⟨hzC, h⟩)).2,
        fun h => (he.symm ▸ (show z ∈ C ∩ η '' Icc 0 r from ⟨hzC, h⟩)).2⟩
    simp only [PocketUnionPt.extHullSet, mem_inter_iff, mem_union, mem_compl_iff,
      hzC, not_true_eq_false, false_or, hz]
  · simp only [PocketUnionPt.extHullSet, mem_inter_iff, mem_union, mem_compl_iff,
      hzC, not_false_eq_true, true_or]

/-- A connected pocket disjoint from a whole trace prefix misses its filled hull
as soon as one pocket point is still unfilled. -/
theorem disjoint_fwdHull_of_avoid_pocket {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {C : Set ℂ} (hC : IsPreconnected C) (hCH : C ⊆ H)
    {t : ℝ} (ht : 0 ≤ t) (havoid : Disjoint C (η '' Icc 0 t))
    {w : ℂ} (hw : w ∈ C) (hwn : w ∉ fwdHull W t) : Disjoint C (fwdHull W t) := by
  rw [hη.2.2 t ht] at hwn ⊢
  have hsub : C ⊆ H \ closure (η '' Icc 0 t) := by
    rw [(hη.isCompact_image t).isClosed.closure_eq]
    exact fun z hz => ⟨hCH hz, fun hm => disjoint_left.1 havoid hz hm⟩
  exact (Coding.subset_fillH_or_disjoint hC ⟨w, hw⟩ hsub).resolve_left
    (fun h => hwn (h hw))

end InteractingSLE.Sec7.PocketStopSide
