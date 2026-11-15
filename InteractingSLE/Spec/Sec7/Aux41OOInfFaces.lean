/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapFaces

/-!
# The compactified faces of a pocket with two outer arms opening at the flow seed

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7, Aux. lemma 41 at the flow seed for pockets with two outer arms).

At `rightLo = 0` the change pocket opens at the flow seed: in the counterflow chart it is unbounded, with the entrance
`y₀ = cfArcRInf 0` and two proper arms `cfArcRInf`, `cfArcLInf` to `∞`. PROVE-R7-GAPEQ's infinite-end face selection
(`R7InfinityAccess.infiniteFaceSides_of_exterior`, `R7InfinityGap.current_faces_leftOuter`) uses the reverse visit order
of the contained arm for the part of the frontier not on its last-visit arm, and the reverse contained arm together with
the clipped certified frontier for unbounded allowed components (`R7EndFace.allowedUnboundedComponents_leftOuter`).

For two outer arms (as in the bounded case, `Aux41OOFaces`): both arms adhere to their own exteriors, each with a real
access outside the compact gate boundary, so the compact inner face avoids the whole frontier
(`compact_face_frontier_of_two_exteriors`, `infiniteFaceSides_of_two_exteriors`); the two clipped certified frontiers at
infinity (`R7EndFace.exists_closed_midBarrierInf` for `β_R` and `β_L`) are the two reverse barriers for unbounded
allowed components (`allowedUnboundedComponents_outerOuter`). Together: `current_faces_outerOuter`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7InfinityChart R7InfinityAccess

section Generic

variable {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ} {C E₁ E₂ : Set ℂ} {τ s a q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ}

/-- **The compact inner face of a two-outer infinite pocket avoids the pocket frontier.** Each proper arm adheres to an
unbounded preconnected exterior avoided by the trace and outside the closed pocket, with a real access outside the
compact gate boundary; no reverse visit order is used. -/
theorem compact_face_frontier_of_two_exteriors (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂)
    (hE₁ : IsPreconnected E₁) (hE₁H : E₁ ⊆ H) (hE₁b : ¬ IsBounded E₁)
    (havoid₁ : Disjoint E₁ (η '' Icc 0 s)) (hE₁C : E₁ ⊆ (closure C)ᶜ)
    (houter₁ : A₁ '' Ici 0 ⊆ closure E₁)
    (hE₂ : IsPreconnected E₂) (hE₂H : E₂ ⊆ H) (hE₂b : ¬ IsBounded E₂)
    (havoid₂ : Disjoint E₂ (η '' Icc 0 s)) (hE₂C : E₂ ⊆ (closure C)ᶜ)
    (houter₂ : A₂ '' Ici 0 ⊆ closure E₂)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve
      (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)))
    (hΓH : compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) ⊆ Hbar)
    (haccess₁ : ∃ x : ℝ, (x : ℂ) ∈ closure (psiMap a '' (fwdMap W s '' E₁)) ∧
      (x : ℂ) ∉ compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹))
    (haccess₂ : ∃ x : ℝ, (x : ℂ) ∈ closure (psiMap a '' (fwdMap W s '' E₂)) ∧
      (x : ℂ) ∉ compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)) :
    ∀ ζ ∈ innerSide (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)),
      trMap W 0 s (psiMapInv a ζ) ∉ frontier C := by
  have hs := hτ0.trans hτs
  have hE₁D := subset_domain_of_not_isBounded hη hs hE₁ hE₁H havoid₁ hE₁b
  have hE₂D := subset_domain_of_not_isBounded hη hs hE₂ hE₂H havoid₂ hE₂b
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  have hE₁O := compact_lift_exterior_subset_outerSide hW hW0 hs hΓ hΓH hE₁ hE₁D
    (fun ζ hζ hζH hzE => hE₁C hzE (frontier_subset_closure (hbd ζ hζ hζH))) haccess₁
  have hE₂O := compact_lift_exterior_subset_outerSide hW hW0 hs hΓ hΓH hE₂ hE₂D
    (fun ζ hζ hζH hzE => hE₂C hzE (frontier_subset_closure (hbd ζ hζ hζH))) haccess₂
  have hcl₁ := compact_inner_not_mem_closure_exterior hW hW0 hs hΓ hΓH hE₁O
  have hcl₂ := compact_inner_not_mem_closure_exterior hW hW0 hs hΓ hΓH hE₂O
  intro ζ hζ hfr
  rw [hC.frontier_eq] at hfr
  rcases hfr with hz | hz
  · exact hcl₁ ζ hζ (houter₁ hz)
  · exact hcl₂ ζ hζ (houter₂ hz)

/-- **Both compact inner-side conditions for a two-outer infinite pocket** (`InfiniteFaceSides`), from the two
exteriors with their real accesses (as `R7InfinityAccess.infiniteFaceSides_of_exterior`, without a reverse-visited
arm). -/
theorem infiniteFaceSides_of_two_exteriors (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂)
    (ha : a < min q₁ q₂)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve
      (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)))
    (hΓH : compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) ⊆ Hbar)
    (hE₁ : IsPreconnected E₁) (hE₁H : E₁ ⊆ H) (hE₁b : ¬ IsBounded E₁)
    (havoid₁ : Disjoint E₁ (η '' Icc 0 s)) (hE₁C : E₁ ⊆ (closure C)ᶜ)
    (houter₁ : A₁ '' Ici 0 ⊆ closure E₁)
    (hreal₁ : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E₁) ∨ (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E₁))
    (hE₂ : IsPreconnected E₂) (hE₂H : E₂ ⊆ H) (hE₂b : ¬ IsBounded E₂)
    (havoid₂ : Disjoint E₂ (η '' Icc 0 s)) (hE₂C : E₂ ⊆ (closure C)ᶜ)
    (houter₂ : A₂ '' Ici 0 ⊆ closure E₂)
    (hreal₂ : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E₂) ∨ (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E₂))
    (hloc : ∀ z ∈ frontier C, z ∈ H → IsLocConnWithin (closure C)ᶜ z) :
    InfiniteFaceSides W C s a (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)) := by
  have hs := hτ0.trans hτs
  have hE₁D := subset_domain_of_not_isBounded hη hs hE₁ hE₁H havoid₁ hE₁b
  have hE₂D := subset_domain_of_not_isBounded hη hs hE₂ hE₂H havoid₂ hE₂b
  have haccess₁ := compact_access_of_real_lift hb₁ hb₂ ha
    (exists_real_lift_outside_interval hη hW hW0 hs hE₁D hreal₁ a (max q₁ q₂))
  have haccess₂ := compact_access_of_real_lift hb₁ hb₂ ha
    (exists_real_lift_outside_interval hη hW hW0 hs hE₂D hreal₂ a (max q₁ q₂))
  have hfr := compact_face_frontier_of_two_exteriors hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
    hE₁ hE₁H hE₁b havoid₁ hE₁C houter₁ hE₂ hE₂H hE₂b havoid₂ hE₂C houter₂ hΓ hΓH haccess₁ haccess₂
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  have hEO := compact_lift_exterior_subset_outerSide hW hW0 hs hΓ hΓH hE₂ hE₂D
    (fun ζ hζ hζH hzE => hE₂C hzE (frontier_subset_closure (hbd ζ hζ hζH))) haccess₂
  have hy₂ : A₂ 0 ∈ η '' Icc 0 s := hC.seed ▸ ⟨τ, ⟨hτ0, hτs⟩, hτ⟩
  obtain ⟨hu, -, hD⟩ := lastVisit_tail_domain hη hs hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  let v := lastVisit (fun t => η '' Icc 0 t) A₂ s + 1
  have huv : lastVisit (fun t => η '' Icc 0 t) A₂ s < v := lt_add_one _
  have hv : 0 < v := hu.trans_lt huv
  have hvD := hD v huv
  have hgH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hvD
  have hζH := (psiMap_mem_H_iff (fun he => not_mem_H_ofReal a (he ▸ hgH))).2 hgH
  have hζarm : psiMap a (fwdMap W s (A₂ v)) ∈ b₂ '' Ioo 0 1 :=
    hb₂.2.2.2.2.2.1 ▸ ⟨_, ⟨_, ⟨v, huv, rfl⟩, rfl⟩, rfl⟩
  have hζΓ : psiMap a (fwdMap W s (A₂ v)) ∈
      compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) :=
    Or.inl (Or.inr (image_mono Ioo_subset_Icc_self hζarm))
  have he : trMap W 0 s (psiMapInv a (psiMap a (fwdMap W s (A₂ v)))) = A₂ v := by
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs hvD]
  refine ⟨hfr, exists_compact_inner_pocket_of_exterior_access hη hW hW0 hs hC.isOpen
    hΓ hΓH hbd hfr hζΓ hζH ?_ ?_⟩
  · rw [he]
    exact hloc _ (hC.frontier_eq.symm ▸ Or.inr ⟨v, hv.le, rfl⟩) (hC.mem_H₂ v hv)
  · rw [he]
    exact mem_closure_compact_exterior_access (houter₂ ⟨v, hv.le, rfl⟩) hE₂D hE₂C hEO

end Generic

section Actual

variable {R L M₁ M₂ : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Every allowed surviving component of a two-outer infinite pocket is unbounded.** The forbidden set is
`m(E_R) ∪ m(E_L)`; the barriers are the clipped certified frontiers `β_R`, `β_L` at infinity. -/
theorem allowedUnboundedComponents_outerOuter
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) :
    R7EndFace.AllowedUnboundedComponents W (cfPocket R L r)
      (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) τ := by
  have hC := h.isCfPocketInf h0
  obtain ⟨B₁, hB₁c, hB₁t, hB₁H, hB₁cl, hB₁rev, hB₁0, hB₁mem⟩ :=
    R7EndFace.exists_closed_midBarrierInf h h0 hM₁ hO₁ hc₁R hc₁L hη.1 hrev₁
  obtain ⟨B₂, hB₂c, hB₂t, hB₂H, hB₂cl, hB₂rev, hB₂0, hB₂mem⟩ :=
    R7EndFace.exists_closed_midBarrierInf h h0 hM₂ hO₂ hc₂R hc₂L hη.1 hrev₂
  obtain ⟨hF₁o, hF₁fr⟩ := forbidden_right hM₁
  obtain ⟨hF₂o, hF₂fr⟩ := forbidden_left hM₂
  have hfr : frontier (cfPocket R L r) ⊆
      (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) ∪
        (B₁ '' Ici 0 ∪ B₂ '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases cfArcRInf_mem_of_outer h h0 houterR hB₁0 hB₁mem hv with hF | hB
      exacts [Or.inl (Or.inl hF), Or.inr (Or.inl hB)]
    · rcases cfArcLInf_mem_of_outer h h0 houterL hB₂0 hB₂mem hv with hF | hB
      exacts [Or.inl (Or.inr hF), Or.inr (Or.inr hB)]
  intro s hτs
  apply R7EndFace.unbounded_component_of_proper_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen
    (fun _ hp => R7EndFace.isLocConnWithin_cfPocket h hp) (hF₁o.union hF₂o) hB₁c hB₂c hB₁t hB₂t
    hB₁H hB₂H hB₁cl hB₂cl hB₁rev hB₂rev ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB₁0.symm⟩
    ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB₂0.symm⟩ hfr
  rintro z ⟨⟨hzc, hzf⟩, hzH⟩
  rcases frontier_union_subset _ _ hzf with ⟨hz1, -⟩ | ⟨-, hz2⟩
  · exact Or.inl (hB₁mem z hzc hzH (hF₁fr z hz1 hzH))
  · exact Or.inr (hB₂mem z hzc hzH (hF₂fr z hz2 hzH))

/-- **The compact inner-side conditions of an actual two-outer infinite pocket** (`InfiniteFaceSides`), for any
last-visit arms and any pole left of both gates: the walls' own exteriors `m(E(α_R))`, `m(E(α_L))` with their real
accesses (negative, resp. positive reals). -/
theorem infiniteFaceSides_outerOuter
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    {s p q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ} (hτs : τ ≤ s)
    (hb₁ : IsLastVisitArm W η (cfArcRInf R L r) s p q₁ b₁)
    (hb₂ : IsLastVisitArm W η (cfArcLInf R L r) s p q₂ b₂) (hp : p < min q₁ q₂)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)))
    (hΓH : compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar) :
    InfiniteFaceSides W (cfPocket R L r) s p (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) := by
  obtain ⟨hE₁, hE₁H, hE₁b, hE₁C, houter₁⟩ := right_outer_exterior_props h h0 hO₁
  obtain ⟨hE₂, hE₂H, hE₂b, hE₂C, houter₂⟩ := left_outer_exterior_props h h0 hO₂
  exact infiniteFaceSides_of_two_exteriors (h.isCfPocketInf h0) hη hW hW0 hτ0 hτs hτ hb₁ hb₂ hp hΓ hΓH
    hE₁ hE₁H hE₁b (Set.disjoint_left.2 (by
      rintro _ hz ⟨t, ht, rfl⟩
      exact notMem_image_negInv (fun hm => havoid t ht.1 (Or.inl hm))
        (R7FaceSelect.right_exterior_subset hO₁ hz)))
    hE₁C houter₁ (Or.inr fun x hx => negative_real_mem_closure_right_exterior h.right hx)
    hE₂ hE₂H hE₂b (Set.disjoint_left.2 (by
      rintro _ hz ⟨t, ht, rfl⟩
      exact notMem_image_negInv (fun hm => havoid t ht.1 (Or.inr hm))
        (R7FaceSelect.left_exterior_subset hO₂ hz)))
    hE₂C houter₂ (Or.inl fun x hx => positive_real_mem_closure_left_exterior h.left hx)
    (fun z hz hzH => OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz))

/-- **Every admissible compact face of a two-outer infinite pocket** has physical image in the pocket and confines the
active future visits (the two-outer counterpart of `R7InfinityGap.current_faces_leftOuter`). -/
theorem current_faces_outerOuter
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂)) :
    ∀ s, τ ≤ s → ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η (cfArcRInf R L r) s p q₁ b₁ →
      IsLastVisitArm W η (cfArcLInf R L r) s p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 s (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) (cfPocket R L r) ∧
      ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap p (trMap W s t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) := by
  intro s hτs p q₁ q₂ b₁ b₂ hb₁ hb₂ hp hΓ hΓH
  have hC := h.isCfPocketInf h0
  have hs := hτ0.trans hτs
  have havoidB : ∀ t, 0 ≤ t →
      η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) := fun t ht hm => by
    rcases hm with hm | hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm
  have hsides := infiniteFaceSides_outerOuter h h0 hO₁ hO₂ hη hW hW0 hτ0 hτ havoid hτs hb₁ hb₂ hp hΓ hΓH
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  obtain ⟨q, hchart⟩ := infiniteFaceChart_of_sides hη hW hW0 hs hC.isOpen hΓ hΓH
    (zero_mem_compactBoundary (b₂ := b₂) hb₁.2.2.2.1)
    (fun ζ hζ hζH hzC => (hC.isOpen.frontier_eq ▸ hbd ζ hζ hζH).2 hzC) hsides
  have hallowed := allowedUnboundedComponents_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L
    houterR houterL hη hW hW0 hτ0 hτ hrev₁ hrev₂
  refine ⟨?_, R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hchart
    (fun t ht => havoidB t (hs.trans ht))⟩
  apply mapsTo_iff_image_subset.2
  rw [hchart.2.2.2.2.2]
  exact (connectedComponentIn_subset _ _).trans inter_subset_left

end Actual

end InteractingSLE.Sec7.Aux41OO
