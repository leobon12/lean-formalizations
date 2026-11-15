/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux41OOInfFaces

/-!
# Mapped gaps of a pocket with two outer arms opening at the flow seed

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7, Aux. lemma 41 at the flow seed for pockets with two outer arms).

§5.4: "In the outer–outer case neither endpoint can be on an open side, so both are the same available pocket
endpoint." With both arms collared (`OuterIn.hasExteriorCollar_cfArc{R,L}Inf`) and Aux. 42, every physical boundary
contact during a gap is the entrance `y₀` (`contact_eq_seed_of_two_collars`), which was visited at the entrance time.
So every gap starts at an *old* point, and PROVE-R7-GAPEQ's old-start argument (an earlier chart after the two attained
last-visit parameters, `R7InfinityGap.exists_earlier_chart_lastVisits`; constancy of both outer attachments from the
collars, `R7InfinityGap.outer_attachConstInf_of_collars`; the compact gate face) proves mapped and physical equality
(`gap_eq_of_current_arms_old`, the old branch of `R7InfinityGap.gap_eq_of_current_arms`, which is the only branch that
does not use a reverse-visited arm). Generic: `gap_eq_of_two_collars`; actual: `gap_eq_outerOuterInf`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEq R7InfinityChart R7InfinityGap

section Generic

variable {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ} {C F K : Set ℂ} {τ : ℝ}

/-- **With both arms collared, every boundary contact during a gap is the entrance.** -/
theorem contact_eq_seed_of_two_collars {a b t : ℝ}
    (hC : IsCfPocketInf C A₁ A₂) (hη : ContinuousOn η (Ici 0))
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (houter₁ : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₁ v))
    (houter₂ : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₂ v))
    (ha : 0 ≤ a) (hab : a < b) (hgap : ∀ u ∈ Icc a b, η u ∉ C)
    (ht : t ∈ Icc a b) (htcl : η t ∈ closure C) : η t = A₁ 0 := by
  have hfr : η t ∈ frontier C := by
    rw [hC.isOpen.frontier_eq]
    exact ⟨htcl, hgap t ht⟩
  rcases hC.frontier_eq ▸ hfr with ⟨v, hv, he⟩ | ⟨v, hv, he⟩
  · rcases eq_or_lt_of_le (show 0 ≤ v from hv) with hv0 | hv0
    · rw [← he, ← hv0]
    · obtain ⟨U, hU, hpU, hcov⟩ := houter₁ v hv0
      rw [he] at hpU
      exact False.elim (not_mem_collar_at_gap hη h42 havoid ha hab hgap ht hU hcov hpU)
  · rcases eq_or_lt_of_le (show 0 ≤ v from hv) with hv0 | hv0
    · rw [← he, ← hv0, hC.seed]
    · obtain ⟨U, hU, hpU, hcov⟩ := houter₂ v hv0
      rw [he] at hpU
      exact False.elim (not_mem_collar_at_gap hη h42 havoid ha hab hgap ht hU hcov hpU)

/-- **The old-start branch of `R7InfinityGap.gap_eq_of_current_arms`** (no reverse-visited arm): in a chart `r` after
the two attained last-visit parameters, with both attachments constant on the gap and the gap start a limit of visits
after `r`, the gap has equal mapped and physical endpoints. -/
theorem gap_eq_of_current_arms_old {s r a b : ℝ} (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hab : a < b) (hτ : η τ = A₁ 0)
    (hAC₁ : BarrierAttachConstInf η C A₁ τ) (hAC₂ : BarrierAttachConstInf η C A₂ τ)
    (he₁ : lastVisit (fun t => η '' Icc 0 t) A₁ r = lastVisit (fun t => η '' Icc 0 t) A₁ a)
    (he₂ : lastVisit (fun t => η '' Icc 0 t) A₂ r = lastVisit (fun t => η '' Icc 0 t) A₂ a)
    (hfaces : ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η A₁ r p q₁ b₁ → IsLastVisitArm W η A₂ r p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 r (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) C ∧
      ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
        psiMap p (trMap W r t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)))
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr := hτ0.trans hτr
  obtain ⟨q₁, q₂, harcs⟩ := exists_pocket_compact_arms hC hη hW hW0 hτ0 hτr hτ
  have hδc : ContinuousOn (fun t => trMap W r t 0) (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun _ ht => hra.trans ht.1
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hδc).isBounded.exists_norm_le
  let p := min (min q₁ q₂) (-|B|) - 1
  have hp : p < min q₁ q₂ := (sub_one_lt _).trans_le (min_le_left _ _)
  have hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p := by
    intro t ht he
    have hsmall := hB _ ⟨t, ht, rfl⟩
    change ‖trMap W r t 0‖ ≤ B at hsmall
    rw [he, norm_real, Real.norm_eq_abs] at hsmall
    have hple : p ≤ -|B| - 1 := sub_le_sub_right (min_le_right _ _) 1
    have hpneg : p < 0 := by linarith only [hple, abs_nonneg B]
    rw [abs_of_neg hpneg] at hsmall
    linarith only [hsmall, hple, le_abs_self B]
  obtain ⟨b₁, b₂, hb₁, hb₂, hdisj⟩ := harcs p hp
  have hpq₁ := hp.trans_le (min_le_left _ _)
  have hpq₂ := hp.trans_le (min_le_right _ _)
  obtain ⟨hΓ, hΓH⟩ := compactBoundary_jordan
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₁)))
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₂)))
    hb₁.1 hb₂.1 hb₁.2.1 hb₂.2.1 hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hdisj
  obtain ⟨hFC, h11⟩ := hfaces p q₁ q₂ b₁ b₂ hb₁ hb₂ hp hΓ hΓH
  have hy₁ : A₁ 0 ∈ η '' Icc 0 r := ⟨τ, ⟨hτ0, hτr⟩, hτ⟩
  have hy₂ : A₂ 0 ∈ η '' Icc 0 r := hC.seed ▸ hy₁
  obtain ⟨hu₁, -, hD₁⟩ := lastVisit_tail_domain hη hr hC.cont₁ hC.tendsto₁ hC.mem_H₁ hy₁
  obtain ⟨hu₂, -, hD₂⟩ := lastVisit_tail_domain hη hr hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  have hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₁ r),
      η t ≠ A₁ v := fun t ht v hv => avoid_tail_of_attachment_const hη.2.1 hC.tendsto₁
        hAC₁ (hτr.trans hra) he₁ hgap t ht (hr.trans (hra.trans ht.1)) v (hu₁.trans hv.le) hv
  have hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₂ r),
      η t ≠ A₂ v := fun t ht v hv => avoid_tail_of_attachment_const hη.2.1 hC.tendsto₂
        hAC₂ (hτr.trans hra) he₂ hgap t ht (hr.trans (hra.trans ht.1)) v (hu₂.trans hv.le) hv
  have heq := ownFuture_gap_eq_of_compact_face hη hW hW0 hr hC.isOpen hra hab hb₁ hb₂ hp
    hdisj hD₁ hD₂ hFC h11 hδp hgap hunv₁ hunv₂ (Or.inr ha) hb
  exact ownFuture_and_trace_eq hη hW hW0 hs hsr hra (hra.trans hab.le) heq

/-- **Every gap of an infinite pocket with two collared arms has equal mapped and physical endpoints** in each earlier
chart (the two-outer counterpart of `R7InfinityGap.gap_eq_of_selected_faces`; every gap start is old). -/
theorem gap_eq_of_two_collars (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = A₁ 0)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (houter₁ : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₁ v))
    (houter₂ : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₂ v))
    (hfaces : ∀ r, τ ≤ r → ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η A₁ r p q₁ b₁ → IsLastVisitArm W η A₂ r p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 r (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) C ∧
      ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
        psiMap p (trMap W r t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)))
    {s a b : ℝ} (hτs : τ ≤ s) (hsa : s < a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | τ < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hτa := hτs.trans_lt hsa
  have hs := hτ0.trans hτs
  have hAC₁ := outer_attachConstInf_of_collars hη.2.1 hC.cont₁ hC.tendsto₁ hτ0 hτ h42 havoid houter₁
  have hAC₂ := outer_attachConstInf_of_collars hη.2.1 hC.cont₂ hC.tendsto₂ hτ0
    (hτ.trans hC.seed.symm) h42 havoid houter₂
  have hy := contact_eq_seed_of_two_collars hC hη.2.1 h42 havoid houter₁ houter₂
    (hτ0.trans hτa.le) hab hgap ⟨le_rfl, hab.le⟩ (mem_closure_of_visits hη.2.1 hτ0 ha)
  have hold : η a ∈ η '' Ico 0 a := ⟨τ, ⟨hτ0, hτa⟩, hτ.trans hy.symm⟩
  obtain ⟨r, hτr, hsr, hra, he₁, he₂⟩ := exists_earlier_chart_lastVisits hη.2.1
    hC.cont₁ hC.cont₂ hC.tendsto₁ hC.tendsto₂ hτ0 hτa hsa hτ (hτ.trans hC.seed.symm) hold
  exact gap_eq_of_current_arms_old hC hη hW hW0 hτ0 hτr hs hsr hra.le hab hτ hAC₁ hAC₂ he₁ he₂
    (hfaces r hτr) hgap (R7GapEqGeo.mem_closure_visits_after hra ha)
    (R7GapEqGeo.mem_closure_visits_after (hra.trans hab) hb)

end Generic

section Actual

variable {R L M₁ M₂ : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Every gap of an actual two-outer pocket opening at the flow seed has equal mapped and physical endpoints** in
each chart after the entrance time. -/
theorem gap_eq_outerOuterInf
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
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    {s a b : ℝ} (hτs : τ ≤ s) (hsa : s < a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ cfPocket R L r)
    (ha : a ∈ closure {t | τ < t ∧ η t ∈ cfPocket R L r})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ cfPocket R L r}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hC := h.isCfPocketInf h0
  have havoidB : ∀ t, 0 ≤ t →
      η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) := fun t ht hm => by
    rcases hm with hm | hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm
  have hK : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier (cfPocket R L r) := by
    rw [hC.frontier_eq]
    exact OuterIn.no_interval_frontier_inf hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hη.2.1 h42
  exact gap_eq_of_two_collars hC hη hW hW0 hτ0 hτ hK havoidB
    (fun v hv => OuterIn.hasExteriorCollar_cfArcRInf h h0
      (R7FaceSelect.changePocket_subset_left_of_order h hO₁)
      ((R7FaceSelect.right_exterior_subset hO₁).trans subset_union_left) Subset.rfl hv)
    (fun v hv => OuterIn.hasExteriorCollar_cfArcLInf h h0
      (R7FaceSelect.changePocket_subset_right_of_order h hO₂)
      ((R7FaceSelect.left_exterior_subset hO₂).trans subset_union_right) Subset.rfl hv)
    (current_faces_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη hW hW0
      hτ0 hτ hrev₁ hrev₂ havoid) hτs hsa hab hgap ha hb

end Actual

end InteractingSLE.Sec7.Aux41OO
