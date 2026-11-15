/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77RealTip
import InteractingSLE.Spec.Sec7.Lemma77Main

/-!
# Lemma 7.7: confinement at a real common first contact

Packet PROVE-LEMMA77-B (specification §7.2, Aux. lemmas 74–75, pp. 279–282, `source/spec/p241-288.md#aux-74`).

At a common first contact `w = α(a) = β(b) ∈ ℝ` of two good paths, with Lemma 7.6's conclusion at the rational
stops, no continuation point `α(v)`, `a < v`, lies off the joint unbounded domain `D` near `a`
(`false_of_notMem_of_real`). The argument splits on the second path's approach to `w`:

* the second prefix `β([0, b))` is trapped by `α([0, a])` (it arrives from inside the first path's hull; this
  includes `b = 0`): the unbounded domain of `α([0, a])` lies in `D`, and the continuation is in its closure
  (Aux. lemma 74, "every bounded component is already in the first path's filled hull");
* real touches of `β` accumulate at `b`: a continuation point `z ∈ ℍ` is in the unbounded domain of `β([0, s*])`
  (`s*` a late real touch) and, by the vertical ray, of the short tail `β([s*, b])`, hence of `β([0, b])` and of `K`
  — a contradiction without Lemma 7.6;
* `β` ends with a final excursion in `ℍ` outside the first hull: the forbidden first exit of Lemma 7.6 at rational
  stops `r > a`, `t < b` (`exists_not_firstExitBarrier_real`, Aux. lemma 74's witness); the late second path is in
  the unbounded domain of the frozen first prefix because the short onward arc `α([a, r])` sits in a small ball about
  the real point `w` and meets `α([0, a])` only at `w`.

`realContactConfinement` proves the proposition `RealContactConfinement` of `Lemma77Main.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart Foundations.ThetaCurve

variable {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ} {L : Set ℂ} {a b : ℝ≥0}

/-! ### Lemma 7.6's conclusion at rational stops -/

theorem firstExitBarrier_mono {a' b' : ℝ≥0} {ζ ζ' : ℝ≥0∞} (h : FirstExitBarrier α a' β ζ b' L)
    (hζ : ζ' ≤ ζ) : FirstExitBarrier α a' β ζ' b' L :=
  fun hd hadm e u v he => h hd hadm e u v (he.trans hζ)

/-- Lemma 7.6's conclusion at the truncated rational stops gives it at the rational stops inside shorter available
ranges. -/
theorem barrier_of_truncAt {ζ₁ ζ₂ : ℝ≥0∞} (hα : ζα ≤ ζ₁) (hβ : ζβ ≤ ζ₂)
    (hbar : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal) L) :
    ∀ q q' : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζα → (((q' : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζβ →
      FirstExitBarrier α (q : ℝ).toNNReal β ζβ (q' : ℝ).toNNReal L := fun q q' hq hq' => by
  have h := hbar q q'
  rw [truncAt_of_le (hq.trans hα), truncAt_of_le (hq'.trans hβ)] at h
  exact firstExitBarrier_mono h hβ

/-! ### The forbidden exit at a real corner -/

/-- **Aux. lemma 74's witness at a real contact.** Let `w = α(a) = β(b) ∈ ℝ` be a common first contact, let `β` end
with a final excursion `β((t₁, b)) ⊆ ℍ` outside the hull of `α([0, a])`, and let the continuation points `α(v) ∈ ℍ`,
`a < v ≤ v₁`, lie off the joint unbounded domain. Then Lemma 7.6's conclusion fails at a pair of rational stops. -/
theorem exists_not_firstExitBarrier_real (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hLc : IsCompact L) (hLpc : IsPreconnected L) (hLim : ∀ z ∈ L, z.im ≤ 0) (hxα : (xα : ℂ) ∈ L)
    (hxβ : (xβ : ℂ) ∈ L) (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H) {t₁ : ℝ≥0} (ht₁ : t₁ < b)
    (harch : ∀ t ∈ Ioo t₁ b, β t ∈ H) (hfree : ∀ t ∈ Ioo t₁ b, β t ∈ H \ fillH (α '' Icc 0 a))
    {v₁ : ℝ≥0} (hav₁ : a < v₁) (hv₁ : (v₁ : ℝ≥0∞) ≤ ζα)
    (hnot : ∀ v ∈ Ioc a v₁, α v ∈ H → α v ∉ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b)) :
    ∃ q q' : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζα ∧ (((q' : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζβ ∧
      ¬ FirstExitBarrier α (q : ℝ).toNNReal β ζβ (q' : ℝ).toNNReal L := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := id hfc
  have hw0 : (α a).im = 0 := IsPathGood.im_eq_zero hpα haζ hwR
  have haζ' : (a : ℝ≥0∞) < ζα := (ENNReal.coe_lt_coe.2 hav₁).trans_le hv₁
  -- a point of the final excursion, away from the contact
  obtain ⟨t₂, ht₁₂, ht₂b⟩ := exists_between ht₁
  have ht₂H : β t₂ ∈ H := harch t₂ ⟨ht₁₂, ht₂b⟩
  have ht₂ζ : (t₂ : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 ht₂b.le).trans hbζ
  have hρ : 0 < dist (β t₂) (α a) := dist_pos.2 fun h => by rw [h] at ht₂H; exact hwR ht₂H
  have hρ0 : 0 < dist (β t₂) (α a) / 2 := half_pos hρ
  -- the contact is free for the earlier second prefix
  have hfreeβ : IsFreeAt (β '' Icc 0 t₂) (α a) := by
    rw [hab]; exact IsPathGood.isFreeAt_of_lt hpβ ht₂b hbζ
  obtain ⟨ε₁, hε₁, hball₁⟩ := exists_ball_of_isFreeAt hfreeβ
  -- the first path just after `a`
  obtain ⟨r₀, har₀, -, hr₀ball⟩ := exists_gt_forall_Icc_mem_ball hpα.continuousOn haζ' (lt_min hρ0 hε₁)
  obtain ⟨q, hq₁, hq₂, hqH⟩ := IsPathGood.exists_rat_mem_H hpα (lt_min har₀ hav₁)
    ((ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hv₁)
  obtain ⟨q', hq'₁, hq'₂⟩ := exists_rat_toNNReal_btwn ht₂b
  set r := (q : ℝ).toNNReal with hr
  set t := (q' : ℝ).toNNReal with ht
  have hrv₁ : r ≤ v₁ := (hq₂.trans_le (min_le_right _ _)).le
  have hrr₀ : r ≤ r₀ := (hq₂.trans_le (min_le_left _ _)).le
  have hrζ : (r : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hrv₁).trans hv₁
  have htζ : (t : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 hq'₂.le).trans hbζ
  refine ⟨q, q', hrζ, htζ, fun hbar => ?_⟩
  have hcαr := IsPathGood.isCompact_image hpα hrζ
  have hcαa := IsPathGood.isCompact_image hpα haζ
  have hcβt := IsPathGood.isCompact_image hpβ htζ
  have hcβ₂ := IsPathGood.isCompact_image hpβ ht₂ζ
  -- the frozen prefixes are disjoint
  have hdisj : Disjoint (α '' Icc 0 r) (β '' Icc 0 t) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have := (hmin s s' ((ENNReal.coe_le_coe.2 hs.2).trans hrζ) ((ENNReal.coe_le_coe.2 hs'.2).trans htζ)
      hss'.symm).2
    exact absurd (this.trans hs'.2) (not_le.2 hq'₂)
  have hd₂ : Disjoint (α '' Icc 0 a) (β '' Icc 0 t₂) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have := (hmin s s' ((ENNReal.coe_le_coe.2 hs.2).trans haζ) ((ENNReal.coe_le_coe.2 hs'.2).trans ht₂ζ)
      hss'.symm).2
    exact absurd (this.trans hs'.2) (not_le.2 ht₂b)
  -- the onward first arc is small
  have hαsmall : α '' Icc a r ⊆ ball (α a) (min (dist (β t₂) (α a) / 2) ε₁) :=
    (image_mono (Icc_subset_Icc_right hrr₀)).trans hr₀ball
  -- the late second path is in the unbounded domain of the frozen first prefix
  have hc2 : ∀ s ∈ Ico t₂ b, β s ∈ H \ fillH (α '' Icc 0 r) := by
    intro s hs
    have hsI : s ∈ Ioo t₁ b := ⟨ht₁₂.trans_le hs.1, hs.2⟩
    have hβoff : ∀ s' ∈ Icc t₂ s, β s' ∈ H \ α '' Icc a r := by
      intro s' hs'
      refine ⟨harch s' ⟨ht₁₂.trans_le hs'.1, hs'.2.trans_lt hs.2⟩, ?_⟩
      rintro ⟨v, hv, hvs'⟩
      have := (hmin v s' ((ENNReal.coe_le_coe.2 hv.2).trans hrζ)
        ((ENNReal.coe_le_coe.2 (hs'.2.trans hs.2.le)).trans hbζ) hvs').2
      exact absurd (hs'.2.trans_lt hs.2) (not_lt.2 this)
    have hcαar : IsCompact (α '' Icc a r) := IsPathGood.isCompact_image_Icc hpα hrζ
    have h1 : β t₂ ∈ H \ fillH (α '' Icc a r) := by
      refine mem_H_diff_fillH_of_ray hcαar ht₂H fun y hy hmem => ?_
      have h₁ := (mem_ball.1 (hαsmall hmem)).trans_le (min_le_left _ _)
      have h₂ := dist_le_dist_add_mul_I (show (0 : ℝ) < (β t₂).im from ht₂H).le hw0 hy
      linarith
    have hβcs : ContinuousOn β (Icc t₂ s) :=
      hpβ.continuousOn.mono fun s' hs' => (ENNReal.coe_le_coe.2 (hs'.2.trans hs.2.le)).trans hbζ
    have h2 : β s ∈ connectedComponentIn (H \ α '' Icc a r) (β t₂) :=
      (isPreconnected_Icc.image _ hβcs).subset_connectedComponentIn ⟨t₂, left_mem_Icc.2 hs.1, rfl⟩
        (by rintro _ ⟨s', hs', rfl⟩; exact hβoff s' hs') ⟨s, right_mem_Icc.2 hs.1, rfl⟩
    have h3 : β s ∈ H \ fillH (α '' Icc a r) := connectedComponentIn_subset_H_diff_fillH hcαar.isClosed h1 h2
    have h4 := H_diff_fillH_inter_subset_of_real hcαa hcαar ?_ (hfree s hsI) h3
    · rwa [← image_union, Icc_union_Icc_eq_Icc zero_le hq₁.le] at h4
    · rintro _ ⟨⟨v, hv, rfl⟩, ⟨v', hv', hvv'⟩⟩
      have := hpα.1 ((ENNReal.coe_le_coe.2 hv'.2).trans hrζ) ((ENNReal.coe_le_coe.2 hv.2).trans haζ) hvv'
      rw [← this, le_antisymm (this ▸ hv.2) hv'.1]
      exact hw0
  -- the onward first point is inside the closing curve
  have hin : α r ∈ WangWu.jordanIn (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L) := by
    have hret := (no_return_of_firstContact hpα.1 hpβ.1 haζ hbζ hab hmin).1 r hq₁ hrζ
    refine mem_jordanIn_of_not_mem_jordanOut (fun h => ?_) fun hout => ?_
    · rcases h with h | h
      · exact hret h
      · exact absurd (hLim _ h) (not_le.2 hqH)
    have hz : α r ∈ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 t₂) :=
      mem_H_diff_fillH_union_of_disjoint hcαa hcβ₂ hd₂ (IsPathGood.mem_H_diff_fillH_of_lt hpα hq₁ hrζ hqH)
        (hball₁ _ (ball_subset_ball (min_le_right _ _) (hαsmall ⟨r, ⟨hq₁.le, le_rfl⟩, rfl⟩)) hqH)
    refine hnot r ⟨hq₁, hrv₁⟩ hqH (mem_H_diff_fillH_of_mem_jordanOut_closing (hcαa.union hcβ₂)
      (hcαa.union (IsPathGood.isCompact_image hpβ hbζ)) hLc
      (union_subset_union subset_rfl (image_mono (Icc_subset_Icc_right ht₂b.le))) ?_ ?_ hLim ?_ hz hout)
    · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact IsPathGood.im_nonneg hpα ((ENNReal.coe_le_coe.2 hs.2).trans haζ)
      · exact IsPathGood.im_nonneg hpβ ((ENNReal.coe_le_coe.2 hs.2).trans hbζ)
    · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) h0
      · exact Or.inl ⟨s, hs, rfl⟩
      · rcases le_or_gt s t₂ with h | h
        · exact Or.inr ⟨s, ⟨hs.1, h⟩, rfl⟩
        rcases eq_or_lt_of_le hs.2 with hsb | hsb
        · exact Or.inl ⟨a, ⟨zero_le, le_rfl⟩, by rw [hsb, hab]⟩
        · exact absurd h0 (ne_of_gt (harch s ⟨ht₁₂.trans h, hsb⟩))
    · have h₁ : IsPreconnected (α '' Icc 0 a ∪ L) :=
        (isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hpα haζ)).union (xα : ℂ)
          ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hpα⟩ hxα hLpc
      have h₂ : IsPreconnected (α '' Icc 0 a ∪ L ∪ β '' Icc 0 t₂) :=
        h₁.union (xβ : ℂ) (Or.inr hxβ) ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hpβ⟩
          (isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hpβ ht₂ζ))
      have he : α '' Icc 0 a ∪ β '' Icc 0 t₂ ∪ L = α '' Icc 0 a ∪ L ∪ β '' Icc 0 t₂ := by
        ext z; simp only [mem_union]; tauto
      rw [he]; exact h₂
  -- the forbidden exit
  refine hbar hdisj (mem_unboundedPart_of_mem_H_diff_fillH hcαr.isClosed (hc2 t ⟨hq'₁.le, hq'₂⟩)) b a r hbζ
    ⟨hq'₂, hq₁, le_rfl, fun s hs => ?_, hab.symm, hin⟩
  have hsH := harch s ⟨ht₁₂.trans (hq'₁.trans hs.1), hs.2⟩
  exact mem_unboundedPart_of_mem_H_diff_fillH (hcαr.union hcβt).isClosed
    (mem_H_diff_fillH_union_of_disjoint hcαr hcβt hdisj (hc2 s ⟨(hq'₁.trans hs.1).le, hs.2⟩)
      (IsPathGood.mem_H_diff_fillH_of_lt hpβ hs.1 ((ENNReal.coe_le_coe.2 hs.2.le).trans hbζ) hsH))

/-! ### No continuation off the joint unbounded domain -/

/-- **The core of Aux. lemmas 74–75 at a real contact.** At a real common first contact, with Lemma 7.6's conclusion
at the rational stops, the continuation points `α(v) ∈ ℍ`, `a < v ≤ v₁`, cannot all lie off the joint unbounded
domain. -/
theorem false_of_notMem_of_real (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hLc : IsCompact L) (hLpc : IsPreconnected L) (hLim : ∀ z ∈ L, z.im ≤ 0) (hxα : (xα : ℂ) ∈ L)
    (hxβ : (xβ : ℂ) ∈ L) (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H) {v₁ : ℝ≥0} (hav₁ : a < v₁)
    (hv₁ : (v₁ : ℝ≥0∞) ≤ ζα)
    (hnot : ∀ v ∈ Ioc a v₁, α v ∈ H → α v ∉ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b))
    (hbar : ∀ q q' : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζα → (((q' : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζβ →
      FirstExitBarrier α (q : ℝ).toNNReal β ζβ (q' : ℝ).toNNReal L) : False := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := id hfc
  have hw0 : (α a).im = 0 := IsPathGood.im_eq_zero hpα haζ hwR
  have haζ' : (a : ℝ≥0∞) < ζα := (ENNReal.coe_lt_coe.2 hav₁).trans_le hv₁
  have hcα := IsPathGood.isCompact_image hpα haζ
  have hcβ := IsPathGood.isCompact_image hpβ hbζ
  have hreal : ∀ y ∈ α '' Icc 0 a ∩ β '' Icc 0 b, y.im = 0 := fun y hy => by
    rw [mem_singleton_iff.1 (image_inter_image_subset_of_isFirstContact hfc hy)]; exact hw0
  -- an interior continuation point
  obtain ⟨v₀, hv₀, hv₀H⟩ := IsPathGood.exists_mem_H hpα hav₁ hv₁
  have hv₀ζ : (v₀ : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hv₀.2.le).trans hv₁
  have hzD := hnot v₀ ⟨hv₀.1, hv₀.2.le⟩ hv₀H
  have hzα : α v₀ ∈ H \ fillH (α '' Icc 0 a) := IsPathGood.mem_H_diff_fillH_of_lt hpα hv₀.1 hv₀ζ hv₀H
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ b) with hb0 | hb0
  · -- `b = 0`: the second prefix is a real point
    refine hzD ?_
    rw [fillH_union_of_forall_notMem_H]
    · exact hzα
    rintro _ ⟨t, ht, rfl⟩
    rw [le_antisymm ht.2 (hb0 ▸ ht.1), ← hab]
    exact hwR
  have hβc : ContinuousOn β (Ico 0 b) :=
    hpβ.continuousOn.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2.le).trans hbζ
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hcα.isClosed (isPreconnected_Ico.image _ hβc)
      (image_Ico_subset_of_isFirstContact hpβ hfc) with hfr | htr
  swap
  · -- the second prefix arrives from inside the first hull
    exact hzD (H_diff_fillH_subset_of_isTrappedAt hpα hpβ hfc hwR htr hzα)
  by_cases hβarch : ∃ t₁ < b, ∀ t ∈ Ioo t₁ b, β t ∈ H
  · -- a final excursion: Lemma 7.6
    obtain ⟨t₁, ht₁, harch⟩ := hβarch
    obtain ⟨q, q', hq, hq', hno⟩ := exists_not_firstExitBarrier_real hpα hpβ hLc hLpc hLim hxα hxβ hfc hwR ht₁
      harch (fun t ht => mem_H_diff_fillH_of_isFreeAt (hfr _ ⟨t, ⟨zero_le, ht.2⟩, rfl⟩) (harch t ht)) hav₁ hv₁
      hnot
    exact hno (hbar q q' hq hq')
  push Not at hβarch
  -- real touches accumulate at `b`: the accumulation argument
  have hd : 0 < dist (α v₀) (α a) := dist_pos.2 fun h => by rw [h] at hv₀H; exact hwR hv₀H
  obtain ⟨t₀, ht₀, ht₀ball⟩ := exists_lt_forall_Icc_mem_ball hpβ.continuousOn hbζ hb0 hd
  rw [← hab] at ht₀ball
  obtain ⟨s', hs', hs'H⟩ := hβarch t₀ ht₀
  have hs'ζ : (s' : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 hs'.2.le).trans hbζ
  have hcβs := IsPathGood.isCompact_image hpβ hs'ζ
  -- the continuation is free for the second prefix up to `s'`
  have hwfree : IsFreeAt (β '' Icc 0 s') (α a) := by
    rw [hab]; exact IsPathGood.isFreeAt_of_lt hpβ hs'.2 hbζ
  obtain ⟨ε₂, hε₂, hball₂⟩ := hwfree
  obtain ⟨v₂, hav₂, -, hv₂ball⟩ := exists_gt_forall_Icc_mem_ball hpα.continuousOn haζ' (half_pos hε₂)
  have hαc : ContinuousOn α (Ioc a v₀) :=
    hpα.continuousOn.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans hv₀ζ
  have hX : α '' Ioc a v₀ ⊆ {y : ℂ | 0 ≤ y.im} \ β '' Icc 0 s' := by
    rintro _ ⟨v, hv, rfl⟩
    have hvζ : (v : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hv.2).trans hv₀ζ
    refine ⟨IsPathGood.im_nonneg hpα hvζ, ?_⟩
    rintro ⟨t, ht, htv⟩
    have := (hmin v t hvζ ((ENNReal.coe_le_coe.2 ht.2).trans hs'ζ) htv.symm).2
    exact absurd (this.trans ht.2) (not_le.2 hs'.2)
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hcβs.isClosed (isPreconnected_Ioc.image _ hαc) hX
    with hXf | hXt
  · have hz1 : α v₀ ∈ H \ fillH (β '' Icc 0 s') :=
      mem_H_diff_fillH_of_isFreeAt (hXf _ ⟨v₀, ⟨hv₀.1, le_rfl⟩, rfl⟩) hv₀H
    have hreal' : ∀ y ∈ β '' Icc 0 s' ∩ β '' Icc s' b, y.im = 0 := by
      rintro _ ⟨⟨r, hr, rfl⟩, ⟨r', hr', hrr'⟩⟩
      have := hpβ.1 ((ENNReal.coe_le_coe.2 hr'.2).trans hbζ) ((ENNReal.coe_le_coe.2 hr.2).trans hs'ζ) hrr'
      rw [← this, le_antisymm (this ▸ hr.2) hr'.1]
      exact IsPathGood.im_eq_zero hpβ hs'ζ hs'H
    have hz2 := mem_H_diff_fillH_union_of_subset_ball hcβs (IsPathGood.isCompact_image_Icc hpβ hbζ) hreal' hw0
      ((image_mono (Icc_subset_Icc_left hs'.1.le)).trans ht₀ball) hz1 le_rfl
    rw [← image_union, Icc_union_Icc_eq_Icc zero_le hs'.2.le] at hz2
    exact hzD (H_diff_fillH_inter_subset_of_real hcα hcβ hreal hzα hz2)
  · -- a continuation point near the contact is free
    have hv₃ : min v₀ v₂ ∈ Ioc a v₀ := ⟨lt_min hv₀.1 hav₂, min_le_left _ _⟩
    have hv₃ball : α (min v₀ v₂) ∈ ball (α a) (ε₂ / 2) :=
      hv₂ball ⟨min v₀ v₂, ⟨hv₃.1.le, min_le_right _ _⟩, rfl⟩
    have hfree3 : IsFreeAt (β '' Icc 0 s') (α (min v₀ v₂)) :=
      ⟨ε₂ / 2, half_pos hε₂, fun y hy => hball₂ ⟨ball_subset_ball' (by linarith [mem_ball.1 hv₃ball]) hy.1, hy.2⟩⟩
    exact hfree3.not_isTrappedAt (IsPathGood.im_nonneg hpα ((ENNReal.coe_le_coe.2 hv₃.2).trans hv₀ζ))
      (hXt _ ⟨min v₀ v₂, hv₃, rfl⟩)

/-- **Aux. lemma 75 at a real contact.** At a common first contact `w = α(a) = β(b) ∈ ℝ` of two good paths, if Lemma
7.6's conclusion holds at the rational stops, every continuation point `α(s)`, `a < s ≤ ζα`, is free for the joint
prefix. -/
theorem forall_isFreeAt_of_barrier_real (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hLc : IsCompact L) (hLpc : IsPreconnected L) (hLim : ∀ z ∈ L, z.im ≤ 0) (hxα : (xα : ℂ) ∈ L)
    (hxβ : (xβ : ℂ) ∈ L) (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H)
    (hbar : ∀ q q' : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζα → (((q' : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζβ →
      FirstExitBarrier α (q : ℝ).toNNReal β ζβ (q' : ℝ).toNNReal L) :
    ∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ ζα → IsFreeAt (α '' Icc 0 a ∪ β '' Icc 0 b) (α s) := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := id hfc
  have hcK : IsCompact (α '' Icc 0 a ∪ β '' Icc 0 b) :=
    (IsPathGood.isCompact_image hpα haζ).union (IsPathGood.isCompact_image hpβ hbζ)
  have hret := (no_return_of_firstContact hpα.1 hpβ.1 haζ hbζ hab hmin).1
  have hXpc : IsPreconnected (α '' {s : ℝ≥0 | a < s ∧ (s : ℝ≥0∞) ≤ ζα}) := by
    refine IsPreconnected.image ?_ _ (hpα.continuousOn.mono fun s hs => hs.2)
    refine OrdConnected.isPreconnected ⟨fun x hx y hy z hz => ⟨hx.1.trans_le hz.1, ?_⟩⟩
    exact (ENNReal.coe_le_coe.2 hz.2).trans hy.2
  have hXK : α '' {s : ℝ≥0 | a < s ∧ (s : ℝ≥0∞) ≤ ζα} ⊆
      {z : ℂ | 0 ≤ z.im} \ (α '' Icc 0 a ∪ β '' Icc 0 b) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨IsPathGood.im_nonneg hpα hs.2, hret s hs.1 hs.2⟩
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hcK.isClosed hXpc hXK with hfree | htrap
  · exact fun s hs hsζ => hfree _ ⟨s, ⟨hs, hsζ⟩, rfl⟩
  intro s₁ hs₁ hs₁ζ
  exfalso
  exact false_of_notMem_of_real hpα hpβ hLc hLpc hLim hxα hxβ hfc hwR hs₁ hs₁ζ
    (fun v hv _ => (htrap _ ⟨v, ⟨hv.1, (ENNReal.coe_le_coe.2 hv.2).trans hs₁ζ⟩, rfl⟩).notMem) hbar

/-! ### `RealContactConfinement` -/

/-- **Lemma 7.7's confinement at a real common first contact** (`RealContactConfinement`, Aux. lemmas 74–75 at a
"physical real junction"). -/
theorem realContactConfinement : RealContactConfinement := by
  intro α β ζ₁ ζ₂ x₁ x₂ hp₁ hp₂ hx a b hfc hwR hbar₁ hbar₂
  set L := lowerArc x₂ x₁ with hL
  have hLim : ∀ z ∈ L, z.im ≤ 0 := fun z hz => (im_le_zero_of_mem_lowerArc hz).1
  have haζ := hfc.1
  have hbζ := hfc.2.1
  have hab : α a = β b := hfc.2.2.1
  have h₁ := forall_mem_closure_of_forall_isFreeAt hp₁ hp₂ haζ hbζ
    (forall_isFreeAt_of_barrier_real hp₁ hp₂ isCompact_lowerArc isPreconnected_lowerArc hLim left_mem_lowerArc
      right_mem_lowerArc hfc hwR (barrier_of_truncAt le_rfl le_rfl hbar₁))
  have h₂' := forall_mem_closure_of_forall_isFreeAt hp₂ hp₁ hbζ haζ
    (forall_isFreeAt_of_barrier_real hp₂ hp₁ isCompact_lowerArc isPreconnected_lowerArc hLim right_mem_lowerArc
      left_mem_lowerArc (isFirstContact_swap hfc) (hab ▸ hwR) (barrier_of_truncAt le_rfl le_rfl hbar₂))
  rw [activeDomain_swap] at h₂'
  have hw : α a ∈ closure (activeDomain α a β b) := by
    rw [activeDomain_eq_of_isPathGood hp₁ hp₂ haζ hbζ]
    exact mem_closure_H_diff_fillH_of_real hp₁ hp₂ hfc hwR
  refine ⟨fun s hs hsζ => ?_, fun t ht htζ => ?_⟩
  · rcases hs.lt_or_eq with hs | rfl
    · exact h₁ s hs hsζ
    · exact hw
  · rcases ht.lt_or_eq with ht | rfl
    · exact h₂' t ht htζ
    · rw [← hab]; exact hw

end Sec7

end InteractingSLE
