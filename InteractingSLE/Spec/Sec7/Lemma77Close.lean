/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Lens

/-!
# Lemma 7.7: the confinement clause at an interior common first contact

Packet PROVE-LEMMA77 (specification §7.2, Lemma 7.7, p. 282, and Aux. lemma 75, p. 281).

At a common first contact `w = α(a) = β(b) ∈ ℍ` of two good paths from `x₁ > x₂`, if Lemma 7.6's conclusion holds at
every pair of rational stops (both halves), both available continuations lie in the closure of the joint unbounded
component `D = activeDomain α a β b` (`conf_of_barrier_of_mem_H`), the contact point included. For the contact point
itself when neither path continues ("A terminal contact supplies no continuation", p. 282), `mem_closure_activeDomain`
uses the Jordan curve `α([0, a]) ∪ β([0, b]) ∪ L`: `w` is adherent to its outside (Jordan curve theorem), and near
`w` the outside lies in `D` (`mem_H_diff_fillH_of_mem_jordanOut_closing`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart Foundations.ThetaCurve

/-- **Near an interior first contact, the outside of the closing curve is in the active domain.** -/
theorem exists_ball_jordanOut_subset {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {L : Set ℂ} (hLc : IsCompact L)
    (hLpc : IsPreconnected L) (hLim : ∀ z ∈ L, z.im ≤ 0) (hxα : (xα : ℂ) ∈ L) (hxβ : (xβ : ℂ) ∈ L)
    {a b : ℝ≥0} (hfc : IsFirstContact α ζα β ζβ a b) (hwH : α a ∈ H) :
    ∃ ε > 0, ball (α a) ε ⊆ H ∧ ∀ z ∈ ball (α a) ε,
      z ∈ WangWu.jordanOut (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L) → z ∈ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := hfc
  set w := α a with hw
  obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.1 QuantumZipper.isOpen_H w hwH
  have ha0 : 0 < a := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpα hwH)
  have hb0 : 0 < b := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpβ (hab ▸ hwH))
  obtain ⟨s', hs', hs'ball⟩ := exists_lt_forall_Icc_mem_ball hpα.continuousOn haζ ha0 hρ
  obtain ⟨t', ht', ht'ball⟩ := exists_lt_forall_Icc_mem_ball hpβ.continuousOn hbζ hb0 hρ
  rw [← hab] at ht'ball
  have hs'ζ : (s' : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hs'.le).trans haζ
  have ht'ζ : (t' : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 ht'.le).trans hbζ
  have hcF₁ : IsCompact (α '' Icc 0 s') := IsPathGood.isCompact_image hpα hs'ζ
  have hcF₂ : IsCompact (β '' Icc 0 t') := IsPathGood.isCompact_image hpβ ht'ζ
  have hcK : IsCompact (α '' Icc 0 a ∪ β '' Icc 0 b) :=
    (IsPathGood.isCompact_image hpα haζ).union (IsPathGood.isCompact_image hpβ hbζ)
  have hdF : Disjoint (α '' Icc 0 s') (β '' Icc 0 t') := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', hqq'⟩
    have := (hmin q q' ((ENNReal.coe_le_coe.2 hq.2).trans hs'ζ) ((ENNReal.coe_le_coe.2 hq'.2).trans ht'ζ)
      hqq'.symm).1
    exact absurd (this.trans hq.2) (not_le.2 hs')
  have hfF : IsFreeAt (α '' Icc 0 s' ∪ β '' Icc 0 t') w := by
    refine isFreeAt_union_of_disjoint hcF₁ hcF₂ hdF (IsPathGood.isFreeAt_of_lt hpα hs' haζ) ?_
    have h2 := IsPathGood.isFreeAt_of_lt hpβ ht' hbζ
    rw [← (show α a = β b from hab)] at h2
    exact h2
  obtain ⟨ε₁, hε₁, hball₁⟩ := exists_ball_of_isFreeAt hfF
  refine ⟨min ε₁ ρ, lt_min hε₁ hρ, (ball_subset_ball (min_le_right _ _)).trans hρH, fun z hz hzJ => ?_⟩
  have hzH : z ∈ H := hρH (ball_subset_ball (min_le_right _ _) hz)
  refine mem_H_diff_fillH_of_mem_jordanOut_closing (hcF₁.union hcF₂) hcK hLc
    (union_subset_union (image_mono (Icc_subset_Icc_right hs'.le)) (image_mono (Icc_subset_Icc_right ht'.le)))
    ?_ ?_ hLim ?_ (hball₁ z (ball_subset_ball (min_le_left _ _) hz) hzH) hzJ
  · rintro _ (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact IsPathGood.im_nonneg hpα ((ENNReal.coe_le_coe.2 hq.2).trans haζ)
    · exact IsPathGood.im_nonneg hpβ ((ENNReal.coe_le_coe.2 hq.2).trans hbζ)
  · rintro _ (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) h0
    · rcases le_total q s' with h | h
      · exact Or.inl ⟨q, ⟨hq.1, h⟩, rfl⟩
      · exact absurd h0 (ne_of_gt (hρH (hs'ball ⟨q, ⟨h, hq.2⟩, rfl⟩)))
    · rcases le_total q t' with h | h
      · exact Or.inr ⟨q, ⟨hq.1, h⟩, rfl⟩
      · exact absurd h0 (ne_of_gt (hρH (ht'ball ⟨q, ⟨h, hq.2⟩, rfl⟩)))
  · have h₁ : IsPreconnected (α '' Icc 0 s' ∪ L) :=
      (isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hpα hs'ζ)).union (xα : ℂ)
        ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hpα⟩ hxα hLpc
    have h₂ : IsPreconnected (α '' Icc 0 s' ∪ L ∪ β '' Icc 0 t') :=
      h₁.union (xβ : ℂ) (Or.inr hxβ) ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hpβ⟩
        (isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hpβ ht'ζ))
    have he : α '' Icc 0 s' ∪ β '' Icc 0 t' ∪ L = α '' Icc 0 s' ∪ L ∪ β '' Icc 0 t' := by
      ext z; simp only [mem_union]; tauto
    rw [he]; exact h₂

/-- The joint prefix is closed, and the active domain is the complement of its filling. -/
theorem activeDomain_eq_of_isPathGood {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {a b : ℝ≥0} (haζ : (a : ℝ≥0∞) ≤ ζα)
    (hbζ : (b : ℝ≥0∞) ≤ ζβ) : activeDomain α a β b = H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  ext z
  exact (mem_H_diff_fillH_of_isClosed ((IsPathGood.isCompact_image hpα haζ).union
    (IsPathGood.isCompact_image hpβ hbζ)).isClosed).symm

/-- **The interior contact point is adherent to the active domain** (Jordan curve theorem). -/
theorem mem_closure_activeDomain {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {a b : ℝ≥0}
    (hfc : IsFirstContact α ζ₁ β ζ₂ a b) (hwH : α a ∈ H) : α a ∈ closure (activeDomain α a β b) := by
  set L := lowerArc x₂ x₁ with hL
  have hLim : ∀ z ∈ L, z.im ≤ 0 := fun z hz => (im_le_zero_of_mem_lowerArc hz).1
  obtain ⟨ε, hε, hεH, hεD⟩ := exists_ball_jordanOut_subset hp₁ hp₂ isCompact_lowerArc isPreconnected_lowerArc
    hLim left_mem_lowerArc right_mem_lowerArc hfc hwH
  obtain ⟨haζ, hbζ, hab, hmin⟩ := hfc
  have ha0 : 0 < a := pos_iff_ne_zero.2 (ne_zero_of_mem_H hp₁ hwH)
  have hb0 : 0 < b := pos_iff_ne_zero.2 (ne_zero_of_mem_H hp₂ (hab ▸ hwH))
  -- the Jordan curve `α([0, a]) ∪ β([0, b]) ∪ L`
  have hαc := IsPathGood.continuousOn_Icc hp₁ haζ
  have hβc := IsPathGood.continuousOn_Icc hp₂ hbζ
  have hαi := IsPathGood.injOn_Icc hp₁ haζ
  have hβi := IsPathGood.injOn_Icc hp₂ hbζ
  have hu₁ : IsArcFrom (segArc α 0 a) (x₁ : ℂ) (α a) := by
    have := isArcFrom_segArc ha0 hαc hαi
    rwa [IsPathGood.zero hp₁] at this
  have hu₂ : IsArcFrom (Sec6.arcRev (segArc β 0 b)) (α a) (x₂ : ℂ) := by
    have := isArcFrom_arcRev (isArcFrom_segArc hb0 hβc hβi)
    rwa [IsPathGood.zero hp₂, ← hab] at this
  have hint : arc (segArc α 0 a) ∩ arc (Sec6.arcRev (segArc β 0 b)) ⊆ {α a} := by
    rw [arc_segArc zero_le, arc_arcRev, arc_segArc zero_le]
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    have := (hmin s t ((ENNReal.coe_le_coe.2 hs.2).trans haζ) ((ENNReal.coe_le_coe.2 ht.2).trans hbζ)
      hts.symm).1
    rw [mem_singleton_iff, le_antisymm hs.2 this]
  have hu := isArcFrom_arcJoin hu₁ hu₂ hint
  have harcu : arc (Sec6.arcJoin (segArc α 0 a) (Sec6.arcRev (segArc β 0 b))) =
      α '' Icc 0 a ∪ β '' Icc 0 b := by
    rw [arc_arcJoin hu₁ hu₂, arc_segArc zero_le, arc_arcRev, arc_segArc zero_le]
  have hℓ := isArcFrom_lowerArcPath hx
  have hJ : LQGMetric.JordanMap.IsJordanCurve (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L) := by
    have := isJordanCurve_arc_union hu hℓ ?_
    · rwa [harcu] at this
    rw [harcu]
    rintro z ⟨hzK, hzL⟩
    have hz0 : 0 ≤ z.im := by
      rcases hzK with ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
      · exact IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans haζ)
      · exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hbζ)
    rcases (im_le_zero_of_mem_lowerArc hzL).2 (le_antisymm (im_le_zero_of_mem_lowerArc hzL).1 hz0) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hwJ : α a ∈ closure (WangWu.jordanOut (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L)) := by
    rw [closure_jordanOut hJ]
    exact Or.inr (Or.inl (Or.inl ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩))
  rw [activeDomain_eq_of_isPathGood hp₁ hp₂ haζ hbζ, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨z, hzJ, hzd⟩ := Metric.mem_closure_iff.1 hwJ (min δ ε) (lt_min hδ hε)
  refine ⟨z, hεD z ?_ hzJ, lt_of_lt_of_le hzd (min_le_left _ _)⟩
  rw [mem_ball, dist_comm]
  exact lt_of_lt_of_le hzd (min_le_right _ _)

/-- `IsFirstContact` is symmetric in the two paths. -/
theorem isFirstContact_swap {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {a b : ℝ≥0}
    (h : IsFirstContact α ζα β ζβ a b) : IsFirstContact β ζβ α ζα b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun t s ht hs hts => (h.2.2.2 s t hs ht hts.symm).symm⟩

theorem activeDomain_swap (α β : ℝ≥0 → ℂ) (a b : ℝ≥0) : activeDomain β b α a = activeDomain α a β b := by
  simp only [activeDomain, union_comm]

/-- The continuation of a good path stays adherent to the active domain when every continuation point is free. -/
theorem forall_mem_closure_of_forall_isFreeAt {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {a b : ℝ≥0} (haζ : (a : ℝ≥0∞) ≤ ζα)
    (hbζ : (b : ℝ≥0∞) ≤ ζβ)
    (hfree : ∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ ζα → IsFreeAt (α '' Icc 0 a ∪ β '' Icc 0 b) (α s)) :
    ∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ ζα → α s ∈ closure (activeDomain α a β b) := by
  intro s hs hsζ
  rw [activeDomain_eq_of_isPathGood hpα hpβ haζ hbζ]
  exact mem_closure_H_diff_fillH_of_isFreeAt (hfree s hs hsζ) (IsPathGood.im_nonneg hpα hsζ)

/-- The start of a continuation is adherent to the closure its later points are adherent to. -/
theorem mem_closure_of_forall_gt {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood α ζ x) {a : ℝ≥0}
    (ha : (a : ℝ≥0∞) < ζ) {S : Set ℂ} (h : ∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ ζ → α s ∈ closure S) :
    α a ∈ closure S := by
  obtain ⟨c, hac, hcζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
  have hac' : a < c := ENNReal.coe_lt_coe.1 hac
  have hcont : ContinuousWithinAt α (Ioc a c) a :=
    (hp.continuousOn a ha.le).mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hcζ.le
  have hcl : a ∈ closure (Ioc a c) := by rw [closure_Ioc hac'.ne]; exact ⟨le_rfl, hac'.le⟩
  have := hcont.mem_closure_image hcl
  refine closure_minimal ?_ isClosed_closure this
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs.1 ((ENNReal.coe_le_coe.2 hs.2).trans hcζ.le)

/-- **Lemma 7.7's confinement clause at an interior common first contact.** -/
theorem conf_of_barrier_of_mem_H {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {a b : ℝ≥0}
    (hfc : IsFirstContact α ζ₁ β ζ₂ a b) (hwH : α a ∈ H)
    (hbar₁ : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁))
    (hbar₂ : ∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁)) :
    (∀ s : ℝ≥0, a ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → α s ∈ closure (activeDomain α a β b)) ∧
      ∀ t : ℝ≥0, b ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → β t ∈ closure (activeDomain α a β b) := by
  set L := lowerArc x₂ x₁ with hL
  have hLim : ∀ z ∈ L, z.im ≤ 0 := fun z hz => (im_le_zero_of_mem_lowerArc hz).1
  have haζ := hfc.1
  have hbζ := hfc.2.1
  have hab : α a = β b := hfc.2.2.1
  -- the continuation of each path
  have h₁ := forall_mem_closure_of_forall_isFreeAt hp₁ hp₂ haζ hbζ
    (forall_isFreeAt_of_barrier hp₁ hp₂ isCompact_lowerArc isPreconnected_lowerArc hLim left_mem_lowerArc
      right_mem_lowerArc hfc hwH hbar₁)
  have h₂' := forall_mem_closure_of_forall_isFreeAt hp₂ hp₁ hbζ haζ
    (forall_isFreeAt_of_barrier hp₂ hp₁ isCompact_lowerArc isPreconnected_lowerArc hLim right_mem_lowerArc
      left_mem_lowerArc (isFirstContact_swap hfc) (hab ▸ hwH) hbar₂)
  rw [activeDomain_swap] at h₂'
  -- the contact point
  have hw : α a ∈ closure (activeDomain α a β b) := by
    rcases haζ.lt_or_eq with ha | ha
    · exact mem_closure_of_forall_gt hp₁ ha h₁
    rcases hbζ.lt_or_eq with hb | hb
    · rw [hab]; exact mem_closure_of_forall_gt hp₂ hb h₂'
    exact mem_closure_activeDomain hp₁ hp₂ hx hfc hwH
  refine ⟨fun s hs hsζ => ?_, fun t ht htζ => ?_⟩
  · rcases hs.lt_or_eq with hs | rfl
    · exact h₁ s hs hsζ
    · exact hw
  · rcases ht.lt_or_eq with ht | rfl
    · exact h₂' t ht htζ
    · rw [← hab]; exact hw

end Sec7

end InteractingSLE
