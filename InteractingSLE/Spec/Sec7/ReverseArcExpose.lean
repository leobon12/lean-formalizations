/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77RealTip

/-!
# Aux. lemma 69, exposure: the common arc of a reverse minimal contact is adherent to the joint unbounded domain

Packet PROVE-LEMMA76B (specification §7.2, Aux. lemma 69, p. 273, `source/spec/p241-288.md#aux-69`: "every compact
subarc of `J ∩ ℍ` is exposed on the boundary of the unbounded component `D` of `ℍ \ (α₁ ∪ α₂)`").

Setting (the output of `exists_rat_reverseArc`): two good paths `α` from `x₁` and `β` from `x₂ < x₁`, stopped at `q₁`
and `q₂`, whose stopped ranges meet exactly in the reverse common arc `J = α([σ₁, q₁]) = β([σ₂, q₂])` (`β ∘ f = α`, `f`
decreasing from `q₂` to `σ₂`).

## Proof (not the source's crosscut description)

Fix `σ₁ < s < q₁` with `α(s) ∈ ℍ`, and `σ₁ < a < s < c < q₁` with `α([a, c]) ⊆ ℍ`. The union
`Γ = α([0, q₁]) ∪ β([0, q₂])` is the simple arc `α([0, q₁]) · β([0, σ₂])⁻¹` from `x₁` to `x₂`, closed by the lower arc
`L` into a Jordan curve. Its part `F = α([0, a]) ∪ β([0, f c])` (two disjoint earlier prefixes) contains every real
point of `Γ`, and `α(s) = β(f s)` is free for both prefixes by the tip property of each path, hence for `F`
(Janiszewski). The closing-curve lemma (`mem_H_diff_fillH_of_mem_jordanOut_closing`) then puts the points of the
outside of `Γ ∪ L` near `α(s)` into the joint unbounded domain, and `α(s)` is adherent to the outside.

## Main results

* `ReverseArc.eq_of_mem_image_Icc`: the reverse correspondence `f` maps `[σ₁, q₁]` onto `[σ₂, q₂]`;
* `ReverseArc.union_eq`: `Γ = α([0, q₁]) ∪ β([0, σ₂])`;
* `ReverseArc.isJordanCurve`: `Γ ∪ L` is a Jordan curve;
* **`ReverseArc.mem_closure_H_diff_fillH`**: `α(s) ∈ closure (ℍ \ fill Γ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart Foundations.ThetaCurve

namespace ReverseArc

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {q₁ q₂ σ₁ σ₂ : ℝ≥0} {f : ℝ≥0 → ℝ≥0}

/-- The decreasing correspondence maps `[σ₁, q₁]` onto `[σ₂, q₂]`. -/
theorem exists_eq_of_mem_Icc (hσq : σ₁ ≤ q₁) (hfc : ContinuousOn f (Icc σ₁ q₁)) (hfσ : f σ₁ = q₂)
    (hfq : f q₁ = σ₂) {t : ℝ≥0} (ht : t ∈ Icc σ₂ q₂) : ∃ u ∈ Icc σ₁ q₁, f u = t := by
  have h := intermediate_value_Icc' hσq hfc
  rw [hfσ, hfq] at h
  exact h ht

/-- The later part of `β` is the common arc. -/
theorem image_Icc_eq (hσq : σ₁ ≤ q₁) (hfc : ContinuousOn f (Icc σ₁ q₁)) (hfa : StrictAntiOn f (Icc σ₁ q₁))
    (hfσ : f σ₁ = q₂) (hfq : f q₁ = σ₂) (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s) :
    β '' Icc σ₂ q₂ = α '' Icc σ₁ q₁ := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_eq_of_mem_Icc hσq hfc hfσ hfq ht
    exact ⟨u, hu, (hfeq u hu).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨f u, ⟨?_, ?_⟩, hfeq u hu⟩
    · rw [← hfq]; exact hfa.antitoneOn hu ⟨hσq, le_rfl⟩ hu.2
    · rw [← hfσ]; exact hfa.antitoneOn ⟨le_rfl, hσq⟩ hu hu.1

/-- The union of the two stopped ranges is the first range and the second one before the common arc. -/
theorem union_eq (hσ₂q : σ₂ ≤ q₂) (hσq : σ₁ ≤ q₁) (hfc : ContinuousOn f (Icc σ₁ q₁))
    (hfa : StrictAntiOn f (Icc σ₁ q₁)) (hfσ : f σ₁ = q₂) (hfq : f q₁ = σ₂)
    (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s) :
    α '' Icc 0 q₁ ∪ β '' Icc 0 q₂ = α '' Icc 0 q₁ ∪ β '' Icc 0 σ₂ := by
  have hsplit : β '' Icc 0 q₂ = β '' Icc 0 σ₂ ∪ β '' Icc σ₂ q₂ := by
    rw [← image_union, Icc_union_Icc_eq_Icc zero_le hσ₂q]
  rw [hsplit, image_Icc_eq hσq hfc hfa hfσ hfq hfeq, ← union_assoc, union_comm (α '' Icc 0 q₁),
    union_assoc, union_eq_left.2 (image_mono (Icc_subset_Icc_left zero_le)), union_comm]

/-- A point of both stopped ranges is on the common arc, at the corresponding parameters. -/
theorem eq_of_mem_both (hp₁ : InjOn α (Icc 0 q₁)) (hp₂ : InjOn β (Icc 0 q₂))
    (hσq : σ₁ ≤ q₁) (hfa : StrictAntiOn f (Icc σ₁ q₁)) (hfσ : f σ₁ = q₂)
    (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s) (hover : α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ ⊆ α '' Icc σ₁ q₁)
    {t t' : ℝ≥0} (ht : t ≤ q₁) (ht' : t' ≤ q₂) (he : α t = β t') : t ∈ Icc σ₁ q₁ ∧ f t = t' := by
  obtain ⟨u, hu, hue⟩ := hover ⟨⟨t, ⟨zero_le, ht⟩, rfl⟩, ⟨t', ⟨zero_le, ht'⟩, he.symm⟩⟩
  have hut : u = t := hp₁ ⟨zero_le, hu.2⟩ ⟨zero_le, ht⟩ hue
  subst hut
  refine ⟨hu, hp₂ ⟨zero_le, ?_⟩ ⟨zero_le, ht'⟩ ((hfeq u hu).trans he)⟩
  rw [← hfσ]
  exact hfa.antitoneOn ⟨le_rfl, hσq⟩ hu hu.1

/-- A point of `ℍ` is in `ℍ` once it is closer to it than its height. -/
theorem mem_H_of_dist_lt {z w : ℂ} (_hz : z ∈ H) (hd : dist z w < z.im) : w ∈ H := by
  show 0 < w.im
  have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  rw [sub_im, ← dist_eq_norm] at h1
  have h3 := le_abs_self (z.im - w.im)
  linarith

/-- **Aux. lemma 69, exposure.** Every point `α(s) ∈ ℍ` of the open common arc (`σ₁ < s < q₁`) is adherent to the
unbounded domain of the union of the two stopped ranges. -/
theorem mem_closure_H_diff_fillH (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    (hq₁ : (q₁ : ℝ≥0∞) ≤ ζ₁) (hq₂ : (q₂ : ℝ≥0∞) ≤ ζ₂) (hσ₂ : 0 < σ₂) (hσ₂q : σ₂ ≤ q₂) (hσq : σ₁ ≤ q₁)
    (hfc : ContinuousOn f (Icc σ₁ q₁)) (hfa : StrictAntiOn f (Icc σ₁ q₁)) (hfσ : f σ₁ = q₂) (hfq : f q₁ = σ₂)
    (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s) (hover : α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ ⊆ α '' Icc σ₁ q₁)
    {s : ℝ≥0} (hs : s ∈ Ioo σ₁ q₁) (hsH : α s ∈ H) :
    α s ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)) := by
  have hc₁ := IsPathGood.continuousOn_Icc hp₁ hq₁
  have hi₁ := IsPathGood.injOn_Icc hp₁ hq₁
  have hc₂ := IsPathGood.continuousOn_Icc hp₂ hq₂
  have hi₂ := IsPathGood.injOn_Icc hp₂ hq₂
  have hα0 : α 0 = x₁ := IsPathGood.zero hp₁
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  have hq₁pos : 0 < q₁ := lt_of_le_of_lt zero_le (hs.1.trans hs.2)
  have hβσ : β σ₂ = α q₁ := by rw [← hfq]; exact hfeq q₁ ⟨hσq, le_rfl⟩
  have hfle : ∀ t ∈ Icc σ₁ q₁, f t ≤ q₂ := fun t ht => by
    rw [← hfσ]; exact hfa.antitoneOn ⟨le_rfl, hσq⟩ ht ht.1
  -- an excursion `α([a, c]) ⊆ ℍ` around `s`
  have hsint : Icc (0 : ℝ≥0) q₁ ∈ 𝓝 s := Icc_mem_nhds (lt_of_le_of_lt zero_le hs.1) hs.2
  have hU : α ⁻¹' H ∩ Ioo σ₁ q₁ ∈ 𝓝 s :=
    inter_mem ((hc₁.continuousAt hsint).preimage_mem_nhds (QuantumZipper.isOpen_H.mem_nhds hsH))
      (isOpen_Ioo.mem_nhds hs)
  obtain ⟨l, u, ⟨hls, hsu⟩, hlu⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨σ₁, hs.1⟩ ⟨q₁, hs.2⟩).1 hU
  obtain ⟨a, hla, has⟩ := exists_between hls
  obtain ⟨c, hsc, hcu⟩ := exists_between hsu
  have hac : Icc a c ⊆ α ⁻¹' H ∩ Ioo σ₁ q₁ := fun t ht => hlu ⟨hla.trans_le ht.1, ht.2.trans_lt hcu⟩
  have hσa : σ₁ < a := (hac ⟨le_rfl, (has.trans hsc).le⟩).2.1
  have hcq : c < q₁ := (hac ⟨(has.trans hsc).le, le_rfl⟩).2.2
  have hsI : s ∈ Icc σ₁ q₁ := Ioo_subset_Icc_self hs
  have hcI : c ∈ Icc σ₁ q₁ := ⟨(hσa.trans (has.trans hsc)).le, hcq.le⟩
  have haI : a ∈ Icc σ₁ q₁ := ⟨hσa.le, (has.trans hs.2).le⟩
  have hfcs : f c < f s := hfa hsI hcI hsc
  -- the two earlier prefixes
  set F := α '' Icc 0 a ∪ β '' Icc 0 (f c) with hF
  have hFdisj : Disjoint (α '' Icc 0 a) (β '' Icc 0 (f c)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ ⟨t', ht', he⟩
    obtain ⟨htI, hft⟩ := eq_of_mem_both hi₁ hi₂ hσq hfa hfσ hfeq hover (ht.2.trans haI.2)
      (ht'.2.trans (hfle c hcI)) he.symm
    have : f c < f t := hfa htI hcI (ht.2.trans_lt (has.trans hsc))
    exact absurd ht'.2 (not_le.2 (hft ▸ this))
  have hcpA := isCompact_Icc.image_of_continuousOn (hc₁.mono (Icc_subset_Icc_right haI.2))
  have hcpB := isCompact_Icc.image_of_continuousOn (hc₂.mono (Icc_subset_Icc_right (hfle c hcI)))
  have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hs.2.le).trans hq₁
  have hfsζ : (f s : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 (hfle s hsI)).trans hq₂
  have hfree : IsFreeAt F (α s) := by
    have h₂ := IsPathGood.isFreeAt_of_lt hp₂ hfcs hfsζ
    rw [hfeq s hsI] at h₂
    exact isFreeAt_union_of_disjoint hcpA hcpB hFdisj (IsPathGood.isFreeAt_of_lt hp₁ has hsζ) h₂
  obtain ⟨ε, hε, hball⟩ := exists_ball_of_isFreeAt hfree
  -- the Jordan curve `Γ ∪ L`
  set Γ := α '' Icc 0 q₁ ∪ β '' Icc 0 σ₂ with hΓdef
  have hΓeq : α '' Icc 0 q₁ ∪ β '' Icc 0 q₂ = Γ := union_eq hσ₂q hσq hfc hfa hfσ hfq hfeq
  have hu₁ : IsArcFrom (segArc α 0 q₁) (x₁ : ℂ) (α q₁) := by
    have := isArcFrom_segArc hq₁pos hc₁ hi₁
    rwa [hα0] at this
  have hu₂ : IsArcFrom (Sec6.arcRev (segArc β 0 σ₂)) (α q₁) (x₂ : ℂ) := by
    have := isArcFrom_segArc hσ₂ (hc₂.mono (Icc_subset_Icc_right hσ₂q)) (hi₂.mono (Icc_subset_Icc_right hσ₂q))
    rw [hβ0, hβσ] at this
    exact isArcFrom_arcRev this
  have hint : arc (segArc α 0 q₁) ∩ arc (Sec6.arcRev (segArc β 0 σ₂)) ⊆ {α q₁} := by
    rw [arc_segArc zero_le, arc_arcRev, arc_segArc zero_le]
    rintro _ ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    obtain ⟨htI, hft⟩ := eq_of_mem_both hi₁ hi₂ hσq hfa hfσ hfeq hover ht.2 (ht'.2.trans hσ₂q) he.symm
    have h1 : σ₂ ≤ t' := by rw [← hft, ← hfq]; exact hfa.antitoneOn htI ⟨hσq, le_rfl⟩ htI.2
    have ht'σ : t' = σ₂ := le_antisymm ht'.2 h1
    rw [mem_singleton_iff, ← hβσ, ← he, ht'σ]
  have hΓarc := isArcFrom_arcJoin hu₁ hu₂ hint
  have harcΓ : arc (Sec6.arcJoin (segArc α 0 q₁) (Sec6.arcRev (segArc β 0 σ₂))) = Γ := by
    rw [arc_arcJoin hu₁ hu₂, arc_segArc zero_le, arc_arcRev, arc_segArc zero_le]
  have hΓim : ∀ w ∈ Γ, 0 ≤ w.im := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 ht.2).trans hq₁)
    · exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 (ht.2.trans hσ₂q)).trans hq₂)
  have hJ : LQGMetric.JordanMap.IsJordanCurve (Γ ∪ lowerArc x₂ x₁) := by
    have := isJordanCurve_arc_union hΓarc (isArcFrom_lowerArcPath hx) ?_
    · rwa [harcΓ] at this
    rw [harcΓ]
    rintro z ⟨hzΓ, hzL⟩
    have h0 := im_le_zero_of_mem_lowerArc hzL
    have him : z.im = 0 := le_antisymm h0.1 (hΓim z hzΓ)
    rcases h0.2 him with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsJ : α s ∈ closure (WangWu.jordanOut (Γ ∪ lowerArc x₂ x₁)) := by
    rw [closure_jordanOut hJ]
    exact Or.inr (Or.inl (Or.inl ⟨s, ⟨zero_le, hs.2.le⟩, rfl⟩))
  -- the closing-curve lemma
  have hFΓ : F ⊆ Γ := union_subset ((image_mono (Icc_subset_Icc_right haI.2)).trans subset_union_left) (fun z hz => by
    obtain ⟨t, ht, rfl⟩ := hz
    rcases le_or_gt t σ₂ with htσ | htσ
    · exact Or.inr ⟨t, ⟨zero_le, htσ⟩, rfl⟩
    · obtain ⟨v, hv, hvt⟩ := exists_eq_of_mem_Icc hσq hfc hfσ hfq ⟨htσ.le, ht.2.trans (hfle c hcI)⟩
      exact Or.inl ⟨v, ⟨zero_le, hv.2⟩, by rw [← hfeq v hv, hvt]⟩)
  have hΓre : ∀ w ∈ Γ, w.im = 0 → w ∈ F := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) h0
    · rcases le_or_gt t a with hta | hta
      · exact Or.inl ⟨t, ⟨zero_le, hta⟩, rfl⟩
      rcases lt_or_ge t c with htc | htc
      · exact absurd h0 (ne_of_gt (hac ⟨hta.le, htc.le⟩).1)
      · have htI : t ∈ Icc σ₁ q₁ := ⟨hcI.1.trans htc, ht.2⟩
        refine Or.inr ⟨f t, ⟨zero_le, hfa.antitoneOn hcI htI htc⟩, hfeq t htI⟩
    · refine Or.inr ⟨t, ⟨zero_le, ht.2.trans ?_⟩, rfl⟩
      rw [← hfq]
      exact hfa.antitoneOn hcI ⟨hσq, le_rfl⟩ hcq.le
  have hFL : IsPreconnected (F ∪ lowerArc x₂ x₁) := by
    have hA : IsPreconnected (α '' Icc 0 a) := isPreconnected_Icc.image _ (hc₁.mono (Icc_subset_Icc_right haI.2))
    have hB : IsPreconnected (β '' Icc 0 (f c)) :=
      isPreconnected_Icc.image _ (hc₂.mono (Icc_subset_Icc_right (hfle c hcI)))
    have hx₁A : (x₁ : ℂ) ∈ α '' Icc 0 a := ⟨0, ⟨le_rfl, zero_le⟩, hα0⟩
    have hx₂B : (x₂ : ℂ) ∈ β '' Icc 0 (f c) := ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩
    have h1 := hA.union (x₁ : ℂ) hx₁A (left_mem_lowerArc (x₂ := x₂)) isPreconnected_lowerArc
    have h2 := h1.union (x₂ : ℂ) (Or.inr (right_mem_lowerArc (x₁ := x₁))) hx₂B hB
    have he : α '' Icc 0 a ∪ lowerArc x₂ x₁ ∪ β '' Icc 0 (f c) = F ∪ lowerArc x₂ x₁ := by
      rw [hF, union_right_comm]
    rwa [he] at h2
  have hcpΓ : IsCompact Γ :=
    (isCompact_Icc.image_of_continuousOn hc₁).union
      (isCompact_Icc.image_of_continuousOn (hc₂.mono (Icc_subset_Icc_right hσ₂q)))
  rw [hΓeq, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨z, hzJ, hzd⟩ := Metric.mem_closure_iff.1 hsJ (min δ (min ε (α s).im)) (lt_min hδ (lt_min hε hsH))
  have hzH : z ∈ H := mem_H_of_dist_lt hsH (hzd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hzF : z ∈ H \ fillH F :=
    hball z (mem_ball.2 (by rw [dist_comm]; exact hzd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))) hzH
  refine ⟨z, ?_, hzd.trans_le (min_le_left _ _)⟩
  exact mem_H_diff_fillH_of_mem_jordanOut_closing (hcpA.union hcpB) hcpΓ isCompact_lowerArc hFΓ hΓim hΓre
    (fun w hw => (im_le_zero_of_mem_lowerArc hw).1) hFL hzF hzJ

end ReverseArc

end Sec7

end InteractingSLE
