/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Sep

/-!
# Lemma 7.7: the forbidden-side witness and confinement at an interior contact

Packet PROVE-LEMMA77 (specification §7.2, Aux. lemmas 74–75, pp. 279–282, `source/spec/p241-288.md#aux-74`).

* `exists_not_firstExitBarrier_of_inside` (the witness of Aux. lemmas 72 and 74): if the second path `β` arrives at
  an interior point `α(u₀) = β(e)` of the first path while the onward first path `α((u₀, v₀])` lies inside the
  closing Jordan curve `α([0, u₀]) ∪ β([0, e]) ∪ L`, and the paths do not meet before, then for every pair of stops
  `r ∈ (u₀, r₀)`, `t ∈ (t₀, e)` the pathwise conclusion of Lemma 7.6 (`FirstExitBarrier`) fails: "its next exit from
  the joint unbounded component is at `w`, through the right side of the frozen first prefix at the strictly earlier
  first-path parameter" (Aux. lemma 74).
* `forall_isFreeAt_of_barrier` (Aux. lemma 75 at an interior contact): at a common first contact `w = α(a) = β(b)`
  in `ℍ`, if Lemma 7.6's conclusion holds at every pair of rational stops, every continuation point `α(s)`,
  `a < s ≤ ζ`, is free for `K = α([0, a]) ∪ β([0, b])`. The proof: the continuation avoids `K` (Aux. lemma 73), so
  it is free throughout or trapped throughout ("A continuous continuation avoiding `K` can belong to the closure of
  only one component", p. 281); if trapped, near `w` it lies inside the closing Jordan curve
  (`mem_H_diff_fillH_of_mem_jordanOut_closing`), which is the forbidden configuration.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart

/-! ### Small helpers -/

theorem exists_rat_toNNReal_btwn {a b : ℝ≥0} (h : a < b) :
    ∃ q : ℚ, a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal < b := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show (a : ℝ) < b from h)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg a).trans hq₁.le
  refine ⟨q, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq₁
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq₂

/-- Left continuity at a parameter, as a closed parameter interval mapped into a ball. -/
theorem exists_lt_forall_Icc_mem_ball {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    (hc : ContinuousOn η {s | (s : ℝ≥0∞) ≤ ζ}) {e : ℝ≥0} (he : (e : ℝ≥0∞) ≤ ζ) (he0 : 0 < e) {ε : ℝ}
    (hε : 0 < ε) : ∃ t₀ < e, η '' Icc t₀ e ⊆ ball (η e) ε := by
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 (hc e he) ε hε
  set t₀ : ℝ≥0 := e - (δ / 2).toNNReal with ht₀
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have ht₀e : t₀ < e := tsub_lt_self he0 (Real.toNNReal_pos.2 hδ2)
  refine ⟨t₀, ht₀e, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hs.2).trans he
  refine hδε hsζ ?_
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hs.2))]
  have h1 : ((e : ℝ) - δ / 2) ≤ s := by
    have := NNReal.coe_le_coe.2 hs.1
    rw [ht₀, NNReal.coe_sub_def] at this
    have h2 : ((e : ℝ) - ((δ / 2).toNNReal : ℝ)) ≤ max ((e : ℝ) - ((δ / 2).toNNReal : ℝ)) 0 := le_max_left _ _
    rw [Real.coe_toNNReal _ hδ2.le] at h2 this
    linarith
  linarith

/-- Right continuity at a parameter before the lifetime. -/
theorem exists_gt_forall_Icc_mem_ball {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    (hc : ContinuousOn η {s | (s : ℝ≥0∞) ≤ ζ}) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v₀ : ℝ≥0, a < v₀ ∧ (v₀ : ℝ≥0∞) ≤ ζ ∧ η '' Icc a v₀ ⊆ ball (η a) ε := by
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 (hc a ha.le) ε hε
  obtain ⟨c, hac, hcζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
  have hac' : a < c := ENNReal.coe_lt_coe.1 hac
  set v₀ : ℝ≥0 := min (a + (δ / 2).toNNReal) c with hv₀
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  refine ⟨v₀, lt_min (lt_add_of_pos_right _ (Real.toNNReal_pos.2 hδ2)) hac',
    (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hcζ.le, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsζ : (s : ℝ≥0∞) ≤ ζ :=
    (ENNReal.coe_le_coe.2 (hs.2.trans (min_le_right _ _))).trans hcζ.le
  refine hδε hsζ ?_
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hs.1))]
  have h1 : (s : ℝ) ≤ a + δ / 2 := by
    have := NNReal.coe_le_coe.2 (hs.2.trans (min_le_left _ _))
    rw [NNReal.coe_add, Real.coe_toNNReal _ hδ2.le] at this
    exact this
  linarith

/-- A free point of `ℍ̄` is adherent to the unbounded domain. -/
theorem mem_closure_H_diff_fillH_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) (hz : 0 ≤ z.im) :
    z ∈ closure (H \ fillH F) := by
  obtain ⟨ε, hε, hball⟩ := hf
  rw [Metric.mem_closure_iff]
  intro e he
  set δ : ℝ := min ε e / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by rw [hδ]; linarith [min_le_left ε e]
  have hδe : δ < e := by rw [hδ]; linarith [min_le_right ε e]
  have hdist : dist z (z + (δ : ℂ) * I) = δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
  refine ⟨z + (δ : ℂ) * I, hball ⟨?_, ?_⟩, by rw [hdist]; exact hδe⟩
  · rw [mem_ball, dist_comm, hdist]; exact hδε
  · show 0 < (z + (δ : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith

theorem ne_zero_of_mem_H {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) {s : ℝ≥0}
    (hs : η s ∈ H) : s ≠ 0 := by
  rintro rfl
  rw [IsPathGood.zero hp] at hs
  exact absurd hs (by simp [QuantumZipper.H])

/-! ### The forbidden-side witness -/

/-- **The forbidden-side witness** (Aux. lemmas 72 and 74). If `β` arrives at the interior point `α(u₀) = β(e)`
while `α((u₀, v₀])` lies inside the closing Jordan curve, and `α|[0, v₀)`, `β|[0, e)` are disjoint, then Lemma 7.6's
pathwise conclusion fails for every pair of stops near `(u₀⁺, e⁻)`. -/
theorem exists_not_firstExitBarrier_of_inside {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {L : Set ℂ} {u₀ v₀ e : ℝ≥0}
    (huv : u₀ < v₀) (hv₀ : (v₀ : ℝ≥0∞) ≤ ζα) (he : (e : ℝ≥0∞) ≤ ζβ) (hp : α u₀ = β e)
    (hpH : α u₀ ∈ H)
    (hin : ∀ v ∈ Ioc u₀ v₀, α v ∈ WangWu.jordanIn (α '' Icc 0 u₀ ∪ β '' Icc 0 e ∪ L))
    (hdisj : ∀ s t : ℝ≥0, s < v₀ → t < e → α s ≠ β t) :
    ∃ r₀ t₀ : ℝ≥0, u₀ < r₀ ∧ t₀ < e ∧ ∀ r t : ℝ≥0, u₀ < r → r < r₀ → t₀ < t → t < e →
      ¬ FirstExitBarrier α (truncAt ζα r) β ζβ (truncAt ζβ t) L := by
  set w := α u₀ with hw
  obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.1 QuantumZipper.isOpen_H w hpH
  have hu₀ζ : (u₀ : ℝ≥0∞) < ζα := (ENNReal.coe_lt_coe.2 huv).trans_le hv₀
  have hu₀0 : 0 < u₀ := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpα hpH)
  have he0 : 0 < e := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpβ (hp ▸ hpH))
  obtain ⟨u', hu', hu'ball⟩ := exists_lt_forall_Icc_mem_ball hpα.continuousOn hu₀ζ.le hu₀0 hρ
  obtain ⟨v₁, hv₁, hv₁ζ, hv₁ball⟩ := exists_gt_forall_Icc_mem_ball hpα.continuousOn hu₀ζ hρ
  obtain ⟨ε, hε, hslit⟩ := IsPathGood.exists_ball_mem_H_diff_fillH hpα hu' hu₀ζ.le
  obtain ⟨t₀, ht₀, ht₀ball⟩ := exists_lt_forall_Icc_mem_ball hpβ.continuousOn he he0
    (lt_min hε hρ)
  refine ⟨min v₀ v₁, t₀, lt_min huv hv₁, ht₀, fun r t hur hrr₀ ht₀t hte hbar => ?_⟩
  have hrv₀ : r < v₀ := hrr₀.trans_le (min_le_left _ _)
  have hrv₁ : r < v₁ := hrr₀.trans_le (min_le_right _ _)
  have hrζ : (r : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hrv₀.le).trans hv₀
  have htζ : (t : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 hte.le).trans he
  rw [truncAt_of_le hrζ, truncAt_of_le htζ] at hbar
  -- the first path near `w` stays in `ℍ`
  have hαH : α '' Icc u' r ⊆ H := by
    rintro _ ⟨s, hs, rfl⟩
    rcases le_total s u₀ with h | h
    · exact hρH (hu'ball ⟨s, ⟨hs.1, h⟩, rfl⟩)
    · exact hρH (hv₁ball ⟨s, ⟨h, hs.2.trans hrv₁.le⟩, rfl⟩)
  -- the second path near `w`
  have hβnear : ∀ s ∈ Icc t e, β s ∈ ball w ε ∧ β s ∈ H := by
    intro s hs
    have h := ht₀ball ⟨s, ⟨ht₀t.le.trans hs.1, hs.2⟩, rfl⟩
    rw [← hp] at h
    exact ⟨ball_subset_ball (min_le_left _ _) h, hρH (ball_subset_ball (min_le_right _ _) h)⟩
  have hβoff : ∀ s, s < e → β s ∉ α '' Icc 0 r := by
    rintro s hs ⟨q, hq, hqs⟩
    exact hdisj q s (hq.2.trans_lt hrv₀) hs hqs
  have hβfree : ∀ s ∈ Ico t e, β s ∈ H \ fillH (α '' Icc 0 r) := fun s hs =>
    hslit r hur.le hrζ hαH _ (hβnear s ⟨hs.1, hs.2.le⟩).1 (hβnear s ⟨hs.1, hs.2.le⟩).2 (hβoff s hs.2)
  have hD : Disjoint (α '' Icc 0 r) (β '' Icc 0 t) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', hqq'⟩
    exact hdisj q q' (hq.2.trans_lt hrv₀) (hq'.2.trans_lt hte) hqq'.symm
  have hcα : IsCompact (α '' Icc 0 r) := IsPathGood.isCompact_image hpα hrζ
  have hcβ : IsCompact (β '' Icc 0 t) := IsPathGood.isCompact_image hpβ htζ
  refine hbar hD (mem_unboundedPart_of_mem_H_diff_fillH hcα.isClosed (hβfree t ⟨le_rfl, hte⟩)) e u₀ r he
    ⟨hte, hur, le_rfl, fun s hs => ?_, hp.symm, hin r ⟨hur, hrv₀.le⟩⟩
  have hsH := (hβnear s ⟨hs.1.le, hs.2.le⟩).2
  have h₂ : β s ∈ H \ fillH (β '' Icc 0 t) := IsPathGood.mem_H_diff_fillH_of_lt hpβ hs.1
    ((ENNReal.coe_le_coe.2 hs.2.le).trans he) hsH
  exact mem_unboundedPart_of_mem_H_diff_fillH (hcα.union hcβ).isClosed
    (mem_H_diff_fillH_union_of_disjoint hcα hcβ hD (hβfree s ⟨hs.1.le, hs.2⟩) h₂)

/-- The countable form: Lemma 7.6's conclusion at every pair of rational stops excludes the inside configuration. -/
theorem false_of_inside {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {L : Set ℂ} {u₀ v₀ e : ℝ≥0}
    (huv : u₀ < v₀) (hv₀ : (v₀ : ℝ≥0∞) ≤ ζα) (he : (e : ℝ≥0∞) ≤ ζβ) (hp : α u₀ = β e)
    (hpH : α u₀ ∈ H)
    (hin : ∀ v ∈ Ioc u₀ v₀, α v ∈ WangWu.jordanIn (α '' Icc 0 u₀ ∪ β '' Icc 0 e ∪ L))
    (hdisj : ∀ s t : ℝ≥0, s < v₀ → t < e → α s ≠ β t)
    (hbar : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζα (q : ℝ).toNNReal) β ζβ (truncAt ζβ (q' : ℝ).toNNReal) L) :
    False := by
  obtain ⟨r₀, t₀, hr₀, ht₀, hno⟩ := exists_not_firstExitBarrier_of_inside hpα hpβ huv hv₀ he hp hpH hin hdisj
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_toNNReal_btwn hr₀
  obtain ⟨q', hq₁', hq₂'⟩ := exists_rat_toNNReal_btwn ht₀
  exact hno _ _ hq₁ hq₂ hq₁' hq₂' (hbar q q')

/-! ### Confinement at an interior common first contact -/

/-- **Aux. lemma 75 at an interior contact.** At a common first contact `w = α(a) = β(b) ∈ ℍ` of two good paths, if
Lemma 7.6's conclusion holds at every pair of rational stops, every continuation point `α(s)`, `a < s ≤ ζα`, is free
for the joint prefix `K = α([0, a]) ∪ β([0, b])`. -/
theorem forall_isFreeAt_of_barrier {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ}
    (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ) {L : Set ℂ} (hLc : IsCompact L)
    (hLpc : IsPreconnected L) (hLim : ∀ z ∈ L, z.im ≤ 0) (hxα : (xα : ℂ) ∈ L) (hxβ : (xβ : ℂ) ∈ L)
    {a b : ℝ≥0} (hfc : IsFirstContact α ζα β ζβ a b) (hwH : α a ∈ H)
    (hbar : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζα (q : ℝ).toNNReal) β ζβ (truncAt ζβ (q' : ℝ).toNNReal) L) :
    ∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ ζα → IsFreeAt (α '' Icc 0 a ∪ β '' Icc 0 b) (α s) := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := hfc
  set K := α '' Icc 0 a ∪ β '' Icc 0 b with hK
  set w := α a with hw
  have hcK : IsCompact K := (IsPathGood.isCompact_image hpα haζ).union (IsPathGood.isCompact_image hpβ hbζ)
  have hret := (no_return_of_firstContact hpα.1 hpβ.1 haζ hbζ hab hmin).1
  -- the continuation is free throughout or trapped throughout
  set X := α '' {s : ℝ≥0 | a < s ∧ (s : ℝ≥0∞) ≤ ζα} with hX
  have hXpc : IsPreconnected X := by
    refine IsPreconnected.image ?_ _ (hpα.continuousOn.mono fun s hs => hs.2)
    refine OrdConnected.isPreconnected ⟨fun x hx y hy z hz => ⟨hx.1.trans_le hz.1, ?_⟩⟩
    exact (ENNReal.coe_le_coe.2 hz.2).trans hy.2
  have hXK : X ⊆ {z : ℂ | 0 ≤ z.im} \ K := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨IsPathGood.im_nonneg hpα hs.2, hret s hs.1 hs.2⟩
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hcK.isClosed hXpc hXK with hfree | htrap
  · exact fun s hs hsζ => hfree _ ⟨s, ⟨hs, hsζ⟩, rfl⟩
  intro s₁ hs₁ hs₁ζ
  exfalso
  have haζ' : (a : ℝ≥0∞) < ζα := (ENNReal.coe_lt_coe.2 hs₁).trans_le hs₁ζ
  obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.1 QuantumZipper.isOpen_H w hwH
  have ha0 : 0 < a := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpα hwH)
  have hb0 : 0 < b := pos_iff_ne_zero.2 (ne_zero_of_mem_H hpβ (hab ▸ hwH))
  obtain ⟨s', hs', hs'ball⟩ := exists_lt_forall_Icc_mem_ball hpα.continuousOn haζ ha0 hρ
  obtain ⟨t', ht', ht'ball⟩ := exists_lt_forall_Icc_mem_ball hpβ.continuousOn hbζ hb0 hρ
  rw [← hab] at ht'ball
  set F := α '' Icc 0 s' ∪ β '' Icc 0 t' with hF
  have hs'ζ : (s' : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hs'.le).trans haζ
  have ht'ζ : (t' : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 ht'.le).trans hbζ
  have hcF₁ : IsCompact (α '' Icc 0 s') := IsPathGood.isCompact_image hpα hs'ζ
  have hcF₂ : IsCompact (β '' Icc 0 t') := IsPathGood.isCompact_image hpβ ht'ζ
  have hdF : Disjoint (α '' Icc 0 s') (β '' Icc 0 t') := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', hqq'⟩
    have := (hmin q q' ((ENNReal.coe_le_coe.2 hq.2).trans hs'ζ) ((ENNReal.coe_le_coe.2 hq'.2).trans ht'ζ)
      hqq'.symm).1
    exact absurd (this.trans hq.2) (not_le.2 hs')
  have hfF : IsFreeAt F w := by
    refine isFreeAt_union_of_disjoint hcF₁ hcF₂ hdF (IsPathGood.isFreeAt_of_lt hpα hs' haζ) ?_
    have h2 := IsPathGood.isFreeAt_of_lt hpβ ht' hbζ
    rw [← (show α a = β b from hab)] at h2
    exact h2
  obtain ⟨ε₁, hε₁, hball₁⟩ := exists_ball_of_isFreeAt hfF
  obtain ⟨v₀, hv₀, hv₀ζ, hv₀ball⟩ := exists_gt_forall_Icc_mem_ball hpα.continuousOn haζ' (lt_min hε₁ hρ)
  -- near `w`, the trapped continuation is inside the closing Jordan curve
  have hin : ∀ v ∈ Ioc a v₀, α v ∈ WangWu.jordanIn (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L) := by
    intro v hv
    have hvball := hv₀ball ⟨v, ⟨hv.1.le, hv.2⟩, rfl⟩
    have hvH : α v ∈ H := hρH (ball_subset_ball (min_le_right _ _) hvball)
    have hvF : α v ∈ H \ fillH F := hball₁ _ (ball_subset_ball (min_le_left _ _) hvball) hvH
    have hvζ : (v : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hv.2).trans hv₀ζ
    have hvtrap := htrap _ ⟨v, ⟨hv.1, hvζ⟩, rfl⟩
    have hvK : α v ∉ K ∪ L := by
      rintro (h | h)
      · exact hret v hv.1 hvζ h
      · exact absurd (hLim _ h) (not_le.2 hvH)
    refine Foundations.ThetaCurve.mem_jordanIn_of_not_mem_jordanOut hvK fun hout => ?_
    refine hvtrap.notMem (mem_H_diff_fillH_of_mem_jordanOut_closing (hcF₁.union hcF₂) hcK hLc
      (union_subset_union (image_mono (Icc_subset_Icc_right hs'.le))
        (image_mono (Icc_subset_Icc_right ht'.le))) ?_ ?_ hLim ?_ hvF hout)
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
      have he : F ∪ L = α '' Icc 0 s' ∪ L ∪ β '' Icc 0 t' := by
        rw [hF]; ext z; simp only [mem_union]; tauto
      rw [he]; exact h₂
  have hdisj : ∀ s t : ℝ≥0, s < v₀ → t < b → α s ≠ β t := fun s t hs ht hst => by
    have := (hmin s t ((ENNReal.coe_le_coe.2 hs.le).trans hv₀ζ) ((ENNReal.coe_le_coe.2 ht.le).trans hbζ)
      hst).2
    exact absurd this (not_le.2 ht)
  exact false_of_inside hpα hpβ hv₀ hv₀ζ hbζ hab hwH hin hdisj hbar

end Sec7

end InteractingSLE
