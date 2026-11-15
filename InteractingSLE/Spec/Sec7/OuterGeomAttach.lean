/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterInGeom

/-!
# Theorem R.7's outer pockets: Aux. lemma 37 along a clipped certified frontier

Packet PROVE-R7-OUTERGEOM. In a pocket whose two arms are outer (§5.3–§5.4, Lemma R.3), the attachment barrier of
STOPIN's erasure is the clipped certified frontier `β_R` between the pocket's corners. Its first-visit (resp.
last-visit) attachment cannot progress on a time interval avoiding the pocket, pathwise:

* a barrier point first visited during `(a, b]` is not in the open pocket `C` but in its closure, hence on
  `frontier C` (`mem_frontier_of_new_visit`); reverse first-visit order and closedness of the visited set turn one new
  point into a nontrivial parameter interval of new points (`visited_eq_of_noArc`, `visitedInf_eq_of_noArc`);
* `frontier C` lies on the two walls, and a nontrivial time interval of the middle curve on the union of two walls
  contradicts `NoCommonArc` with one of them (Baire on two closed sets, `exists_subinterval_of_union`,
  `false_of_interval_union`) — the source's "distinct angles share no open subarc" (p. 473, Lemma R.3).

Main results: **`outerOuterAttach`** (`OuterIn.OuterOuterAttach`, every clipping) and **`outerOuterAttachInf`**
(`OuterIn.OuterOuterAttachInf`), from the pocket configuration, the reverse visits and visits of `β_R`, and
`NoCommonArc` of `β_R` with both walls. No field input is used.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.OuterGeom

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

section Abstract

variable {η : ℝ → ℂ} {C K : Set ℂ} {B : ℝ → ℂ}

/-- The visited parameters of a barrier at time `a` form a closed set. -/
theorem isClosed_visited {I : Set ℝ} (hI : IsClosed I) (hηc : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B I)
    (a : ℝ) : IsClosed {v ∈ I | B v ∈ η '' Icc 0 a} :=
  hBc.preimage_isClosed_of_isClosed hI
    ((isCompact_Icc.image_of_continuousOn (hηc.mono Icc_subset_Ici_self)).isClosed)

/-- A barrier point first visited during `(a, b]`, `η` avoiding the open `C` on `[a, b]`, lies on `frontier C` when
it lies in `closure C`. -/
theorem mem_frontier_of_new_visit (hC : IsOpen C) {a b : ℝ} (havoid : ∀ t ∈ Icc a b, η t ∉ C) {z : ℂ}
    (hzb : z ∈ η '' Icc 0 b) (hza : z ∉ η '' Icc 0 a) (hzc : z ∈ closure C) : z ∈ frontier C := by
  obtain ⟨t, ht, rfl⟩ := hzb
  have hta : a < t := lt_of_not_ge fun h => hza ⟨t, ⟨ht.1, h⟩, rfl⟩
  refine ⟨hzc, ?_⟩
  rw [hC.interior_eq]
  exact havoid t ⟨hta.le, ht.2⟩

/-- **No attachment progress through the frontier (bounded barrier)**: if the barrier `B : [0, 1] → closure C` is
visited in reverse first-visit order, `B 1` is visited by time `a`, and no nontrivial parameter interval of `B` lies
in a set `K ⊇ frontier C`, then on an interval `[a, b]` avoiding `C` no new barrier point is visited. -/
theorem visited_eq_of_noArc (hηc : ContinuousOn η (Ici 0)) (hC : IsOpen C) (hBc : ContinuousOn B (Icc 0 1))
    (hBcl : ∀ v ∈ Icc (0 : ℝ) 1, B v ∈ closure C) (hfr : frontier C ⊆ K)
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hno : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → ¬ B '' Icc c d ⊆ K) {a b : ℝ} (hab : a ≤ b)
    (h1 : B 1 ∈ η '' Icc 0 a) (havoid : ∀ t ∈ Icc a b, η t ∉ C) :
    {v ∈ Icc (0 : ℝ) 1 | B v ∈ η '' Icc 0 b} = {v ∈ Icc (0 : ℝ) 1 | B v ∈ η '' Icc 0 a} := by
  have hmono : η '' Icc 0 a ⊆ η '' Icc 0 b := image_mono (Icc_subset_Icc_right hab)
  refine Subset.antisymm (fun v hv => ?_) fun v hv => ⟨hv.1, hmono hv.2⟩
  by_contra hva
  have hcl := isClosed_visited isClosed_Icc hηc hBc a
  have hv1 : v < 1 := lt_of_le_of_ne hv.1.2 fun he => hva ⟨hv.1, he ▸ h1⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v hva
  set d := min (v + ε / 2) 1 with hd
  have hvd : v < d := lt_min (by linarith) hv1
  refine hno v d hv.1.1 hvd (min_le_right _ _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw01 : w ∈ Icc (0 : ℝ) 1 := ⟨hv.1.1.trans hw.1, hw.2.trans (min_le_right _ _)⟩
  have hwb : B w ∈ η '' Icc 0 b := hrev b v hv.1 w hw01 hw.1 hv.2
  have hwa : B w ∉ η '' Icc 0 a := fun h => by
    refine hball ?_ ⟨hw01, h⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2, min_le_left (v + ε / 2) 1]
  exact hfr (mem_frontier_of_new_visit hC havoid hwb hwa (hBcl w hw01))

/-- **No attachment progress through the frontier (barrier to infinity)**: the analogue of `visited_eq_of_noArc` for
a barrier `B : [0, ∞) → closure C` in reverse first-visit order at infinity, with `B 0` visited by time `a`. -/
theorem visitedInf_eq_of_noArc (hηc : ContinuousOn η (Ici 0)) (hC : IsOpen C) (hBc : ContinuousOn B (Ici 0))
    (hBcl : ∀ v ∈ Ici (0 : ℝ), B v ∈ closure C) (hfr : frontier C ⊆ K)
    (hrev : IsReverseVisitOrderInf B fun t => η '' Icc 0 t)
    (hno : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ B '' Icc c d ⊆ K) {a b : ℝ} (hab : a ≤ b)
    (h0 : B 0 ∈ η '' Icc 0 a) (havoid : ∀ t ∈ Icc a b, η t ∉ C) :
    {v ∈ Ici (0 : ℝ) | B v ∈ η '' Icc 0 b} = {v ∈ Ici (0 : ℝ) | B v ∈ η '' Icc 0 a} := by
  have hmono : η '' Icc 0 a ⊆ η '' Icc 0 b := image_mono (Icc_subset_Icc_right hab)
  refine Subset.antisymm (fun v hv => ?_) fun v hv => ⟨hv.1, hmono hv.2⟩
  by_contra hva
  have hcl := isClosed_visited isClosed_Ici hηc hBc a
  have hv0 : 0 < v := lt_of_le_of_ne hv.1 fun he => hva ⟨hv.1, he ▸ h0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl v hva
  set c := max (v - ε / 2) 0 with hc
  have hcv : c < v := max_lt (by linarith) hv0
  refine hno c v (le_max_right _ _) hcv ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw0 : w ∈ Ici (0 : ℝ) := (le_max_right _ _).trans hw.1
  have hwb : B w ∈ η '' Icc 0 b := hrev b w hw0 v hv.1 hw.2 hv.2
  have hwa : B w ∉ η '' Icc 0 a := fun h => by
    refine hball ?_ ⟨hw0, h⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2, le_max_left (v - ε / 2) 0]
  exact hfr (mem_frontier_of_new_visit hC havoid hwb hwa (hBcl w hw0))

/-- **A nontrivial interval in the union of two closed sets has a nontrivial subinterval in one of them.** -/
theorem exists_subinterval_of_union {f : ℝ → ℂ} {K₁ K₂ : Set ℂ} (hK₁ : IsClosed K₁) {c d : ℝ} (hcd : c < d)
    (hf : ContinuousOn f (Icc c d)) (hsub : f '' Icc c d ⊆ K₁ ∪ K₂) :
    f '' Icc c d ⊆ K₁ ∨ ∃ c' d', c ≤ c' ∧ c' < d' ∧ d' ≤ d ∧ f '' Icc c' d' ⊆ K₂ := by
  by_cases hall : f '' Icc c d ⊆ K₁
  · exact Or.inl hall
  right
  obtain ⟨_, ⟨w, hw, rfl⟩, hwK⟩ := not_subset.1 hall
  have hopen : IsOpen K₁ᶜ := hK₁.isOpen_compl
  have hcw : ContinuousWithinAt f (Icc c d) w := hf w hw
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hcw (hopen.mem_nhds hwK))
  set c' := max c (w - ε / 2)
  set d' := min d (w + ε / 2)
  have hc'd' : c' < d' := by
    rcases lt_or_ge w d with hwd | hwd
    · exact (max_le hw.1 (by linarith)).trans_lt (lt_min hwd (by linarith))
    · exact (max_lt (hcd.trans_le hwd) (by linarith)).trans_le (le_min hw.2 (by linarith))
  refine ⟨c', d', le_max_left _ _, hc'd', min_le_left _ _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxI : x ∈ Icc c d := ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  have hxb : x ∈ ball w ε := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, le_max_right c (w - ε / 2), min_le_right d (w + ε / 2)]
  have := hball ⟨hxb, hxI⟩
  exact (hsub ⟨x, hxI, rfl⟩).resolve_left this

end Abstract

section Arcs

variable {R M L X : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- A disc point of a simple proper curve off the open disc times maps to `0` in the counterflow chart. -/
theorem cfPt_toDisc_eq_zero (hX : IsSimpleProper X) {p : ℝ} (hp : p ∉ Ioo (0 : ℝ) 1) :
    cfPt (toDisc (Lemma71I.realPath X) p) = 0 := by
  rcases le_or_gt 1 p with h1 | h1
  · have : toDisc (Lemma71I.realPath X) p = 1 := by simp [toDisc, not_lt.2 h1]
    rw [this, cfPt_one]
  · have hp0 : p ≤ 0 := by
      by_contra h0
      exact hp ⟨lt_of_not_ge h0, h1⟩
    have ha : arcTime p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp0 (by linarith)
    have hz : Lemma71I.realPath X (arcTime p) = 0 := by
      simp only [Lemma71I.realPath, Real.toNNReal_of_nonpos ha]
      exact hX.2.2.1
    rw [toDisc_of_lt h1, hz, WangWu.cayley_zero]
    simp [cfPt, QuantumZipper.CA.cayleyInv]

/-- **A counterflow-chart point of a wall in `ℍ` is the image of a point of the wall.** -/
theorem mem_range_of_cfPt_toDisc (hX : IsSimpleProper X) {p : ℝ} {z : ℂ} (hz : z ∈ H)
    (he : cfPt (toDisc (Lemma71I.realPath X) p) = negInv z) : z ∈ range X := by
  by_cases hp : p ∈ Ioo (0 : ℝ) 1
  · obtain ⟨e, -⟩ := cfPt_toDisc_of_mem hX hp
    rw [e] at he
    refine ⟨(arcTime p).toNNReal, ?_⟩
    rw [← WangWu.negInv_negInv' z, ← he, WangWu.negInv_negInv']
  · rw [cfPt_toDisc_eq_zero hX hp] at he
    have h' : negInv z ∈ H := Sec7.StripSysField.negInv_mem_H hz
    rw [← he] at h'
    exact absurd (show (0 : ℝ) < (0 : ℂ).im from h') (lt_irrefl _)

/-- `NoCommonArc` on a real time interval: no nontrivial interval of positive times of `M` lies on `X`. -/
theorem false_of_interval_range (hcX : NoCommonArc M X) {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (h : ∀ t ∈ Icc c d, M t.toNNReal ∈ range X) : False := by
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn hcd
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn hq₁b
  obtain ⟨t, ht₁, ht₂, htX⟩ := hcX q₁ q₂ (by exact_mod_cast hc.trans hq₁a) (by exact_mod_cast hq₂a)
  have := h t ⟨hq₁a.le.trans ht₁, ht₂.trans hq₂b.le⟩
  rw [Real.toNNReal_coe] at this
  exact htX this

/-- **No nontrivial time interval of a middle curve lies on the union of the two walls** (Lemma R.3: distinct angles
share no open subarc). -/
theorem false_of_interval_union (hR : IsSimpleProper R) (hM : IsSimpleProper M)
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂)
    (h : ∀ t ∈ Icc t₁ t₂, M t.toNNReal ∈ range R ∪ range L) : False := by
  have hcont : ContinuousOn (fun t : ℝ => M t.toNNReal) (Icc t₁ t₂) :=
    (hM.1.comp continuous_real_toNNReal).continuousOn
  rcases exists_subinterval_of_union (Sec7.Lemma71Pin.IsSimpleProper.isClosed_range hR) ht hcont
      (by rintro _ ⟨t, htI, rfl⟩; exact h t htI) with hall | ⟨c', d', hc', hcd', -, hsub⟩
  · exact false_of_interval_range hcR ht₁ ht fun t htI => hall ⟨t, htI, rfl⟩
  · exact false_of_interval_range hcL (ht₁.trans_le hc') hcd' fun t htI => hsub ⟨t, htI, rfl⟩

/-- A positive time of a simple proper curve read through `toDisc` at its disc time. -/
theorem cfPt_toDisc_discTime (hM : IsSimpleProper M) {t : ℝ} (ht : 0 < t) :
    cfPt (toDisc (Lemma71I.realPath M) (discTime t)) = negInv (M t.toNNReal) := by
  have hMH : M t.toNNReal ∈ H := hM.2.2.2.1 _ (Real.toNNReal_pos.2 ht)
  rw [toDisc_discTime _ ht.le]
  exact cfPt_cayley (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH)

theorem discTime_le_discTime {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') : discTime t ≤ discTime t' := by
  rcases htt'.lt_or_eq with h | h
  · exact (discTime_lt_discTime ht h).le
  · rw [h]

/-- **A parameter interval of the clipped arc covers a time interval of the middle curve.** -/
theorem exists_interval_midArc (hM : IsSimpleProper M) {σM τM : ℝ} (hσ : 0 < σM) (hστ : σM < τM) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c < d) (hd : σM + d * (τM - σM) ≤ 1) :
    ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < t₂ ∧
      ∀ t ∈ Icc t₁ t₂, ∃ v ∈ Icc c d, midArc M σM τM v = negInv (M t.toNNReal) := by
  have hΔ : 0 < τM - σM := sub_pos.2 hστ
  set e : ℝ := (c + d) / 2 with he
  have hce : c < e := by rw [he]; linarith
  have hed : e < d := by rw [he]; linarith
  set s₁ := σM + c * (τM - σM) with hs₁
  set s₂ := σM + e * (τM - σM) with hs₂
  have hs₁pos : 0 < s₁ := by have := mul_nonneg hc hΔ.le; linarith
  have hs₁₂ : s₁ < s₂ := by have := mul_lt_mul_of_pos_right hce hΔ; linarith
  have hs₂1 : s₂ < 1 := by have := mul_lt_mul_of_pos_right hed hΔ; linarith
  have hT₁ : 0 < arcTime s₁ := arcTime_pos ⟨hs₁pos, hs₁₂.trans hs₂1⟩
  have hT₁₂ : arcTime s₁ < arcTime s₂ := by
    by_contra hle
    have h' := discTime_le_discTime (arcTime_pos ⟨hs₁pos.trans hs₁₂, hs₂1⟩).le (not_lt.1 hle)
    rw [discTime_arcTime (hs₁₂.trans hs₂1), discTime_arcTime hs₂1] at h'
    linarith
  refine ⟨arcTime s₁, arcTime s₂, hT₁, hT₁₂, fun t ht => ?_⟩
  have ht0 : 0 < t := hT₁.trans_le ht.1
  have hss₁ : s₁ ≤ discTime t := by
    have := discTime_le_discTime hT₁.le ht.1
    rwa [discTime_arcTime (hs₁₂.trans hs₂1)] at this
  have hss₂ : discTime t ≤ s₂ := by
    have := discTime_le_discTime ht0.le ht.2
    rwa [discTime_arcTime hs₂1] at this
  refine ⟨(discTime t - σM) / (τM - σM), ⟨?_, ?_⟩, ?_⟩
  · rw [le_div_iff₀ hΔ]; linarith
  · rw [div_le_iff₀ hΔ]; have := mul_lt_mul_of_pos_right hed hΔ; linarith
  · have hvs : σM + (discTime t - σM) / (τM - σM) * (τM - σM) = discTime t := by field_simp; ring
    rw [midArc, hvs]
    exact cfPt_toDisc_discTime hM ht0

/-- **A parameter interval of the clipped arc at infinity covers a time interval of the middle curve.** -/
theorem exists_interval_midArcInf (hM : IsSimpleProper M) {τM : ℝ} (hτ0 : 0 < τM) (hτ1 : τM ≤ 1) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c < d) :
    ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < t₂ ∧
      ∀ t ∈ Icc t₁ t₂, ∃ v ∈ Icc c d, midArcInf M τM v = negInv (M t.toNNReal) := by
  set e : ℝ := (c + d) / 2 with he
  have hce : c < e := by rw [he]; linarith
  have hed : e < d := by rw [he]; linarith
  have he0 : 0 < e := hc.trans_lt hce
  set s₁ := τM / (1 + d) with hs₁
  set s₂ := τM / (1 + e) with hs₂
  have hs₁pos : 0 < s₁ := div_pos hτ0 (by linarith)
  have hs₁₂ : s₁ < s₂ := div_lt_div_of_pos_left hτ0 (by linarith) (by linarith)
  have hs₂1 : s₂ < 1 := by
    rw [hs₂, div_lt_one (by linarith)]; linarith
  have hT₁ : 0 < arcTime s₁ := arcTime_pos ⟨hs₁pos, hs₁₂.trans hs₂1⟩
  have hT₁₂ : arcTime s₁ < arcTime s₂ := by
    by_contra hle
    have h' := discTime_le_discTime (arcTime_pos ⟨hs₁pos.trans hs₁₂, hs₂1⟩).le (not_lt.1 hle)
    rw [discTime_arcTime (hs₁₂.trans hs₂1), discTime_arcTime hs₂1] at h'
    linarith
  refine ⟨arcTime s₁, arcTime s₂, hT₁, hT₁₂, fun t ht => ?_⟩
  have ht0 : 0 < t := hT₁.trans_le ht.1
  have hss₁ : s₁ ≤ discTime t := by
    have := discTime_le_discTime hT₁.le ht.1
    rwa [discTime_arcTime (hs₁₂.trans hs₂1)] at this
  have hss₂ : discTime t ≤ s₂ := by
    have := discTime_le_discTime ht0.le ht.2
    rwa [discTime_arcTime hs₂1] at this
  have hs0 : 0 < discTime t := hs₁pos.trans_le hss₁
  refine ⟨τM / discTime t - 1, ⟨?_, ?_⟩, ?_⟩
  · have h1 : τM / s₂ ≤ τM / discTime t := div_le_div_of_nonneg_left hτ0.le hs0 hss₂
    have h2 : τM / s₂ = 1 + e := by rw [hs₂]; field_simp
    linarith
  · have h1 : τM / discTime t ≤ τM / s₁ := div_le_div_of_nonneg_left hτ0.le hs₁pos hss₁
    have h2 : τM / s₁ = 1 + d := by rw [hs₁]; field_simp
    linarith
  · have hvs : τM / (1 + (τM / discTime t - 1)) = discTime t := by
      rw [add_sub_cancel]; field_simp
    rw [midArcInf, hvs]
    exact cfPt_toDisc_discTime hM ht0

end Arcs

section Visits

variable {η : ℝ → ℂ}

theorem firstHit_nonneg (p : ℂ) : 0 ≤ firstHit η p := Real.sInf_nonneg fun _ hu => hu.1

theorem firstHit_le_of_mem {p : ℂ} {b : ℝ} (hp : p ∈ η '' Icc 0 b) : firstHit η p ≤ b := by
  obtain ⟨u, hu, hup⟩ := hp
  have hbdd : BddBelow {u ∈ Ici (0 : ℝ) | η u = p} := ⟨0, fun _ hw => hw.1⟩
  exact (csInf_le hbdd ⟨hu.1, hup⟩).trans hu.2

end Visits

section Clip

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- The counterflow-chart image of a closure point of the disc pocket off `−1` is in the closure of the pocket. -/
theorem cfPt_mem_closure (h : IsChangeConfigInc R L r) {w : ℂ} (hw : w ∈ closure (cayley '' changePocket R L r))
    (hw1 : w ≠ -1) : cfPt w ∈ closure (cfPocket R L r) := by
  rw [cfPocket, image_negInv_eq h.changePocket_subset_H]
  exact (continuousAt_cfPt hw1).continuousWithinAt.mem_closure_image hw

theorem toDisc_ne_neg_one (hM : IsSimpleProper M) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    toDisc (Lemma71I.realPath M) s ≠ -1 := fun he => by
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have := hαM.inj ⟨hs.1.le, hs.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hαM.zero.symm)
  linarith [hs.1]

theorem zero_notMem_H : (0 : ℂ) ∉ H := fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0)

/-- **The middle curve gains no new point beyond `x₀` on a no-`C` interval** (bounded pocket; Lemma R.3 and Aux. 42's
"no common arc"): for a disc time `p ∈ [σ_M, 1)` of the middle curve `M`, a point `m(M̃(p))` visited by time `b`
was visited by time `a`, when `[a, b]`, `a ≥ τ`, avoids the pocket. -/
theorem wall_stable (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) (hvis : IsWallVisited M η) {σM τM : ℝ} (hσ : 0 < σM) (hστ : σM < τM)
    (hτ1 : τM ≤ 1) (hτb : toDisc (Lemma71I.realPath M) τM = closePt R L r)
    (hin : ∀ t ∈ Icc σM τM, toDisc (Lemma71I.realPath M) t ∈ closure (cayley '' changePocket R L r))
    {a b : ℝ} (hτa : firstHit η (cfArcR R L r 1) ≤ a) (hab : a ≤ b)
    (havoid : ∀ t ∈ Icc a b, η t ∉ cfPocket R L r) {p : ℝ} (hp : p ∈ Ico σM 1)
    (hpb : cfPt (toDisc (Lemma71I.realPath M) p) ∈ η '' Icc 0 b) :
    cfPt (toDisc (Lemma71I.realPath M) p) ∈ η '' Icc 0 a := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hτI : τM ∈ Ioc (0 : ℝ) 1 := ⟨hσ.trans hστ, hτ1⟩
  have hy : cfPt (toDisc (Lemma71I.realPath M) τM) ∈ η '' Icc 0 a := by
    have hv := wall_visited hη0 hM hvis hτI
    have he : cfPt (toDisc (Lemma71I.realPath M) τM) = cfArcR R L r 1 := by
      rw [hτb, PocketCoord.IsChangeConfigInc.cfArcR_one]
    rw [he] at hv ⊢
    obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩
  rcases lt_or_ge p τM with hpτ | hpτ
  · obtain ⟨hBc, -⟩ := midArc_props hM hσ hστ hτ1
    have hBcl : ∀ v ∈ Icc (0 : ℝ) 1, midArc M σM τM v ∈ closure (cfPocket R L r) := fun v hv => by
      have hm := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hv
      exact cfPt_mem_closure h (hin _ hm) (toDisc_ne_neg_one hM ⟨hσ.trans_le hm.1, hm.2.trans hτ1⟩)
    have hno : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → ¬ midArc M σM τM '' Icc c d ⊆ frontier (cfPocket R L r) := by
      intro c d hc hcd hd hsub
      have hd' : σM + d * (τM - σM) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hd (sub_nonneg.2 hστ.le)
        linarith
      obtain ⟨t₁, t₂, ht₁, ht₁₂, hcov⟩ := exists_interval_midArc hM hσ hστ hc hcd hd'
      refine false_of_interval_union h.right hM hcR hcL ht₁ ht₁₂ fun t ht => ?_
      obtain ⟨v, hv, hve⟩ := hcov t ht
      have hMH : M t.toNNReal ∈ H := hM.2.2.2.1 _ (Real.toNNReal_pos.2 (ht₁.trans_le ht.1))
      have hfr := hsub ⟨v, hv, rfl⟩
      rw [hC.frontier_eq, hve] at hfr
      rcases hfr with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
      · exact Or.inl (mem_range_of_cfPt_toDisc h.right hMH hu)
      · exact Or.inr (mem_range_of_cfPt_toDisc h.left hMH hu)
    have heq := visited_eq_of_noArc hηc hC.isOpen hBc hBcl subset_rfl (midArc_rev hM hη0 hrev hσ hστ hτ1) hno hab
      (by rw [midArc_one]; exact hy) havoid
    have hΔ : 0 < τM - σM := sub_pos.2 hστ
    set v := (p - σM) / (τM - σM) with hv
    have hvI : v ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.2 hp.1) hΔ.le
      · rw [hv, div_le_one hΔ]; linarith
    have hBv : midArc M σM τM v = cfPt (toDisc (Lemma71I.realPath M) p) := by
      rw [midArc, hv]; congr 2; field_simp; ring
    have hmem : v ∈ {v ∈ Icc (0 : ℝ) 1 | midArc M σM τM v ∈ η '' Icc 0 b} := ⟨hvI, hBv ▸ hpb⟩
    rw [heq] at hmem
    exact hBv ▸ hmem.2
  · exact wall_rev hM hη0 hrev hτI ⟨hσ.trans_le hp.1, hp.2.le⟩ hpτ hy

/-- **Aux. lemma 37 along the clipped `β_R` of a bounded pocket with two outer arms** (`OuterOuterAttach`, every
clipping with the corner endpoints): a pathwise consequence of Lemma R.3's clipping, the reverse visits of `M` and
`NoCommonArc` of `M` with both walls — a newly visited clipped point on a no-`C` interval lies on the pocket's frontier,
which is on the two walls, and a nontrivial arc of `M` cannot lie there. -/
theorem outerOuterAttach (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) (hvis : IsWallVisited M η) : OuterIn.OuterOuterAttach R L M r η := by
  intro σ₁ τ₁ hB0 _ a b hτa hab hbσ havoid
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hσpos : 0 < σM := by
    refine lt_of_le_of_ne h0σ fun he => h.openPt_ne_neg_one h0 ?_
    rw [← hσa, ← he]
    exact hαM.zero
  have hx : cfArcR R L r 0 = cfPt (toDisc (Lemma71I.realPath M) σM) := by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, hσa]
  have hxH : cfArcR R L r 0 ∈ H := hC.mem_H₁ 0 ⟨le_rfl, zero_lt_one⟩
  have hσ₁ : σ₁ = σM := by
    rw [midArc_zero] at hB0
    have hH : cfPt (toDisc (Lemma71I.realPath M) σ₁) ∈ H := hB0 ▸ hxH
    have hσ₁I : σ₁ ∈ Ioo (0 : ℝ) 1 := by
      by_contra hn
      rw [cfPt_toDisc_eq_zero hM hn] at hH
      exact zero_notMem_H hH
    rw [hx] at hB0
    exact hαM.inj ⟨hσ₁I.1.le, hσ₁I.2.le⟩ ⟨h0σ, hστ.le.trans hτ1⟩
      (injOn_cfPt (toDisc_ne_neg_one hM ⟨hσ₁I.1, hσ₁I.2.le⟩) (toDisc_ne_neg_one hM ⟨hσpos, hστ.le.trans hτ1⟩) hB0)
  subst hσ₁
  have ha0 : 0 ≤ a := (firstHit_nonneg _).trans hτa
  have h0a : (0 : ℂ) ∈ η '' Icc 0 a := ⟨0, ⟨le_rfl, ha0⟩, hη0⟩
  unfold firstVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  change cfPt (toDisc (Lemma71I.realPath M) (σ₁ + v * (τ₁ - σ₁))) ∈ η '' Icc 0 a
  have hvb : cfPt (toDisc (Lemma71I.realPath M) (σ₁ + v * (τ₁ - σ₁))) ∈ η '' Icc 0 b := hv.2
  set p := σ₁ + v * (τ₁ - σ₁) with hp
  by_cases hpI : p ∈ Ioo (0 : ℝ) 1
  · rcases lt_or_ge p σ₁ with hpσ | hpσ
    · exfalso
      have hxv := wall_rev hM hη0 hrev ⟨hpI.1, hpI.2.le⟩ ⟨hσpos, hστ.le.trans hτ1⟩ hpσ.le hvb
      rw [← hx] at hxv
      exact absurd (firstHit_le_of_mem hxv) (not_le.2 hbσ)
    · exact wall_stable h hb hM hcR hcL hηc hη0 hrev hvis hσpos hστ hτ1 hτb hin hτa hab havoid ⟨hpσ, hpI.2⟩ hvb
  · rw [cfPt_toDisc_eq_zero hM hpI]
    exact h0a

/-- **The middle curve gains no new point on a no-`C` interval of a pocket opening at the flow seed**: for every disc
time `p ∈ (0, 1)` of `M`, a point `m(M̃(p))` visited by time `b` was visited by time `a`. -/
theorem wall_stableInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hM : IsSimpleProper M)
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) (hvis : IsWallVisited M η) {τM : ℝ} (hτ0 : 0 < τM) (hτ1 : τM ≤ 1)
    (hτb : toDisc (Lemma71I.realPath M) τM = closePt R L r)
    (hin : ∀ t ∈ Icc 0 τM, toDisc (Lemma71I.realPath M) t ∈ closure (cayley '' changePocket R L r))
    {a b : ℝ} (hτa : firstHit η (cfArcRInf R L r 0) ≤ a) (hab : a ≤ b)
    (havoid : ∀ t ∈ Icc a b, η t ∉ cfPocket R L r) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpb : cfPt (toDisc (Lemma71I.realPath M) p) ∈ η '' Icc 0 b) :
    cfPt (toDisc (Lemma71I.realPath M) p) ∈ η '' Icc 0 a := by
  have hC := h.isCfPocketInf h0
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hτI : τM ∈ Ioc (0 : ℝ) 1 := ⟨hτ0, hτ1⟩
  have hy : cfPt (toDisc (Lemma71I.realPath M) τM) ∈ η '' Icc 0 a := by
    have hv := wall_visited hη0 hM hvis hτI
    have he : cfPt (toDisc (Lemma71I.realPath M) τM) = cfArcRInf R L r 0 := by
      rw [hτb, PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
    rw [he] at hv ⊢
    obtain ⟨hτ0', hτ, -⟩ := firstHit_spec hηc hv
    exact ⟨_, ⟨hτ0', hτa⟩, hτ⟩
  rcases le_or_gt p τM with hpτ | hpτ
  · obtain ⟨hBc, -, -, -, -⟩ := crosscut_arcInf_props hαM hτ0 hτ1
    have hBcl : ∀ v ∈ Ici (0 : ℝ), midArcInf M τM v ∈ closure (cfPocket R L r) := fun v hv => by
      have hm := div_one_add_mem hτ0 hv
      exact cfPt_mem_closure h (hin _ ⟨hm.1.le, hm.2⟩) (toDisc_ne_neg_one hM ⟨hm.1, hm.2.trans hτ1⟩)
    have hno : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ midArcInf M τM '' Icc c d ⊆ frontier (cfPocket R L r) := by
      intro c d hc hcd hsub
      obtain ⟨t₁, t₂, ht₁, ht₁₂, hcov⟩ := exists_interval_midArcInf hM hτ0 hτ1 hc hcd
      refine false_of_interval_union h.right hM hcR hcL ht₁ ht₁₂ fun t ht => ?_
      obtain ⟨v, hv, hve⟩ := hcov t ht
      have hMH : M t.toNNReal ∈ H := hM.2.2.2.1 _ (Real.toNNReal_pos.2 (ht₁.trans_le ht.1))
      have hfr := hsub ⟨v, hv, rfl⟩
      rw [hC.frontier_eq, hve] at hfr
      rcases hfr with ⟨u, -, hu⟩ | ⟨u, -, hu⟩
      · exact Or.inl (mem_range_of_cfPt_toDisc h.right hMH hu)
      · exact Or.inr (mem_range_of_cfPt_toDisc h.left hMH hu)
    have hB0 : midArcInf M τM 0 = cfPt (toDisc (Lemma71I.realPath M) τM) := by
      simp only [midArcInf, add_zero, div_one]
    have heq := visitedInf_eq_of_noArc (B := midArcInf M τM) hηc hC.isOpen hBc hBcl subset_rfl
      (rev_inf_of_wall hM hη0 hrev hτ0 hτ1) hno hab (by rw [hB0]; exact hy) havoid
    set v := τM / p - 1 with hv
    have hvI : v ∈ Ici (0 : ℝ) := by
      rw [mem_Ici, hv, sub_nonneg, le_div_iff₀ hp.1, one_mul]; exact hpτ
    have hBv : midArcInf M τM v = cfPt (toDisc (Lemma71I.realPath M) p) := by
      rw [midArcInf, hv, add_sub_cancel]; congr 2; field_simp
    have hmem : v ∈ {v ∈ Ici (0 : ℝ) | midArcInf M τM v ∈ η '' Icc 0 b} := ⟨hvI, hBv ▸ hpb⟩
    rw [heq] at hmem
    exact hBv ▸ hmem.2
  · exact wall_rev hM hη0 hrev hτI ⟨hp.1, hp.2.le⟩ hpτ.le hy

/-- **Aux. lemma 37 along the clipped `β_R` of a pocket with two outer arms opening at the flow seed**
(`OuterOuterAttachInf`, every clipping from `m(y₀)`): pathwise, as `outerOuterAttach`. -/
theorem outerOuterAttachInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit M η) (hvis : IsWallVisited M η) : OuterIn.OuterOuterAttachInf R L M r η := by
  intro τ₁ _ a b hτa hab havoid
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, hin, -⟩ := exists_midTimes h hO hcR hcL
  have hαR := h.right.isProperArc.isDiscCrosscut_toDisc
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hσ0 : σM = 0 := by
    have he : toDisc (Lemma71I.realPath M) σM = toDisc (Lemma71I.realPath M) 0 := by
      rw [hσa, hαM.zero, openPt, h0, hαR.zero]
    exact hαM.inj ⟨h0σ, hστ.le.trans hτ1⟩ ⟨le_rfl, zero_le_one⟩ he
  subst hσ0
  have ha0 : 0 ≤ a := (firstHit_nonneg _).trans hτa
  have h0a : (0 : ℂ) ∈ η '' Icc 0 a := ⟨0, ⟨le_rfl, ha0⟩, hη0⟩
  unfold lastVisit
  congr 1
  ext v
  refine ⟨fun hv => ⟨hv.1, ?_⟩, fun hv => ⟨hv.1, image_mono (Icc_subset_Icc_right hab) hv.2⟩⟩
  change cfPt (toDisc (Lemma71I.realPath M) (τ₁ / (1 + v))) ∈ η '' Icc 0 a
  have hvb : cfPt (toDisc (Lemma71I.realPath M) (τ₁ / (1 + v))) ∈ η '' Icc 0 b := hv.2
  by_cases hpI : τ₁ / (1 + v) ∈ Ioo (0 : ℝ) 1
  · exact wall_stableInf h h0 hM hcR hcL hηc hη0 hrev hvis hστ hτ1 hτb hin hτa hab havoid hpI hvb
  · rw [cfPt_toDisc_eq_zero hM hpI]
    exact h0a

end Clip


end InteractingSLE.Sec7.OuterGeom
