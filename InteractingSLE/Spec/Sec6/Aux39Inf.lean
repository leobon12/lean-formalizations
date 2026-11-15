/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux36Face
import InteractingSLE.Foundations.Topology.ThetaCurve

/-!
# The fixed-chart gate lemma with the junction at infinity

Ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` L140–L186), Lemma 1.3: "If the
target junction is infinity, the two proper incoming arms give the same separation directly: the
central face has real base `[q₁, q₂]`, and the two exterior faces meet only at infinity after the
arms are removed. The finite bounded path cannot use that point. In either case its endpoint gates
agree."

When the pocket junction `x_C` is the original target, the two lifted incoming arms are proper
arcs from the gates `q₁ < q₂` to `∞`. A real Möbius map `ψ(w) = −1/(w − p)` (`p < q₁` real) of `ℍ`
sends `∞` to `0` and the arms to arcs `b₁, b₂` from the real points `x₁ = ψ(q₁) < x₂ = ψ(q₂) < 0`
to `0`, open in `ℍ` and meeting only at `0`. This file proves the gate lemma in that picture: the
central face is the inner side of the Jordan curve `Γ = B₁ ∪ B₂ ∪ [x₁, x₂]`, the bounded path
avoids `0` (the image of `∞`), and the separating curves are `Ξ₁ = B₁ ∪ [x₁, 0]` and
`Ξ₂ = B₂ ∪ [x₂, 0]` (the closure of the right exterior face is that of `innerSide Ξ₂`; the left
exterior face is `outerSide Ξ₁`).

## Main results

* `jordanIn_eq_innerSide`, `jordanOut_eq_outerSide`: the Jordan sides of `WangWu` (used by the
  θ-curve theorem, PROVE-R16) are `innerSide`, `outerSide` for curves in `ℍ̄`;
* `halfDisc_subset_innerSide_of_real`: near a real point of a Jordan curve in `ℍ̄` whose nearby
  points are real, the upper half-disc is on the inner side;
* `isJordanCurve_sideInf`, `isJordanCurve_faceInf`: the curves `Ξᵢ` and `Γ`;
* `false_of_isPreconnected_inf`: **the separation** — a preconnected subset of `ℍ̄ \ {0}` avoiding
  the open arcs, the central face and `(x₁, x₂)` cannot contain both gates (via the θ-curve
  theorem `Foundations.ThetaCurve.compl_theta_subset` for the three arcs `[x₂, x₁] + B₁`,
  `[x₂, 0]`, `B₂`
  from `x₂` to `0`);
* `gate_lemma_inf`, `gate_lemma_inf_of_gate`: **Lemma 1.3, junction at infinity** (distinct gates).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

section Sides

variable {J : Set ℂ}

/-- For a Jordan curve in `ℍ̄`, `WangWu.jordanIn` is `innerSide`. -/
theorem jordanIn_eq_innerSide (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar) :
    WangWu.jordanIn J = innerSide J := by
  obtain ⟨⟨x₁, -, hin⟩, hIb, -, -, -, -, -, -, -⟩ := jordan_sides hJ hJH
  ext z
  constructor
  · rintro ⟨hzJ, hb⟩
    rw [← eq_innerSide_of_isBounded hJ hJH hzJ hb]
    exact mem_connectedComponentIn hzJ
  · intro hz
    refine ⟨hz.1, ?_⟩
    have : connectedComponentIn Jᶜ z = innerSide J := by
      rw [hin] at hz ⊢; exact (connectedComponentIn_eq hz).symm
    rw [this]; exact hIb

/-- For a Jordan curve in `ℍ̄`, `WangWu.jordanOut` is `outerSide`. -/
theorem jordanOut_eq_outerSide (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar) :
    WangWu.jordanOut J = outerSide J := by
  ext z
  constructor
  · rintro ⟨hzJ, hb⟩
    have h : z ∈ Jᶜ := hzJ
    rw [compl_eq_innerSide_union_outerSide] at h
    refine h.resolve_left fun hzI => hb ?_
    rw [← jordanIn_eq_innerSide hJ hJH] at hzI
    exact hzI.2
  · intro hz
    refine ⟨outerSide_subset_compl hz, fun hb => outerSide_not_isBounded hJH ?_⟩
    rw [outerSide, connectedComponentIn_eq hz]; exact hb

/-- **Upper half-discs at real points.** If `v` is a real point of a Jordan curve `J ⊆ ℍ̄` and every
point of `J` within `ε` of `v` is real, the upper half-disc of radius `ε` about `v` lies on the
inner side of `J`. -/
theorem halfDisc_subset_innerSide_of_real (hJ : LQGMetric.JordanMap.IsJordanCurve J)
    (hJH : J ⊆ Hbar) {v : ℝ} (hv : (v : ℂ) ∈ J) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ w ∈ J, dist w v < ε → w.im = 0) {w : ℂ} (hw : dist w v < ε) (hwH : 0 < w.im) :
    w ∈ innerSide J := by
  obtain ⟨⟨x₁, -, hin⟩, -, hfr, -, -, -, -, -, -⟩ := jordan_sides hJ hJH
  set B := ball (v : ℂ) ε ∩ H with hB
  have hBJ : B ⊆ Jᶜ := fun u hu huJ => by
    have h1 := hloc u huJ hu.1
    have h2 : (0 : ℝ) < u.im := hu.2
    linarith
  have hBc : IsPreconnected B :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hvF : (v : ℂ) ∈ frontier (innerSide J) := by rw [hfr]; exact hv
  obtain ⟨p, hpb, hpF⟩ := mem_closure_iff.1 (frontier_subset_closure hvF) _ isOpen_ball
    (mem_ball_self hε)
  have hpH : p ∈ H := innerSide_subset_H hJ hJH hpF
  have hsub := hBc.subset_connectedComponentIn (x := p) ⟨hpb, hpH⟩ hBJ
  have hpcc : connectedComponentIn Jᶜ p = innerSide J := by
    rw [hin] at hpF ⊢; exact (connectedComponentIn_eq hpF).symm
  rw [← hpcc]; exact hsub ⟨hw, hwH⟩

end Sides

section Arcs

/-- Real points of an arc `b : [0, 1] → ℂ` from `x` to `0` which is open in `ℍ` are its ends. -/
theorem arcInf_real {b : ℝ → ℂ} {x : ℝ} (hb0 : b 0 = x) (hb1 : b 1 = 0)
    (hbH : ∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) {w : ℂ} (hw : w ∈ b '' Icc 0 1) (him : w.im = 0) :
    w = x ∨ w = 0 := by
  obtain ⟨t, ht, rfl⟩ := hw
  rcases eq_or_lt_of_le ht.1 with h | h
  · left; rw [← h, hb0]
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · right; rw [h', hb1]
  · have : (0 : ℝ) < (b t).im := hbH t ⟨h, h'⟩
    linarith

/-- Such an arc lies in `ℍ̄`. -/
theorem image_arcInf_subset_Hbar {b : ℝ → ℂ} {x : ℝ} (hb0 : b 0 = x) (hb1 : b 1 = 0)
    (hbH : ∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) : b '' Icc 0 1 ⊆ Hbar := by
  rintro _ ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, hb0]; exact ofReal_mem_Hbar x
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · rw [h', hb1]; simpa using ofReal_mem_Hbar 0
  · exact QuantumZipper.H_subset_Hbar (hbH t ⟨h, h'⟩)

theorem ofReal_image_subset_Hbar (S : Set ℝ) : ofReal '' S ⊆ Hbar := by
  rintro _ ⟨x, -, rfl⟩; exact ofReal_mem_Hbar x

/-- **The side curve** `Ξ = B ∪ [x, 0]` is a Jordan curve in `ℍ̄`. -/
theorem isJordanCurve_sideInf {b : ℝ → ℂ} {x : ℝ} (hx : x < 0) (hb : ContinuousOn b (Icc 0 1))
    (hbi : InjOn b (Icc 0 1)) (hb0 : b 0 = x) (hb1 : b 1 = 0)
    (hbH : ∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) :
    LQGMetric.JordanMap.IsJordanCurve (b '' Icc 0 1 ∪ ofReal '' Icc x 0) ∧
      b '' Icc 0 1 ∪ ofReal '' Icc x 0 ⊆ Hbar := by
  have hseg : segPath (x : ℂ) ((0 : ℝ) : ℂ) '' Icc 0 1 = ofReal '' Icc x 0 :=
    image_segPath_ofReal hx.le
  have hne : (x : ℂ) ≠ ((0 : ℝ) : ℂ) := fun h => by have := ofReal_injective h; linarith
  have hJ := Sec7.isJordanCurve_image_union (u := b) (v := segPath (x : ℂ) ((0 : ℝ) : ℂ)) hb
    (continuous_segPath _ _).continuousOn hbi (injOn_segPath hne) (by rw [hb0, segPath_zero])
    (by rw [hb1, segPath_one, ofReal_zero]) (by
      rintro w ⟨hw1, hw2⟩
      rw [hseg] at hw2
      rcases arcInf_real hb0 hb1 hbH hw1 (im_eq_zero_of_mem_ofReal_image hw2) with h | h
      · left; rw [h, hb0]
      · right; rw [h, hb1]; rfl)
  rw [hseg] at hJ
  exact ⟨hJ, union_subset (image_arcInf_subset_Hbar hb0 hb1 hbH) (ofReal_image_subset_Hbar _)⟩

end Arcs

section Inf

/-- The configuration at infinity, in the `ψ`-picture: two arcs `b₁, b₂` from the real gates
`x₁ < x₂ < 0` to `0` (the image of `∞`), open in `ℍ`, meeting only at `0`. -/
structure IsArcPairInf (x₁ x₂ : ℝ) (b₁ b₂ : ℝ → ℂ) : Prop where
  lt : x₁ < x₂
  neg : x₂ < 0
  cont₁ : ContinuousOn b₁ (Icc 0 1)
  cont₂ : ContinuousOn b₂ (Icc 0 1)
  inj₁ : InjOn b₁ (Icc 0 1)
  inj₂ : InjOn b₂ (Icc 0 1)
  zero₁ : b₁ 0 = x₁
  zero₂ : b₂ 0 = x₂
  one₁ : b₁ 1 = 0
  one₂ : b₂ 1 = 0
  mem₁ : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H
  mem₂ : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H
  inter : b₁ '' Icc 0 1 ∩ b₂ '' Icc 0 1 ⊆ {0}

variable {x₁ x₂ : ℝ} {b₁ b₂ : ℝ → ℂ}

/-- A point of an arc is its start, a point of the open arc, or its end. -/
theorem mem_arc_trichotomy {b : ℝ → ℂ} {w : ℂ} (hw : w ∈ b '' Icc 0 1) :
    w = b 0 ∨ w ∈ b '' Ioo 0 1 ∨ w = b 1 := by
  obtain ⟨t, ht, rfl⟩ := hw
  rcases eq_or_lt_of_le ht.1 with h | h
  · left; rw [h]
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · right; right; rw [h']
  · exact Or.inr (Or.inl ⟨t, ⟨h, h'⟩, rfl⟩)

/-- A real point `v` off a compact arc has a neighbourhood missing the arc. -/
theorem exists_ball_disjoint_arc {b : ℝ → ℂ} (hb : ContinuousOn b (Icc 0 1)) {v : ℂ}
    (hv : v ∉ b '' Icc 0 1) : ∃ ε > 0, ∀ w ∈ b '' Icc 0 1, ε ≤ dist w v := by
  have hc : IsClosed (b '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hb).isClosed
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hc.isOpen_compl v hv
  refine ⟨ε, hε, fun w hw => ?_⟩
  by_contra h
  push Not at h
  exact hεs (mem_ball.2 h) hw

/-- Upper half-discs over a real point `v ∈ (x, 0)` of a side curve `B ∪ [x, 0]` are inner. -/
theorem halfDisc_side {b : ℝ → ℂ} {x : ℝ} (hb : ContinuousOn b (Icc 0 1))
    (hJ : LQGMetric.JordanMap.IsJordanCurve (b '' Icc 0 1 ∪ ofReal '' Icc x 0))
    (hJH : b '' Icc 0 1 ∪ ofReal '' Icc x 0 ⊆ Hbar) (hb0 : b 0 = x) (hb1 : b 1 = 0)
    (hbH : ∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) {v : ℝ} (hv : v ∈ Ioo x 0) :
    ∃ ε > 0, ∀ w : ℂ, dist w v < ε → 0 ≤ w.im →
      w ∈ innerSide (b '' Icc 0 1 ∪ ofReal '' Icc x 0) ∨ w ∈ ofReal '' Icc x 0 := by
  have hvb : (v : ℂ) ∉ b '' Icc 0 1 := fun hv' => by
    rcases arcInf_real hb0 hb1 hbH hv' (by simp) with h' | h'
    · have := ofReal_injective h'; linarith [hv.1]
    · have := ofReal_eq_zero.1 h'; linarith [hv.2]
  obtain ⟨ε₀, hε₀, hε₀b⟩ := exists_ball_disjoint_arc hb hvb
  set ε := min ε₀ (min (v - x) (-v)) with hε
  have hεpos : 0 < ε := lt_min hε₀ (lt_min (by linarith [hv.1]) (by linarith [hv.2]))
  refine ⟨ε, hεpos, fun w hw hwim => ?_⟩
  rcases eq_or_lt_of_le hwim with h0 | h0
  · right
    refine ⟨w.re, ?_, Complex.ext (by simp) (by simp [← h0])⟩
    have h1 := abs_re_le_norm (w - v)
    rw [sub_re, ofReal_re, ← dist_eq_norm] at h1
    have h2 : ε ≤ v - x := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : ε ≤ -v := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : |w.re - v| < ε := lt_of_le_of_lt h1 hw
    rw [abs_lt] at h4
    exact ⟨by linarith [h4.1], by linarith [h4.2]⟩
  · left
    refine halfDisc_subset_innerSide_of_real hJ hJH (Or.inr ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩) hεpos
      (fun u hu hud => ?_) hw h0
    rcases hu with hu | hu
    · exact absurd (hε₀b u hu) (not_le.2 (lt_of_lt_of_le hud (min_le_left _ _)))
    · exact im_eq_zero_of_mem_ofReal_image hu

namespace IsArcPairInf

variable (h : IsArcPairInf x₁ x₂ b₁ b₂)
include h

/-- **The central face boundary** `Γ = B₁ ∪ B₂ ∪ [x₁, x₂]` is a Jordan curve in `ℍ̄`. -/
theorem isJordanCurve_face :
    LQGMetric.JordanMap.IsJordanCurve (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂) ∧
      b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂ ⊆ Hbar := by
  have hj : segPath (x₁ : ℂ) (x₂ : ℂ) 1 = b₂ 0 := by rw [segPath_one, h.zero₂]
  have hseg : segPath (x₁ : ℂ) (x₂ : ℂ) '' Icc 0 1 = ofReal '' Icc x₁ x₂ :=
    image_segPath_ofReal h.lt.le
  have hne : (x₁ : ℂ) ≠ x₂ := fun h' => by have := ofReal_injective h'; linarith [h.lt]
  have hvi : InjOn (arcJoin (segPath (x₁ : ℂ) (x₂ : ℂ)) b₂) (Icc 0 1) :=
    injOn_arcJoin (injOn_segPath hne) h.inj₂ hj (by
      rintro w ⟨hw1, hw2⟩
      rw [hseg] at hw1
      obtain ⟨y, hy, rfl⟩ := hw1
      rcases arcInf_real h.zero₂ h.one₂ h.mem₂ hw2 (by simp) with h' | h'
      · rw [mem_singleton_iff, segPath_one, h']
      · have := ofReal_eq_zero.1 h'; linarith [hy.2, h.neg])
  have hJ := Sec7.isJordanCurve_image_union (u := b₁)
    (v := arcJoin (segPath (x₁ : ℂ) (x₂ : ℂ)) b₂) h.cont₁
    (continuousOn_arcJoin (continuous_segPath _ _).continuousOn h.cont₂ hj) h.inj₁ hvi
    (by rw [arcJoin_zero, segPath_zero, h.zero₁]) (by rw [arcJoin_one, h.one₁, h.one₂]) (by
      rw [image_arcJoin hj, hseg]
      rintro w ⟨hw1, hw2 | hw2⟩
      · rcases arcInf_real h.zero₁ h.one₁ h.mem₁ hw1 (im_eq_zero_of_mem_ofReal_image hw2)
          with h' | h'
        · left; rw [h', h.zero₁]
        · right; rw [h', h.one₁]; rfl
      · right; rw [h.inter ⟨hw1, hw2⟩, h.one₁]; rfl)
  rw [image_arcJoin hj, hseg] at hJ
  have e : b₁ '' Icc 0 1 ∪ (ofReal '' Icc x₁ x₂ ∪ b₂ '' Icc 0 1) =
      b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂ := by
    rw [union_comm (ofReal '' Icc x₁ x₂), union_assoc]
  rw [e] at hJ
  exact ⟨hJ, union_subset (union_subset (image_arcInf_subset_Hbar h.zero₁ h.one₁ h.mem₁)
    (image_arcInf_subset_Hbar h.zero₂ h.one₂ h.mem₂)) (ofReal_image_subset_Hbar _)⟩

theorem isJordanCurve_side₁ :
    LQGMetric.JordanMap.IsJordanCurve (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) ∧
      b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 ⊆ Hbar :=
  isJordanCurve_sideInf (h.lt.trans h.neg) h.cont₁ h.inj₁ h.zero₁ h.one₁ h.mem₁

theorem isJordanCurve_side₂ :
    LQGMetric.JordanMap.IsJordanCurve (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0) ∧
      b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0 ⊆ Hbar :=
  isJordanCurve_sideInf h.neg h.cont₂ h.inj₂ h.zero₂ h.one₂ h.mem₂

/-- The right exterior face lies inside the left side curve: `innerSide Ξ₂ ⊆ innerSide Ξ₁`. -/
theorem innerSide_side₂_subset :
    innerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0) ⊆
      innerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) := by
  obtain ⟨hΞ₁, hΞ₁H⟩ := h.isJordanCurve_side₁
  obtain ⟨hΞ₂, hΞ₂H⟩ := h.isJordanCurve_side₂
  obtain ⟨-, -, -, -, hI₁o, hO₁o, -, -, -⟩ := jordan_sides hΞ₁ hΞ₁H
  obtain ⟨-, -, -, -, -, hO₂o, -, hI₂p, -⟩ := jordan_sides hΞ₂ hΞ₂H
  set Ξ₁ := b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 with hΞ₁def
  set Ξ₂ := b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0 with hΞ₂def
  -- the open arc `B₁` is on the outer side of `Ξ₂`
  have hb₁O : b₁ '' Ioo 0 1 ⊆ outerSide Ξ₂ := by
    have hpre : IsPreconnected (b₁ '' Ioo 0 1) :=
      isPreconnected_Ioo.image _ (h.cont₁.mono Ioo_subset_Icc_self)
    have hsub : b₁ '' Ioo 0 1 ⊆ Ξ₂ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ (hw | hw)
      · have h0 := h.inter ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, hw⟩
        rw [mem_singleton_iff] at h0
        have h1 : (0 : ℝ) < (b₁ t).im := h.mem₁ t ht
        rw [h0] at h1; simp at h1
      · have h1 : (0 : ℝ) < (b₁ t).im := h.mem₁ t ht
        rw [im_eq_zero_of_mem_ofReal_image hw] at h1; exact lt_irrefl _ h1
    have hx₁Ξ₂ : (x₁ : ℂ) ∉ Ξ₂ := by
      rintro (hx | ⟨y, hy, hyx⟩)
      · rcases arcInf_real h.zero₂ h.one₂ h.mem₂ hx (by simp) with h' | h'
        · have := ofReal_injective h'; linarith [h.lt]
        · have := ofReal_eq_zero.1 h'; linarith [h.lt, h.neg]
      · have := ofReal_injective hyx; linarith [hy.1, h.lt]
    have hx₁O : (x₁ : ℂ) ∈ outerSide Ξ₂ := ofReal_mem_outerSide hΞ₂ hΞ₂H hx₁Ξ₂
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO₂o _ hx₁O
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 (h.cont₁ 0 ⟨le_rfl, zero_le_one⟩) ε hε
    set t := min (δ / 2) (1 / 2) with ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num)⟩
    have htO : b₁ t ∈ outerSide Ξ₂ := by
      refine hεO ?_
      have := hδb (Ioo_subset_Icc_self htI) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos htI.1]
        exact (min_le_left _ _).trans_lt (by linarith))
      rw [h.zero₁] at this; exact this
    have h1 := hpre.subset_connectedComponentIn ⟨t, htI, rfl⟩ hsub
    rw [outerSide, connectedComponentIn_eq htO]
    exact h1
  -- `innerSide Ξ₂` avoids `Ξ₁`
  have hsub : innerSide Ξ₂ ⊆ innerSide Ξ₁ ∪ outerSide Ξ₁ := by
    intro w hw
    have hwH : w ∈ H := innerSide_subset_H hΞ₂ hΞ₂H hw
    have hwΞ₁ : w ∈ Ξ₁ᶜ := by
      rintro (hw1 | hw1)
      · rcases mem_arc_trichotomy hw1 with h' | h' | h'
        · rw [h', h.zero₁] at hwH; exact not_mem_H_ofReal x₁ hwH
        · exact disjoint_innerSide_outerSide.le_bot ⟨hw, hb₁O h'⟩
        · rw [h', h.one₁] at hwH; simpa using not_mem_H_ofReal 0 (by simpa using hwH)
      · exact absurd hwH (by obtain ⟨y, -, rfl⟩ := hw1; exact not_mem_H_ofReal y)
    rw [← compl_eq_innerSide_union_outerSide]; exact hwΞ₁
  -- a common inner point over `x₂ / 2`
  have hv₂ : x₂ / 2 ∈ Ioo x₂ 0 := ⟨by linarith [h.neg], by linarith [h.neg]⟩
  have hv₁ : x₂ / 2 ∈ Ioo x₁ 0 := ⟨by linarith [h.neg, h.lt], by linarith [h.neg]⟩
  obtain ⟨ε₁, hε₁, hε₁I⟩ := halfDisc_side h.cont₁ hΞ₁ hΞ₁H h.zero₁ h.one₁ h.mem₁ hv₁
  obtain ⟨ε₂, hε₂, hε₂I⟩ := halfDisc_side h.cont₂ hΞ₂ hΞ₂H h.zero₂ h.one₂ h.mem₂ hv₂
  set ε := min ε₁ ε₂ with hε
  have hεpos : 0 < ε := lt_min hε₁ hε₂
  set w : ℂ := ((x₂ / 2 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I with hw
  have hwd : dist w ((x₂ / 2 : ℝ) : ℂ) = ε / 2 := by
    rw [hw, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hwim : 0 < w.im := by simp [hw]; positivity
  have hnreal : ∀ {x : ℝ}, w ∉ ofReal '' Icc x 0 := fun hm => by
    have := im_eq_zero_of_mem_ofReal_image hm; linarith
  have hw₂ : w ∈ innerSide Ξ₂ :=
    (hε₂I w (by rw [hwd]; linarith [min_le_right ε₁ ε₂]) hwim.le).resolve_right hnreal
  have hw₁ : w ∈ innerSide Ξ₁ :=
    (hε₁I w (by rw [hwd]; linarith [min_le_left ε₁ ε₂]) hwim.le).resolve_right hnreal
  exact hI₂p.subset_left_of_subset_union hI₁o hO₁o disjoint_innerSide_outerSide hsub
    ⟨w, hw₂, hw₁⟩

/-- **The three faces** (θ-curve theorem for the arcs `[x₂, x₁] + B₁`, `[x₂, 0]`, `B₂` from `x₂`
to `0`): every point off `B₁ ∪ B₂ ∪ [x₁, 0]` is outside `Ξ₁`, inside `Γ`, or inside `Ξ₂`. -/
theorem compl_subset {z : ℂ} (hz : z ∉ b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) :
    z ∈ outerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) ∨
      z ∈ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂) ∨
      z ∈ innerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0) := by
  have hj : segPath (x₂ : ℂ) (x₁ : ℂ) 1 = b₁ 0 := by rw [segPath_one, h.zero₁]
  have hseg₁ : segPath (x₂ : ℂ) (x₁ : ℂ) '' Icc 0 1 = ofReal '' Icc x₁ x₂ :=
    image_segPath_ofReal' h.lt.le
  have hseg₂ : segPath (x₂ : ℂ) ((0 : ℝ) : ℂ) '' Icc 0 1 = ofReal '' Icc x₂ 0 :=
    image_segPath_ofReal h.neg.le
  have hne₁ : (x₂ : ℂ) ≠ x₁ := fun h' => by have := ofReal_injective h'; linarith [h.lt]
  have hne₂ : (x₂ : ℂ) ≠ ((0 : ℝ) : ℂ) := fun h' => by
    have := ofReal_injective h'; linarith [h.neg]
  have hu : Foundations.ThetaCurve.IsArcFrom (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁)
      (x₂ : ℂ) 0 := by
    refine ⟨continuousOn_arcJoin (continuous_segPath _ _).continuousOn h.cont₁ hj,
      injOn_arcJoin (injOn_segPath hne₁) h.inj₁ hj ?_, by rw [arcJoin_zero, segPath_zero],
      by rw [arcJoin_one, h.one₁]⟩
    rintro w ⟨hw1, hw2⟩
    rw [hseg₁] at hw1
    obtain ⟨y, hy, rfl⟩ := hw1
    rcases arcInf_real h.zero₁ h.one₁ h.mem₁ hw2 (by simp) with h' | h'
    · rw [mem_singleton_iff, segPath_one, h']
    · have := ofReal_eq_zero.1 h'; linarith [hy.2, h.neg]
  have hv : Foundations.ThetaCurve.IsArcFrom (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) (x₂ : ℂ) 0 :=
    ⟨(continuous_segPath _ _).continuousOn, injOn_segPath hne₂, segPath_zero _ _,
      by rw [segPath_one, ofReal_zero]⟩
  have hw : Foundations.ThetaCurve.IsArcFrom b₂ (x₂ : ℂ) 0 := ⟨h.cont₂, h.inj₂, h.zero₂, h.one₂⟩
  have hau : Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) =
      ofReal '' Icc x₁ x₂ ∪ b₁ '' Icc 0 1 := by
    rw [Foundations.ThetaCurve.arc, image_arcJoin hj, hseg₁]
  have hav : Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) =
      ofReal '' Icc x₂ 0 := hseg₂
  have haw : Foundations.ThetaCurve.arc b₂ = b₂ '' Icc 0 1 := rfl
  have h0 : ((0 : ℝ) : ℂ) = 0 := ofReal_zero
  have huv : Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) ∩
      Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) ⊆ {(x₂ : ℂ), 0} := by
    rw [hau, hav]
    rintro w ⟨hw1 | hw1, ⟨y, hy, rfl⟩⟩
    · obtain ⟨y', hy', hyy⟩ := hw1
      have := ofReal_injective hyy
      left; rw [show y = x₂ by linarith [hy'.2, hy.1]]
    · rcases arcInf_real h.zero₁ h.one₁ h.mem₁ hw1 (by simp) with h' | h'
      · have := ofReal_injective h'; linarith [hy.1, h.lt]
      · right; exact h'
  have huw : Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) ∩
      Foundations.ThetaCurve.arc b₂ ⊆
      {(x₂ : ℂ), 0} := by
    rw [hau, haw]
    rintro w ⟨hw1 | hw1, hw2⟩
    · obtain ⟨y, hy, rfl⟩ := hw1
      rcases arcInf_real h.zero₂ h.one₂ h.mem₂ hw2 (by simp) with h' | h'
      · left; exact h'
      · have := ofReal_eq_zero.1 h'; linarith [hy.2, h.neg]
    · right; exact h.inter ⟨hw1, hw2⟩
  have hvw : Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) ∩
      Foundations.ThetaCurve.arc b₂ ⊆
      {(x₂ : ℂ), 0} := by
    rw [hav, haw]
    rintro w ⟨⟨y, -, rfl⟩, hw2⟩
    exact arcInf_real h.zero₂ h.one₂ h.mem₂ hw2 (by simp)
  have hzΘ : z ∉ Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) ∪
      Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) ∪
      Foundations.ThetaCurve.arc b₂ := by
    rw [hau, hav, haw]
    rintro ((((⟨y, hy, rfl⟩) | hz1) | ⟨y, hy, rfl⟩) | hz2)
    · exact hz (Or.inr ⟨y, ⟨hy.1, hy.2.trans h.neg.le⟩, rfl⟩)
    · exact hz (Or.inl (Or.inl hz1))
    · exact hz (Or.inr ⟨y, ⟨h.lt.le.trans hy.1, hy.2⟩, rfl⟩)
    · exact hz (Or.inl (Or.inr hz2))
  have hmain := Foundations.ThetaCurve.compl_theta_subset hu hv hw huv huw hvw hzΘ
  have E1 : Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) ∪
      Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) =
        b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 := by
    rw [hau, hav, union_right_comm, ← image_union, Icc_union_Icc_eq_Icc h.lt.le h.neg.le,
      union_comm]
  have E2 : Foundations.ThetaCurve.arc (arcJoin (segPath (x₂ : ℂ) (x₁ : ℂ)) b₁) ∪
      Foundations.ThetaCurve.arc b₂ =
      b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂ := by
    rw [hau, haw, union_comm (ofReal '' Icc x₁ x₂), union_assoc, union_assoc,
      union_comm (ofReal '' Icc x₁ x₂)]
  have E3 : Foundations.ThetaCurve.arc (segPath (x₂ : ℂ) ((0 : ℝ) : ℂ)) ∪
      Foundations.ThetaCurve.arc b₂ =
      b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0 := by
    rw [hav, haw, union_comm]
  rw [E1, E2, E3] at hmain
  obtain ⟨hΓ, hΓH⟩ := h.isJordanCurve_face
  obtain ⟨hΞ₁, hΞ₁H⟩ := h.isJordanCurve_side₁
  obtain ⟨hΞ₂, hΞ₂H⟩ := h.isJordanCurve_side₂
  rw [jordanOut_eq_outerSide hΞ₁ hΞ₁H, jordanIn_eq_innerSide hΓ hΓH,
    jordanIn_eq_innerSide hΞ₂ hΞ₂H] at hmain
  rcases hmain with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- **The separation at infinity.** A preconnected subset of `ℍ̄ \ {0}` which avoids the two open
arcs, the central face and `(x₁, x₂)` cannot contain both gates. -/
theorem false_of_isPreconnected {P : Set ℂ} (hP : IsPreconnected P) (hPH : P ⊆ Hbar)
    (hP0 : (0 : ℂ) ∉ P) (hP₁ : Disjoint P (b₁ '' Ioo 0 1)) (hP₂ : Disjoint P (b₂ '' Ioo 0 1))
    (hPF : Disjoint P (innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂)))
    (hPI : Disjoint P (ofReal '' Ioo x₁ x₂)) (hx₁P : (x₁ : ℂ) ∈ P) (hx₂P : (x₂ : ℂ) ∈ P) :
    False := by
  obtain ⟨hΞ₁, hΞ₁H⟩ := h.isJordanCurve_side₁
  obtain ⟨hΞ₂, hΞ₂H⟩ := h.isJordanCurve_side₂
  obtain ⟨-, -, -, hfrO₁, -, hO₁o, hΞ₁c, -, -⟩ := jordan_sides hΞ₁ hΞ₁H
  obtain ⟨-, -, hfrI₂, -, -, -, hΞ₂c, -, -⟩ := jordan_sides hΞ₂ hΞ₂H
  set Ξ₁ := b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0 with hΞ₁def
  set Ξ₂ := b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0 with hΞ₂def
  set K₁ : Set ℂ := (outerSide Ξ₁ ∩ Hbar) ∪ {(x₁ : ℂ)} with hK₁
  set K₂ : Set ℂ := innerSide Ξ₂ ∪ ofReal '' Ico x₂ 0 with hK₂
  have hx₂0 : x₂ ∈ Ico x₂ 0 := ⟨le_rfl, h.neg⟩
  have hnP₁ : ∀ w ∈ P, w ∉ b₁ '' Ioo 0 1 := fun w hw h' => Set.disjoint_left.1 hP₁ hw h'
  have hnP₂ : ∀ w ∈ P, w ∉ b₂ '' Ioo 0 1 := fun w hw h' => Set.disjoint_left.1 hP₂ hw h'
  have hnPI : ∀ w ∈ P, w ∉ ofReal '' Ioo x₁ x₂ := fun w hw h' => Set.disjoint_left.1 hPI hw h'
  -- the real points of `P` on `[x₁, 0]` are `x₁` or in `[x₂, 0)`
  have hreal : ∀ w ∈ P, ∀ y ∈ Icc x₁ 0, w = (y : ℂ) → y = x₁ ∨ y ∈ Ico x₂ 0 := by
    rintro w hw y hy rfl
    rcases eq_or_lt_of_le hy.1 with h1 | h1
    · exact Or.inl h1.symm
    rcases eq_or_lt_of_le hy.2 with h2 | h2
    · exact absurd (by rw [h2, ofReal_zero]) (fun h0 : (y : ℂ) = 0 => hP0 (h0 ▸ hw))
    by_cases h3 : y < x₂
    · exact absurd ⟨y, ⟨h1, h3⟩, rfl⟩ (hnPI _ hw)
    · exact Or.inr ⟨not_lt.1 h3, h2⟩
  -- cover
  have hcover : P ⊆ K₁ ∪ K₂ := by
    intro w hw
    by_cases hwΘ : w ∈ b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0
    · rcases hwΘ with (hw1 | hw1) | ⟨y, hy, rfl⟩
      · rcases mem_arc_trichotomy hw1 with h' | h' | h'
        · left; right; rw [h', h.zero₁]; rfl
        · exact absurd h' (hnP₁ w hw)
        · exact absurd (by rw [h', h.one₁] at hw; exact hw) hP0
      · rcases mem_arc_trichotomy hw1 with h' | h' | h'
        · right; right; rw [h', h.zero₂]; exact ⟨x₂, hx₂0, rfl⟩
        · exact absurd h' (hnP₂ w hw)
        · exact absurd (by rw [h', h.one₂] at hw; exact hw) hP0
      · rcases hreal _ hw y hy rfl with h' | h'
        · left; right; rw [h']; rfl
        · right; right; exact ⟨y, h', rfl⟩
    · rcases h.compl_subset hwΘ with h' | h' | h'
      · exact Or.inl (Or.inl ⟨h', hPH hw⟩)
      · exact absurd h' (Set.disjoint_left.1 hPF hw)
      · exact Or.inr (Or.inl h')
  -- the two pieces are relatively closed
  have hcl₁ : ∀ w ∈ P, w ∈ closure K₁ → w ∈ K₁ := by
    intro w hw hwc
    rw [hK₁, closure_union, closure_singleton] at hwc
    rcases hwc with hwc | hwc
    swap; · exact Or.inr hwc
    have hwO : w ∈ closure (outerSide Ξ₁) := closure_mono inter_subset_left hwc
    rw [closure_eq_self_union_frontier, hfrO₁] at hwO
    rcases hwO with hwO | hwΞ
    · exact Or.inl ⟨hwO, hPH hw⟩
    rcases hwΞ with hw1 | ⟨y, hy, rfl⟩
    · rcases mem_arc_trichotomy hw1 with h' | h' | h'
      · exact Or.inr (by rw [h', h.zero₁]; rfl)
      · exact absurd h' (hnP₁ w hw)
      · exact absurd (by rw [h', h.one₁] at hw; exact hw) hP0
    · rcases hreal _ hw y hy rfl with h' | h'
      · exact Or.inr (by rw [h']; rfl)
      exfalso
      have hy' : y ∈ Ioo x₁ 0 := ⟨h.lt.trans_le h'.1, h'.2⟩
      obtain ⟨ε, hε, hεI⟩ := halfDisc_side h.cont₁ hΞ₁ hΞ₁H h.zero₁ h.one₁ h.mem₁ hy'
      obtain ⟨u, hub, huO, huH⟩ := mem_closure_iff.1 hwc _ isOpen_ball (mem_ball_self hε)
      rcases hεI u hub huH with hu | hu
      · exact disjoint_innerSide_outerSide.le_bot ⟨hu, huO⟩
      · exact outerSide_subset_compl huO (Or.inr hu)
  have hcl₂ : ∀ w ∈ P, w ∈ closure K₂ → w ∈ K₂ := by
    intro w hw hwc
    rw [hK₂, closure_union] at hwc
    have hseg : closure (ofReal '' Ico x₂ 0) ⊆ ofReal '' Icc x₂ 0 :=
      closure_minimal (image_mono Ico_subset_Icc_self)
        (isCompact_Icc.image continuous_ofReal).isClosed
    have hreal₂ : ∀ y ∈ Icc x₂ 0, w = (y : ℂ) → w ∈ K₂ := by
      rintro y hy rfl
      rcases eq_or_lt_of_le hy.2 with h2 | h2
      · exact absurd (by rw [h2, ofReal_zero] at hw; exact hw) hP0
      · exact Or.inr ⟨y, ⟨hy.1, h2⟩, rfl⟩
    rcases hwc with hwc | hwc
    · rw [closure_eq_self_union_frontier, hfrI₂] at hwc
      rcases hwc with hwc | hwΞ
      · exact Or.inl hwc
      rcases hwΞ with hw1 | ⟨y, hy, rfl⟩
      · rcases mem_arc_trichotomy hw1 with h' | h' | h'
        · exact Or.inr ⟨x₂, hx₂0, by rw [h', h.zero₂]⟩
        · exact absurd h' (hnP₂ w hw)
        · exact absurd (by rw [h', h.one₂] at hw; exact hw) hP0
      · exact hreal₂ y hy rfl
    · obtain ⟨y, hy, rfl⟩ := hseg hwc
      exact hreal₂ y hy rfl
  -- the two pieces are disjoint
  have hdisj : ∀ w ∈ P, w ∈ K₁ → w ∈ K₂ → False := by
    intro w hw h1 h2
    rcases h1 with ⟨hwO, -⟩ | hw1
    · rcases h2 with hwI | ⟨y, hy, rfl⟩
      · exact disjoint_innerSide_outerSide.le_bot ⟨h.innerSide_side₂_subset hwI, hwO⟩
      · exact outerSide_subset_compl hwO
          (Or.inr ⟨y, ⟨h.lt.le.trans hy.1, hy.2.le⟩, rfl⟩)
    · rw [mem_singleton_iff] at hw1
      subst hw1
      rcases h2 with hwI | ⟨y, hy, hyx⟩
      · exact not_mem_H_ofReal x₁ (innerSide_subset_H hΞ₂ hΞ₂H hwI)
      · have := ofReal_injective hyx; linarith [hy.1, h.lt]
  obtain ⟨w, hwP, hw1, hw2⟩ := isPreconnected_closed_iff.1 hP (closure K₁) (closure K₂)
    isClosed_closure isClosed_closure
    (hcover.trans (union_subset_union subset_closure subset_closure))
    ⟨x₁, hx₁P, subset_closure (Or.inr rfl)⟩ ⟨x₂, hx₂P, subset_closure (Or.inr ⟨x₂, hx₂0, rfl⟩)⟩
  exact hdisj w hwP (hcl₁ w hwP hw1) (hcl₂ w hwP hw2)

/-- Every point of `(x₁, x₂)` has an upper half-disc in the central face. -/
theorem halfDisc_face {v : ℝ} (hv : v ∈ Ioo x₁ x₂) :
    ∃ ε > 0, ∀ w : ℂ, dist w v < ε → 0 < w.im →
      w ∈ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂) := by
  obtain ⟨hΓ, hΓH⟩ := h.isJordanCurve_face
  have hvb : ∀ {b : ℝ → ℂ} {x : ℝ}, b 0 = x → b 1 = 0 → (∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) →
      x ∉ Ioo x₁ x₂ → (v : ℂ) ∉ b '' Icc 0 1 := by
    intro b x hb0 hb1 hbH hx hv'
    rcases arcInf_real hb0 hb1 hbH hv' (by simp) with h' | h'
    · exact hx (ofReal_injective h' ▸ hv)
    · have := ofReal_eq_zero.1 h'; linarith [hv.2, h.neg]
  obtain ⟨ε₁, hε₁, hε₁b⟩ := exists_ball_disjoint_arc h.cont₁
    (hvb h.zero₁ h.one₁ h.mem₁ (fun hx => lt_irrefl _ hx.1))
  obtain ⟨ε₂, hε₂, hε₂b⟩ := exists_ball_disjoint_arc h.cont₂
    (hvb h.zero₂ h.one₂ h.mem₂ (fun hx => lt_irrefl _ hx.2))
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw hwH => ?_⟩
  refine halfDisc_subset_innerSide_of_real hΓ hΓH (Or.inr ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩)
    (lt_min hε₁ hε₂) (fun u hu hud => ?_) hw hwH
  rcases hu with (hu | hu) | hu
  · exact absurd (hε₁b u hu) (not_le.2 (lt_of_lt_of_le hud (min_le_left _ _)))
  · exact absurd (hε₂b u hu) (not_le.2 (lt_of_lt_of_le hud (min_le_right _ _)))
  · exact im_eq_zero_of_mem_ofReal_image hu

/-- Points of `F̄ \ F` off the open arcs and `0` are gates. -/
theorem gate_of_mem_closure {w : ℂ}
    (hw : w ∈ closure (innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂)))
    (hwF : w ∉ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂))
    (hw₁ : w ∉ b₁ '' Ioo 0 1) (hw₂ : w ∉ b₂ '' Ioo 0 1) (hw0 : w ≠ 0)
    (hwI : w ∉ ofReal '' Ioo x₁ x₂) : w = x₁ ∨ w = x₂ := by
  obtain ⟨hΓ, -⟩ := h.isJordanCurve_face
  rcases mem_of_mem_closure_innerSide (isCompact_of_isJordanCurve hΓ).isClosed hw hwF with
    (hw' | hw') | ⟨y, hy, rfl⟩
  · rcases mem_arc_trichotomy hw' with h' | h' | h'
    · left; rw [h', h.zero₁]
    · exact absurd h' hw₁
    · exact absurd (h'.trans h.one₁) hw0
  · rcases mem_arc_trichotomy hw' with h' | h' | h'
    · right; rw [h', h.zero₂]
    · exact absurd h' hw₂
    · exact absurd (h'.trans h.one₂) hw0
  · rcases eq_or_lt_of_le hy.1 with h1 | h1
    · left; rw [h1]
    rcases eq_or_lt_of_le hy.2 with h2 | h2
    · right; rw [h2]
    · exact absurd ⟨y, ⟨h1, h2⟩, rfl⟩ hwI

/-- The gate values agree (the separation step of Lemma 1.3 at infinity). -/
theorem gate_eq {δ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hδ : ContinuousOn δ (Icc a b))
    (hδH : MapsTo δ (Icc a b) Hbar)
    (hδF : ∀ t ∈ Icc a b,
      δ t ∉ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂))
    (hδB₁ : ∀ t ∈ Icc a b, δ t ∉ b₁ '' Ioo 0 1) (hδB₂ : ∀ t ∈ Icc a b, δ t ∉ b₂ '' Ioo 0 1)
    (hδ0 : ∀ t ∈ Icc a b, δ t ≠ 0) (hδI : ∀ t ∈ Icc a b, δ t ∉ ofReal '' Ioo x₁ x₂)
    (hδa : δ a = x₁ ∨ δ a = x₂) (hδb : δ b = x₁ ∨ δ b = x₂) : δ a = δ b := by
  by_contra hne
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hgates : (x₁ : ℂ) ∈ δ '' Icc a b ∧ (x₂ : ℂ) ∈ δ '' Icc a b := by
    rcases hδa with h1 | h1 <;> rcases hδb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    · exact ⟨⟨b, hb, h2⟩, ⟨a, ha, h1⟩⟩
    · exact absurd (h1.trans h2.symm) hne
  refine h.false_of_isPreconnected (isPreconnected_Icc.image δ hδ)
    (by rintro _ ⟨t, ht, rfl⟩; exact hδH ht) (fun ⟨t, ht, h0⟩ => hδ0 t ht h0) ?_ ?_ ?_ ?_
    hgates.1 hgates.2
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδB₁ t ht
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδB₂ t ht
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδF t ht
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδI t ht

/-- **Lemma 1.3, junction at infinity** (`ψ`-picture, distinct gates `x₁ < x₂`). A continuous path
`δ : [a, b] → ℍ̄ \ {0}` (finite in the original chart) avoiding the central face and the open arcs,
with no nontrivial time interval in `ℝ`, whose endpoints are in `F̄`, has
`δ(a) = δ(b) ∈ {x₁, x₂}`. -/
theorem gate_lemma {δ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hδ : ContinuousOn δ (Icc a b))
    (hδH : MapsTo δ (Icc a b) Hbar)
    (hδF : ∀ t ∈ Icc a b,
      δ t ∉ innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂))
    (hδB₁ : ∀ t ∈ Icc a b, δ t ∉ b₁ '' Ioo 0 1) (hδB₂ : ∀ t ∈ Icc a b, δ t ∉ b₂ '' Ioo 0 1)
    (hδ0 : ∀ t ∈ Icc a b, δ t ≠ 0)
    (hδR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H)
    (hδa : δ a = x₁ ∨ δ a = x₂ ∨
      δ a ∈ closure (innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂)))
    (hδb : δ b ∈ closure (innerSide (b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₁ x₂))) :
    δ a = δ b ∧ (δ a = x₁ ∨ δ a = x₂) := by
  have hI : ∀ t ∈ Icc a b, δ t ∉ ofReal '' Ioo x₁ x₂ := fun t ht =>
    not_mem_Ioo_of_avoid_face hab hδ hδF hδR (fun v hv => h.halfDisc_face hv) ht
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have ha' : δ a = x₁ ∨ δ a = x₂ := by
    rcases hδa with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact h.gate_of_mem_closure h1 (hδF a ha) (hδB₁ a ha) (hδB₂ a ha) (hδ0 a ha) (hI a ha)
  have hb' := h.gate_of_mem_closure hδb (hδF b hb) (hδB₁ b hb) (hδB₂ b hb) (hδ0 b hb) (hI b hb)
  exact ⟨h.gate_eq hab.le hδ hδH hδF hδB₁ hδB₂ hδ0 hI ha' hb', ha'⟩

omit h in
/-- A point of `b '' Ioo 0 1` within `ε` of `b 0`, for an arc continuous at `0`. -/
theorem exists_arcInt_near_start {b : ℝ → ℂ} (hb : ContinuousOn b (Icc 0 1)) {ε : ℝ}
    (hε : 0 < ε) : ∃ t ∈ Ioo (0 : ℝ) 1, dist (b t) (b 0) < ε := by
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 (hb 0 ⟨le_rfl, zero_le_one⟩) ε hε
  set t := min (δ / 2) (1 / 2) with ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩
  refine ⟨t, htI, hδb (Ioo_subset_Icc_self htI) ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos htI.1]
  exact (min_le_left _ _).trans_lt (by linarith)

/-- The open arc `B₁` lies on the outer side of `Ξ₂`. -/
theorem arcInt₁_subset_outerSide₂ :
    b₁ '' Ioo 0 1 ⊆ outerSide (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0) := by
  obtain ⟨hΞ₂, hΞ₂H⟩ := h.isJordanCurve_side₂
  obtain ⟨-, -, -, -, -, hO₂o, -, -, -⟩ := jordan_sides hΞ₂ hΞ₂H
  have hpre : IsPreconnected (b₁ '' Ioo 0 1) :=
    isPreconnected_Ioo.image _ (h.cont₁.mono Ioo_subset_Icc_self)
  have hsub : b₁ '' Ioo 0 1 ⊆ (b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ (hw | hw)
    · have h0 := h.inter ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, hw⟩
      rw [mem_singleton_iff] at h0
      have h1 : (0 : ℝ) < (b₁ t).im := h.mem₁ t ht
      rw [h0] at h1; simp at h1
    · have h1 : (0 : ℝ) < (b₁ t).im := h.mem₁ t ht
      rw [im_eq_zero_of_mem_ofReal_image hw] at h1; exact lt_irrefl _ h1
  have hx₁Ξ₂ : (x₁ : ℂ) ∉ b₂ '' Icc 0 1 ∪ ofReal '' Icc x₂ 0 := by
    rintro (hx | ⟨y, hy, hyx⟩)
    · rcases arcInf_real h.zero₂ h.one₂ h.mem₂ hx (by simp) with h' | h'
      · have := ofReal_injective h'; linarith [h.lt]
      · have := ofReal_eq_zero.1 h'; linarith [h.lt, h.neg]
    · have := ofReal_injective hyx; linarith [hy.1, h.lt]
  have hx₁O := ofReal_mem_outerSide hΞ₂ hΞ₂H hx₁Ξ₂
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO₂o _ hx₁O
  obtain ⟨t, htI, htd⟩ := exists_arcInt_near_start h.cont₁ hε
  rw [h.zero₁] at htd
  have htO := hεO htd
  have h1 := hpre.subset_connectedComponentIn ⟨t, htI, rfl⟩ hsub
  rw [outerSide, connectedComponentIn_eq htO]
  exact h1

/-- The open arc `B₂` lies on the inner side of `Ξ₁`. -/
theorem arcInt₂_subset_innerSide₁ :
    b₂ '' Ioo 0 1 ⊆ innerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) := by
  obtain ⟨hΞ₁, hΞ₁H⟩ := h.isJordanCurve_side₁
  obtain ⟨⟨z₁, -, hin⟩, -, -, -, -, -, -, -, -⟩ := jordan_sides hΞ₁ hΞ₁H
  have hpre : IsPreconnected (b₂ '' Ioo 0 1) :=
    isPreconnected_Ioo.image _ (h.cont₂.mono Ioo_subset_Icc_self)
  have hsub : b₂ '' Ioo 0 1 ⊆ (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ (hw | hw)
    · have h0 := h.inter ⟨hw, ⟨t, Ioo_subset_Icc_self ht, rfl⟩⟩
      rw [mem_singleton_iff] at h0
      have h1 : (0 : ℝ) < (b₂ t).im := h.mem₂ t ht
      rw [h0] at h1; simp at h1
    · have h1 : (0 : ℝ) < (b₂ t).im := h.mem₂ t ht
      rw [im_eq_zero_of_mem_ofReal_image hw] at h1; exact lt_irrefl _ h1
  obtain ⟨ε, hε, hεI⟩ := halfDisc_side h.cont₁ hΞ₁ hΞ₁H h.zero₁ h.one₁ h.mem₁
    (v := x₂) ⟨h.lt, h.neg⟩
  obtain ⟨t, htI, htd⟩ := exists_arcInt_near_start h.cont₂ hε
  rw [h.zero₂] at htd
  have htH : (0 : ℝ) < (b₂ t).im := h.mem₂ t htI
  have htIn : b₂ t ∈ innerSide (b₁ '' Icc 0 1 ∪ ofReal '' Icc x₁ 0) := by
    rcases hεI _ htd htH.le with h' | h'
    · exact h'
    · rw [im_eq_zero_of_mem_ofReal_image h'] at htH; exact absurd htH (lt_irrefl _)
  have h1 := hpre.subset_connectedComponentIn ⟨t, htI, rfl⟩ hsub
  rw [hin] at htIn ⊢
  rw [connectedComponentIn_eq htIn]
  exact h1

end IsArcPairInf

end Inf

end InteractingSLE.Sec6
