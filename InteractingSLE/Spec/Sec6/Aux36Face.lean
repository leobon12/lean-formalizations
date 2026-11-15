/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Gate
import InteractingSLE.Foundations.Loewner.HullBasic

/-!
# The central face of a fixed chart (Aux. lemma 36, chart-face geometry): the planar part

Specification §6.2, **Aux.** lemma 36 (`source/spec/p193-240.md` L36–L78, p. 195): "Map `D_T` to
the half-plane using its original target at infinity. ... These faces are exactly the image of
`E_T`. Indeed, inside `D_T` the only portions of `∂C` are the two incoming arcs. Crossing from the
selected face to another part of `D_T` would cross one of them." In the ZTip-elimination note
(ruling R41, §1.1) this is the confinement (1.1) `η(t) ∈ C, δ_r(t) ∈ ℍ ⇒ δ_r(t) ∈ F_r` together
with `f̄_r(F_r) ⊆ C`.

This file proves the planar statement behind both, for a Jordan curve `J ⊆ ℍ̄` whose real points
form an interval `[q₁, q₂]` (the face boundary `A₁ ∪ A₂ ∪ [q₁, q₂]`, or `A₁ ∪ A₂` when
`q₁ = q₂`).

## Main results

* `mem_outerSide_of_norm_gt`: far points are outer;
* `isPreconnected_outerSide_inter_H`: the outer side meets `ℍ` in a connected set;
* `mem_innerSide_iff`: **the face identification.** Let `F` be continuous on `ℍ` with bounded
  displacement `‖F w − w‖ ≤ K`, and `C` open and bounded. If `F` maps `J ∩ ℍ` off `C`, every
  point of `ℍ` mapped to `∂C` is on `J`, and `F(ℍ)` meets `C`, then for `w ∈ ℍ`,
  `F w ∈ C ↔ w ∈ innerSide J`.

## Proof of the connectivity

A component `V` of `outerSide J ∩ ℍ` is not closed in the connected `outerSide J` (it misses
`-i`), so its closure has a point `x` of `outerSide J` off `ℍ`, i.e. a real point off `J`, hence
outside `[q₁, q₂]`. A thin rectangle over a real segment from `x` away from `[q₁, q₂]` avoids `J`,
meets `V` near `x`, and reaches the far region, which lies in one component.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

section Planar

variable {J : Set ℂ}

/-- **Far points are outer.** -/
theorem mem_outerSide_of_norm_gt (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar)
    {M : ℝ} (hM : ∀ w ∈ J, ‖w‖ ≤ M) {w : ℂ} (hw : M < ‖w‖) : w ∈ outerSide J := by
  set R := ‖w‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg w
  set A := circPath R (arg w) 0 '' Icc 0 1 with hA
  have hAJ : A ⊆ Jᶜ := by
    rintro _ ⟨t, -, rfl⟩ hJ'
    have := hM _ hJ'
    rw [norm_circPath hR0] at this
    linarith
  have hRmem : ((R : ℝ) : ℂ) ∉ J := fun h => by
    have := hM _ h
    rw [norm_real, Real.norm_of_nonneg hR0] at this
    linarith
  have hRO : ((R : ℝ) : ℂ) ∈ outerSide J := ofReal_mem_outerSide hJ hJH hRmem
  have hA1 : ((R : ℝ) : ℂ) ∈ A := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [circPath_one]; simp⟩
  have hA0 : w ∈ A := ⟨0, ⟨le_rfl, zero_le_one⟩, by
    rw [circPath_zero]; exact norm_mul_exp_arg_mul_I w⟩
  have hApre : IsPreconnected A :=
    isPreconnected_Icc.image _ (continuous_circPath _ _ _).continuousOn
  have h1 := hApre.subset_connectedComponentIn hA1 hAJ
  rw [outerSide, connectedComponentIn_eq hRO]
  exact h1 hA0

/-- Far points of `ℍ` lie in the component of `(M + 1) i` in `outerSide J ∩ ℍ`. -/
theorem mem_connectedComponentIn_outerSide_of_le_norm (hJ : LQGMetric.JordanMap.IsJordanCurve J)
    (hJH : J ⊆ Hbar) {M : ℝ} (hM0 : 0 < M) (hM : ∀ w ∈ J, ‖w‖ < M) {z : ℂ} (hz : z ∈ H)
    (hzM : M ≤ ‖z‖) :
    z ∈ connectedComponentIn (outerSide J ∩ H) (((M + 1 : ℝ) : ℂ) * I) := by
  have hJb : J ⊆ ball 0 M := fun w hw => mem_ball_zero_iff.2 (hM w hw)
  have h1 := mem_connectedComponentIn_of_le_norm hM0 hJb hz hzM
  set p₀ : ℂ := ((M + 1 : ℝ) : ℂ) * I with hp₀
  have hp₀n : ‖p₀‖ = M + 1 := by
    rw [hp₀, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg (by linarith)]
  have hp₀H : p₀ ∈ H := by
    show 0 < p₀.im
    simp only [hp₀, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hp₀J : p₀ ∉ J := fun h => by have := hM _ h; linarith
  have hp₀O : p₀ ∈ outerSide J :=
    mem_outerSide_of_norm_gt hJ hJH (fun w hw => (hM w hw).le) (by linarith)
  have hK : connectedComponentIn (H \ J) p₀ ⊆ outerSide J ∩ H := by
    intro y hy
    have hsub : connectedComponentIn (H \ J) p₀ ⊆ Jᶜ := fun u hu =>
      (connectedComponentIn_subset _ _ hu).2
    have h2 := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (show p₀ ∈ H \ J from ⟨hp₀H, hp₀J⟩)) hsub
    refine ⟨?_, (connectedComponentIn_subset _ _ hy).1⟩
    rw [outerSide, connectedComponentIn_eq hp₀O]
    exact h2 hy
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (show p₀ ∈ H \ J from ⟨hp₀H, hp₀J⟩)) hK h1

/-- `dist z (re z) = |im z|`. -/
theorem dist_ofReal_re (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  have h : z - (z.re : ℂ) = (z.im : ℂ) * I := by apply Complex.ext <;> simp
  rw [dist_eq_norm, h, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]

/-- A thin rectangle over a real segment `[l, h]` off `J`, whose interior point `x` is adherent to
a component `V` of `outerSide J ∩ ℍ`, lies in `V`. -/
theorem rect_subset_connectedComponentIn (hJc : IsClosed J) {l h x : ℝ} (hlx : l < x)
    (hxh : x < h) (hseg : ∀ y ∈ Icc l h, (y : ℂ) ∉ J) {w : ℂ}
    (hx : (x : ℂ) ∈ closure (connectedComponentIn (outerSide J ∩ H) w)) :
    ∃ ρ > 0, {z : ℂ | l < z.re ∧ z.re < h ∧ 0 < z.im ∧ z.im < ρ} ⊆
      connectedComponentIn (outerSide J ∩ H) w := by
  set S₀ : Set ℂ := ofReal '' Icc l h with hS₀
  have hS₀c : IsCompact S₀ := isCompact_Icc.image continuous_ofReal
  obtain ⟨ρ, hρ, hthick⟩ := hS₀c.exists_thickening_subset_open hJc.isOpen_compl
    (by rintro _ ⟨y, hy, rfl⟩; exact hseg y hy)
  set ρ' := min ρ (min (x - l) (h - x)) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min (by linarith) (by linarith))
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'l : ρ' ≤ x - l := (min_le_right _ _).trans (min_le_left _ _)
  have hρ'h : ρ' ≤ h - x := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ', hρ'pos, ?_⟩
  set Rect : Set ℂ := {z : ℂ | l < z.re ∧ z.re < h ∧ 0 < z.im ∧ z.im < ρ'} with hRect
  have hRpre : IsPreconnected Rect :=
    ((convex_halfSpace_re_gt (r := l)).inter ((convex_halfSpace_re_lt (r := h)).inter
      ((convex_halfSpace_im_gt (r := 0)).inter (convex_halfSpace_im_lt (r := ρ'))))).isPreconnected
  have hRJ : Rect ⊆ Jᶜ := by
    intro z hz
    refine hthick (mem_thickening_iff.2 ⟨(z.re : ℂ), ⟨z.re, ⟨hz.1.le, hz.2.1.le⟩, rfl⟩, ?_⟩)
    rw [dist_ofReal_re, abs_of_pos hz.2.2.1]
    linarith [hz.2.2.2]
  have hRH : Rect ⊆ H := fun z hz => hz.2.2.1
  -- a point of `V` in the rectangle
  obtain ⟨v, hvb, hvV⟩ := mem_closure_iff.1 hx _ isOpen_ball (mem_ball_self hρ'pos)
  have hvOH : v ∈ outerSide J ∩ H := connectedComponentIn_subset _ _ hvV
  have hvR : v ∈ Rect := by
    rw [mem_ball] at hvb
    have hre : |v.re - x| < ρ' := by
      have := abs_re_le_norm (v - x)
      rw [sub_re, ofReal_re] at this
      rw [dist_eq_norm] at hvb
      linarith
    have him : v.im < ρ' := by
      have := abs_im_le_norm (v - x)
      rw [sub_im, ofReal_im, sub_zero] at this
      rw [dist_eq_norm] at hvb
      linarith [le_abs_self v.im]
    rw [abs_lt] at hre
    exact ⟨by linarith, by linarith, hvOH.2, him⟩
  have hRO : Rect ⊆ outerSide J := by
    have h1 := hRpre.subset_connectedComponentIn hvR hRJ
    rw [outerSide, connectedComponentIn_eq hvOH.1]
    exact h1
  have h2 := hRpre.subset_connectedComponentIn hvR (subset_inter hRO hRH)
  rw [connectedComponentIn_eq hvV]
  exact h2

/-- **The outer side meets `ℍ` in one component**: every point of `outerSide J ∩ ℍ` lies in the
component of the far point `(M + 1) i`, for a Jordan curve `J ⊆ ℍ̄` inside `ball 0 M` whose real
points are exactly `[q₁, q₂]`. -/
theorem outerSide_inter_H_subset (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar)
    {q₁ q₂ : ℝ} (hJR : ∀ x : ℝ, (x : ℂ) ∈ J ↔ x ∈ Icc q₁ q₂) {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ w ∈ J, ‖w‖ < M) :
    outerSide J ∩ H ⊆ connectedComponentIn (outerSide J ∩ H) (((M + 1 : ℝ) : ℂ) * I) := by
  obtain ⟨-, -, -, -, -, hOo, hJc, -, hOp⟩ := jordan_sides hJ hJH
  have hOHo : IsOpen (outerSide J ∩ H) := hOo.inter QuantumZipper.isOpen_H
  rintro w ⟨hwO, hwH⟩
  set V := connectedComponentIn (outerSide J ∩ H) w with hV
  have hwV : w ∈ V := mem_connectedComponentIn ⟨hwO, hwH⟩
  have hVo : IsOpen V := hOHo.connectedComponentIn
  have hVsub : V ⊆ outerSide J ∩ H := connectedComponentIn_subset _ _
  -- it suffices to find a far point in `V`
  suffices hfar : ∃ z ∈ V, z ∈ H ∧ M ≤ ‖z‖ by
    obtain ⟨z, hzV, hzH, hzM⟩ := hfar
    have h1 := mem_connectedComponentIn_outerSide_of_le_norm hJ hJH hM0 hM hzH hzM
    rw [connectedComponentIn_eq h1, ← connectedComponentIn_eq hzV]
    exact hwV
  -- step A: the closure of `V` has a point of `outerSide J` off `ℍ`
  obtain ⟨x, hxV, hxO, hxH⟩ : ∃ x ∈ closure V, x ∈ outerSide J ∧ x ∉ H := by
    by_contra hcon
    push Not at hcon
    have hcl : closure V ∩ outerSide J ⊆ V := by
      rintro y ⟨hyV, hyO⟩
      have hyH := hcon y hyV hyO
      obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hOHo y ⟨hyO, hyH⟩
      obtain ⟨v, hvb, hvV⟩ := mem_closure_iff.1 hyV _ isOpen_ball (mem_ball_self hε)
      have h1 := (convex_ball y ε).isPreconnected.subset_connectedComponentIn hvb hεs
      rw [← connectedComponentIn_eq hvV] at h1
      exact h1 (mem_ball_self hε)
    have hOV := hOp.subset_of_closure_inter_subset hVo ⟨w, hwO, hwV⟩ hcl
    have hI : (-I : ℂ) ∈ V := hOV (lowerHalf_subset_outerSide hJH neg_I_im)
    have : (0 : ℝ) < (-I : ℂ).im := (hVsub hI).2
    linarith [neg_I_im]
  -- step B: `x` is a real point outside `[q₁, q₂]`
  have hxim : x.im = 0 := by
    have hcl : closure V ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => (show (0 : ℝ) < z.im from (hVsub hz).2).le)
        (isClosed_le continuous_const Complex.continuous_im)
    have h1 : 0 ≤ x.im := hcl hxV
    have h2 : ¬ (0 < x.im) := hxH
    linarith [not_lt.1 h2]
  have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hxim])
  have hxJ : x ∉ J := outerSide_subset_compl hxO
  rw [hxr] at hxV hxJ
  have hxI : x.re ∉ Icc q₁ q₂ := fun h => hxJ ((hJR _).2 h)
  rw [mem_Icc, not_and_or, not_le, not_le] at hxI
  set X := x.re with hX
  have hMX : 0 ≤ M + |X| := by positivity
  rcases hxI with hlt | hgt
  · -- go left
    obtain ⟨ρ, hρ, hR⟩ := rect_subset_connectedComponentIn (J := J) hJc (l := X - (M + 2 + |X|))
      (h := (X + q₁) / 2) (x := X) (by linarith) (by linarith)
      (fun y hy h => by have := ((hJR y).1 h).1; linarith [hy.2]) hxV
    refine ⟨((X - (M + 3 / 2 + |X|) : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I, hR ?_, ?_, ?_⟩
    · simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_zero, add_im, mul_im, zero_add, add_zero]
      refine ⟨by linarith, by linarith [le_abs_self X], by linarith, by linarith⟩
    · show (0 : ℝ) < (((X - (M + 3 / 2 + |X|) : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith
    · refine le_trans ?_ (abs_re_le_norm _)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero]
      rw [abs_of_neg (by linarith [le_abs_self X])]
      linarith [le_abs_self X]
  · -- go right
    obtain ⟨ρ, hρ, hR⟩ := rect_subset_connectedComponentIn (J := J) hJc (l := (X + q₂) / 2)
      (h := X + (M + 2 + |X|)) (x := X) (by linarith) (by linarith)
      (fun y hy h => by have := ((hJR y).1 h).2; linarith [hy.1]) hxV
    refine ⟨((X + (M + 3 / 2 + |X|) : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I, hR ?_, ?_, ?_⟩
    · simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_zero, add_im, mul_im, zero_add, add_zero]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · show (0 : ℝ) < (((X + (M + 3 / 2 + |X|) : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith
    · refine le_trans ?_ (abs_re_le_norm _)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero]
      rw [abs_of_pos (by linarith [neg_abs_le X])]
      linarith [neg_abs_le X]

/-- `outerSide J ∩ ℍ` is preconnected (same hypotheses as `outerSide_inter_H_subset`). -/
theorem isPreconnected_outerSide_inter_H (hJ : LQGMetric.JordanMap.IsJordanCurve J)
    (hJH : J ⊆ Hbar) {q₁ q₂ : ℝ} (hJR : ∀ x : ℝ, (x : ℂ) ∈ J ↔ x ∈ Icc q₁ q₂) :
    IsPreconnected (outerSide J ∩ H) := by
  obtain ⟨M, hM⟩ := (isCompact_of_isJordanCurve hJ).isBounded.exists_norm_le
  have h := outerSide_inter_H_subset hJ hJH hJR (M := |M| + 1) (by positivity)
    (fun w hw => lt_of_le_of_lt ((hM w hw).trans (le_abs_self M)) (lt_add_one _))
  rw [subset_antisymm h (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn

/-- A preconnected set whose `F`-image avoids `∂C` and meets the open set `C` is mapped into `C`. -/
theorem mapsTo_of_isPreconnected {C S : Set ℂ} {F : ℂ → ℂ} (hC : IsOpen C)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hfr : ∀ s ∈ S, F s ∉ frontier C)
    {s₀ : ℂ} (hs₀ : s₀ ∈ S) (hs₀C : F s₀ ∈ C) : ∀ s ∈ S, F s ∈ C := by
  have hFS : IsPreconnected (F '' S) := hS.image F hF
  have hsub : F '' S ⊆ C ∪ (closure C)ᶜ := by
    rintro _ ⟨s, hs, rfl⟩
    by_cases h : F s ∈ C
    · exact Or.inl h
    · refine Or.inr fun hcl => hfr s hs ?_
      rw [frontier, hC.interior_eq]
      exact ⟨hcl, h⟩
  have h := hFS.subset_left_of_subset_union hC isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun _ h1 h2 => h2 (subset_closure h1)) hsub
    ⟨F s₀, ⟨s₀, hs₀, rfl⟩, hs₀C⟩
  exact fun s hs => h ⟨s, hs, rfl⟩

/-- **The face identification** (the planar core of Aux. lemma 36's "these faces are exactly the
image of `E_T`", and of (1.1) with `f̄_r(F_r) ⊆ C` in ruling R41's note). Let `J ⊆ ℍ̄` be a Jordan
curve whose real points are `[q₁, q₂]`, `C` open and bounded, and `F` continuous on `ℍ` with
`‖F w − w‖ ≤ K`. Suppose `F` maps `J ∩ ℍ` off `C`, every point of `ℍ` mapped to `∂C` is on `J`,
and `F(ℍ)` meets `C`. Then a point `w ∈ ℍ` is mapped into `C` iff it is on the inner side of
`J`. -/
theorem mem_innerSide_iff {C : Set ℂ} {F : ℂ → ℂ} (hJ : LQGMetric.JordanMap.IsJordanCurve J)
    (hJH : J ⊆ Hbar) {q₁ q₂ : ℝ} (hJR : ∀ x : ℝ, (x : ℂ) ∈ J ↔ x ∈ Icc q₁ q₂) (hC : IsOpen C)
    (hCb : IsBounded C) (hF : ContinuousOn F H) {K : ℝ} (hK : ∀ w ∈ H, ‖F w - w‖ ≤ K)
    (hJC : ∀ w ∈ J, w ∈ H → F w ∉ C) (hfr : ∀ w ∈ H, F w ∈ frontier C → w ∈ J)
    (hCF : ∃ p ∈ H, F p ∈ C) {w : ℂ} (hw : w ∈ H) : F w ∈ C ↔ w ∈ innerSide J := by
  obtain ⟨-, -, -, -, -, -, -, hIp, -⟩ := jordan_sides hJ hJH
  have fwd : ∀ w ∈ H, F w ∈ C → w ∈ innerSide J := by
    intro w hw hFw
    have hwJ : w ∉ J := fun h => hJC w h hw hFw
    have h' : w ∈ Jᶜ := hwJ
    rw [compl_eq_innerSide_union_outerSide] at h'
    refine h'.resolve_right fun hwO => ?_
    have hall := mapsTo_of_isPreconnected hC (isPreconnected_outerSide_inter_H hJ hJH hJR)
      (hF.mono inter_subset_right)
      (fun s hs hsC => outerSide_subset_compl hs.1 (hfr s hs.2 hsC)) ⟨hwO, hw⟩ hFw
    obtain ⟨B, hB⟩ := hCb.exists_norm_le
    obtain ⟨Mj, hMj⟩ := (isCompact_of_isJordanCurve hJ).isBounded.exists_norm_le
    set R := max |Mj| (|B| + |K|) + 1 with hR
    set z : ℂ := ((R : ℝ) : ℂ) * I with hz
    have hRpos : 0 < R := by positivity
    have hzn : ‖z‖ = R := by
      rw [hz, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hRpos.le]
    have hzH : z ∈ H := by
      show 0 < z.im
      simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      exact hRpos
    have hzO : z ∈ outerSide J :=
      mem_outerSide_of_norm_gt hJ hJH hMj (by
        rw [hzn]; linarith [le_max_left |Mj| (|B| + |K|), le_abs_self Mj])
    have hFz := hB _ (hall z ⟨hzO, hzH⟩)
    have h1 := hK z hzH
    have h2 := norm_sub_norm_le z (F z)
    rw [norm_sub_rev] at h2
    linarith [le_max_right |Mj| (|B| + |K|), le_abs_self B, le_abs_self K]
  refine ⟨fwd w hw, fun hwI => ?_⟩
  obtain ⟨p, hpH, hpC⟩ := hCF
  exact mapsTo_of_isPreconnected hC hIp (hF.mono (innerSide_subset_H hJ hJH))
    (fun s hs hsC => innerSide_subset_compl hs (hfr s (innerSide_subset_H hJ hJH hs) hsC))
    (fwd p hpH hpC) hpC w hwI

end Planar

end InteractingSLE.Sec6
