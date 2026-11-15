/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionContacts
import LQGMetric.Complex.JordanMapCurve

/-!
# The Jordan lens of two adjacent minimal contacts (§7.2: Aux. lemma 68, last assertion)

Packet PROVE-SEC7-B. Aux. lemma 68 (p. 273) ends: "In the plane, the two subarcs in part 4 form a
Jordan curve" — gluing the two injective subarcs `α([a, c])` and `β([d, b])` along their two distinct
common endpoints gives a continuous injection of the circle. Jordan curves are LQGMetric's
`LQGMetric.JordanMap.IsJordanCurve` (the image of the unit circle under a map continuous and injective
on it), the notion used by the project's Jordan and Schoenflies theorems
(`InteractingSLE.Foundations.Jordan.jordan_curve_components_complex`).

* `isJordanCurve_image_union`: two injective paths `u, v : [0, 1] → ℂ` with the same endpoints and no
  other common point form a Jordan curve (`γ(w) = u((1 - Re w)/2)` on the closed
  upper unit half-circle and `v((1 - Re w)/2)` on the lower one).
* `isJordanCurve_adjacent_minimalContacts`: the Jordan lens of two adjacent minimal contacts.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace InteractingSLE

namespace Sec7

/-! ### Two arcs with common endpoints form a Jordan curve -/

/-- The parameter `(1 - Re w)/2 ∈ [0, 1]` of a point of the unit circle. -/
def circleParam (w : ℂ) : ℝ := (1 - w.re) / 2

theorem re_mul_add_im_mul_of_mem_sphere {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w.re * w.re + w.im * w.im = 1 := by
  have h : ‖w‖ ^ 2 = 1 := by rw [mem_sphere_zero_iff_norm.mp hw, one_pow]
  rw [Complex.sq_norm, Complex.normSq_apply] at h
  exact h

theorem circleParam_mem_Icc {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) : circleParam w ∈ Icc 0 1 := by
  have h := abs_le.mp ((Complex.abs_re_le_norm w).trans (mem_sphere_zero_iff_norm.mp hw).le)
  constructor <;> unfold circleParam <;> linarith [h.1, h.2]

/-- On the unit circle, the parameter is `0` or `1` exactly at the real points `±1`. -/
theorem im_eq_zero_iff_circleParam {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w.im = 0 ↔ circleParam w = 0 ∨ circleParam w = 1 := by
  have h := re_mul_add_im_mul_of_mem_sphere hw
  unfold circleParam
  constructor
  · intro him
    rw [him, mul_zero, add_zero] at h
    rcases mul_self_eq_one_iff.mp h with h' | h'
    · left; rw [h']; norm_num
    · right; rw [h']; norm_num
  · intro hp
    have hre : w.re * w.re = 1 := by
      rcases hp with hp | hp
      · have : w.re = 1 := by linarith
        rw [this, one_mul]
      · have : w.re = -1 := by linarith
        rw [this]; norm_num
    have : w.im * w.im = 0 := by linarith
    exact mul_self_eq_zero.mp this

/-- A point of the unit circle is determined by its real part and the sign of its imaginary part. -/
theorem eq_of_re_eq_of_mem_sphere {w w' : ℂ} (hw : w ∈ sphere (0 : ℂ) 1)
    (hw' : w' ∈ sphere (0 : ℂ) 1) (hre : w.re = w'.re) (hsign : (0 ≤ w.im ∧ 0 ≤ w'.im) ∨
      (w.im ≤ 0 ∧ w'.im ≤ 0)) : w = w' := by
  have h := re_mul_add_im_mul_of_mem_sphere hw
  have h' := re_mul_add_im_mul_of_mem_sphere hw'
  have him : w.im * w.im = w'.im * w'.im := by rw [hre] at h; linarith
  refine Complex.ext hre ?_
  rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (mul_self_inj h1 h2).mp him
  · have hneg : (-w.im) * (-w.im) = (-w'.im) * (-w'.im) := by
      rw [neg_mul_neg, neg_mul_neg]
      exact him
    have := (mul_self_inj (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)).mp hneg
    linarith

/-- The point `(1 - 2x) ± i√(1 - (1 - 2x)²)` of the unit circle with parameter `x`. -/
theorem exists_mem_sphere_circleParam_eq {x : ℝ} (hx : x ∈ Icc 0 1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ w ∈ sphere (0 : ℂ) 1, circleParam w = x ∧ 0 ≤ σ * w.im := by
  set r := 1 - 2 * x
  have hr : 0 ≤ 1 - r * r := by nlinarith [hx.1, hx.2]
  refine ⟨⟨r, σ * Real.sqrt (1 - r * r)⟩, ?_, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm]
    have h : ‖(⟨r, σ * Real.sqrt (1 - r * r)⟩ : ℂ)‖ ^ 2 = 1 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp only
      have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have := Real.mul_self_sqrt hr
      nlinarith [this, hσ2]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h
  · simp only [circleParam, r]
    ring
  · dsimp only
    rcases hσ with rfl | rfl
    · rw [one_mul, one_mul]; exact Real.sqrt_nonneg _
    · nlinarith [Real.sqrt_nonneg (1 - r * r)]

/-- **Gluing two arcs.** Two injective continuous paths `u, v : [0, 1] → ℂ` with common endpoints
`u 0 = v 0`, `u 1 = v 1` (distinct, by injectivity) and no other common point form a Jordan curve. -/
theorem isJordanCurve_image_union {u v : ℝ → ℂ} (hu : ContinuousOn u (Icc 0 1))
    (hv : ContinuousOn v (Icc 0 1)) (hui : InjOn u (Icc 0 1)) (hvi : InjOn v (Icc 0 1))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1}) :
    LQGMetric.JordanMap.IsJordanCurve (u '' Icc 0 1 ∪ v '' Icc 0 1) := by
  classical
  set γ : ℂ → ℂ := fun w => if 0 ≤ w.im then u (circleParam w) else v (circleParam w) with hγ
  have hpc : Continuous circleParam := by
    unfold circleParam
    fun_prop
  -- off the two real points `±1`, the parameter is interior; at them `u` and `v` agree
  have huv : ∀ w ∈ sphere (0 : ℂ) 1, w.im = 0 → u (circleParam w) = v (circleParam w) := by
    intro w hw him
    rcases (im_eq_zero_iff_circleParam hw).mp him with h | h <;> rw [h]
    · exact h0
    · exact h1
  -- parameters `0` and `1` of `v` only at the real points
  have hv01 : ∀ x ∈ Icc (0 : ℝ) 1, v x ∈ ({u 0, u 1} : Set ℂ) → x = 0 ∨ x = 1 := by
    rintro x hx (h | h)
    · exact Or.inl (hvi hx ⟨le_rfl, zero_le_one⟩ (h.trans h0))
    · exact Or.inr (hvi hx ⟨zero_le_one, le_rfl⟩ (h.trans h1))
  refine ⟨γ, ?_, ?_, ?_⟩
  · -- continuity, on the closed upper and lower half-circles
    have hU : IsClosed (sphere (0 : ℂ) 1 ∩ {w | 0 ≤ w.im}) :=
      isClosed_sphere.inter (isClosed_le continuous_const Complex.continuous_im)
    have hL : IsClosed (sphere (0 : ℂ) 1 ∩ {w | w.im ≤ 0}) :=
      isClosed_sphere.inter (isClosed_le Complex.continuous_im continuous_const)
    have hcU : ContinuousOn γ (sphere (0 : ℂ) 1 ∩ {w | 0 ≤ w.im}) := by
      refine (hu.comp hpc.continuousOn fun w hw => circleParam_mem_Icc hw.1).congr fun w hw => ?_
      simp only [hγ, Function.comp_apply]
      exact ite_eq_left hw.2
    have hcL : ContinuousOn γ (sphere (0 : ℂ) 1 ∩ {w | w.im ≤ 0}) := by
      refine (hv.comp hpc.continuousOn fun w hw => circleParam_mem_Icc hw.1).congr fun w hw => ?_
      simp only [hγ, Function.comp_apply]
      split_ifs with h
      · exact huv w hw.1 (le_antisymm hw.2 h)
      · rfl
    have hsplit : sphere (0 : ℂ) 1 =
        (sphere (0 : ℂ) 1 ∩ {w | 0 ≤ w.im}) ∪ (sphere (0 : ℂ) 1 ∩ {w | w.im ≤ 0}) := by
      rw [← inter_union_distrib_left]
      exact (inter_eq_left.mpr fun w _ => le_total 0 w.im).symm
    rw [hsplit]
    exact hcU.union_of_isClosed hcL hU hL
  · -- injectivity
    intro w hw w' hw' hww'
    have hp := circleParam_mem_Icc hw
    have hp' := circleParam_mem_Icc hw'
    have hre : circleParam w = circleParam w' → w.re = w'.re := fun h => by
      unfold circleParam at h; linarith
    simp only [hγ] at hww'
    split_ifs at hww' with h h' h'
    · exact eq_of_re_eq_of_mem_sphere hw hw' (hre (hui hp hp' hww')) (Or.inl ⟨h, h'⟩)
    · exfalso
      have hm : v (circleParam w') ∈ ({u 0, u 1} : Set ℂ) :=
        hint ⟨⟨_, hp, hww'⟩, ⟨_, hp', rfl⟩⟩
      exact h' ((im_eq_zero_iff_circleParam hw').mpr (hv01 _ hp' hm)).symm.le
    · exfalso
      have hm : v (circleParam w) ∈ ({u 0, u 1} : Set ℂ) :=
        hint ⟨⟨_, hp', hww'.symm⟩, ⟨_, hp, rfl⟩⟩
      exact h ((im_eq_zero_iff_circleParam hw).mpr (hv01 _ hp hm)).symm.le
    · exact eq_of_re_eq_of_mem_sphere hw hw' (hre (hvi hp hp' hww'))
        (Or.inr ⟨(not_le.mp h).le, (not_le.mp h').le⟩)
  · -- the image
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      simp only [hγ]
      split_ifs
      · exact Or.inl ⟨_, circleParam_mem_Icc hw, rfl⟩
      · exact Or.inr ⟨_, circleParam_mem_Icc hw, rfl⟩
    · rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · obtain ⟨w, hw, hpx, him⟩ := exists_mem_sphere_circleParam_eq hx 1 (Or.inl rfl)
        rw [one_mul] at him
        refine ⟨w, hw, ?_⟩
        simp only [hγ]
        rw [ite_eq_left him, hpx]
      · obtain ⟨w, hw, hpx, him⟩ := exists_mem_sphere_circleParam_eq hx (-1) (Or.inr rfl)
        refine ⟨w, hw, ?_⟩
        simp only [hγ]
        split_ifs with h
        · rw [← hpx]
          exact huv w hw (le_antisymm (by linarith) h)
        · rw [hpx]

/-! ### The Jordan lens of two adjacent minimal contacts -/

/-- The increasing affine parameter `x ↦ p + (q - p)x` of `[p, q]`, as a map into `ℝ≥0`. -/
def segParam (p q : ℝ≥0) (x : ℝ) : ℝ≥0 := Real.toNNReal ((p : ℝ) + ((q : ℝ) - p) * x)

theorem continuous_segParam (p q : ℝ≥0) : Continuous (segParam p q) := by
  unfold segParam
  fun_prop

theorem segParam_zero (p q : ℝ≥0) : segParam p q 0 = p := by
  simp only [segParam, mul_zero, add_zero, Real.toNNReal_coe]

theorem segParam_one (p q : ℝ≥0) : segParam p q 1 = q := by
  simp only [segParam, mul_one, add_sub_cancel, Real.toNNReal_coe]

theorem coe_segParam {p q : ℝ≥0} (hpq : p ≤ q) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (segParam p q x : ℝ) = p + (q - p) * x := by
  have hpq' : (p : ℝ) ≤ q := hpq
  unfold segParam
  rw [Real.coe_toNNReal _ (by linarith [mul_nonneg (sub_nonneg.mpr hpq') hx.1, NNReal.coe_nonneg p])]

theorem segParam_mem_Icc {p q : ℝ≥0} (hpq : p ≤ q) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    segParam p q x ∈ Icc p q := by
  have hpq' : (p : ℝ) ≤ q := hpq
  have h := coe_segParam hpq hx
  constructor
  · rw [← NNReal.coe_le_coe, h]
    linarith [mul_nonneg (sub_nonneg.mpr hpq') hx.1]
  · rw [← NNReal.coe_le_coe, h]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr hpq')]

theorem injOn_segParam {p q : ℝ≥0} (hpq : p < q) : InjOn (segParam p q) (Icc 0 1) := by
  intro x hx y hy hxy
  have hpq' : (0 : ℝ) < (q : ℝ) - p := sub_pos.mpr hpq
  have h := congrArg (fun z : ℝ≥0 => (z : ℝ)) hxy
  simp only [coe_segParam hpq.le hx, coe_segParam hpq.le hy, add_right_inj] at h
  exact mul_left_cancel₀ hpq'.ne' h

theorem image_segParam {p q : ℝ≥0} (hpq : p ≤ q) : segParam p q '' Icc 0 1 = Icc p q := by
  refine Subset.antisymm (image_subset_iff.mpr fun x hx => segParam_mem_Icc hpq hx) ?_
  have h := intermediate_value_Icc (zero_le_one' ℝ) (continuous_segParam p q).continuousOn
  rwa [segParam_zero, segParam_one] at h

/-- **Aux. lemma 68 (4)**, last assertion: in the plane, the two subarcs `α([a, c])` and `β([d, b])`
between two adjacent minimal contacts `(a, b)`, `(c, d)` form a Jordan curve. -/
theorem isJordanCurve_adjacent_minimalContacts {α β : ℝ≥0 → ℂ} {A B : ℝ≥0}
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) {a b c d : ℝ≥0} (hab : (a, b) ∈ minimalContacts α A β B)
    (hcd : (c, d) ∈ minimalContacts α A β B) (hac : a < c)
    (hgap : ∀ p ∈ minimalContacts α A β B, p.1 ∉ Ioo a c) :
    LQGMetric.JordanMap.IsJordanCurve (α '' Icc a c ∪ β '' Icc d b) := by
  have hdb : d < b := snd_lt_of_mem_minimalContacts hab hcd hac
  have hsep := (adjacent_minimalContacts hα hβ hab hcd hac hgap).1
  have hcA : Icc a c ⊆ Icc 0 A := fun s hs => ⟨zero_le, hs.2.trans hcd.1.1.2⟩
  have hbB : Icc d b ⊆ Icc 0 B := fun t ht => ⟨zero_le, ht.2.trans hab.1.2.1.2⟩
  have hflip : (fun x : ℝ => 1 - x) '' Icc 0 1 = Icc 0 1 := by
    rw [image_const_sub_Icc, sub_zero, sub_self]
  set u : ℝ → ℂ := fun x => α (segParam a c x) with hu
  set v : ℝ → ℂ := fun x => β (segParam d b (1 - x)) with hv
  have huI : u '' Icc 0 1 = α '' Icc a c := by
    rw [hu, ← image_image α (segParam a c), image_segParam hac.le]
  have hvI : v '' Icc 0 1 = β '' Icc d b := by
    rw [hv, ← image_image β (fun x => segParam d b (1 - x)), ← image_image (segParam d b)
      (fun x : ℝ => 1 - x), hflip, image_segParam hdb.le]
  have hu0 : u 0 = α a := by simp only [hu, segParam_zero]
  have hu1 : u 1 = α c := by simp only [hu, segParam_one]
  have hv0 : v 0 = β b := by simp only [hv, sub_zero, segParam_one]
  have hv1 : v 1 = β d := by simp only [hv, sub_self, segParam_zero]
  have hmaps₁ : MapsTo (segParam a c) (Icc 0 1) (Icc a c) := fun x hx => segParam_mem_Icc hac.le hx
  have hmaps₂ : MapsTo (fun x : ℝ => segParam d b (1 - x)) (Icc 0 1) (Icc d b) := fun x hx =>
    segParam_mem_Icc hdb.le ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [← huI, ← hvI]
  refine isJordanCurve_image_union ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hα.mono hcA).comp (continuous_segParam a c).continuousOn hmaps₁
  · exact (hβ.mono hbB).comp ((continuous_segParam d b).comp (continuous_const.sub
      continuous_id)).continuousOn hmaps₂
  · exact (hαi.mono hcA).comp (injOn_segParam hac) hmaps₁
  · refine (hβi.mono hbB).comp (fun x hx y hy hxy => ?_) hmaps₂
    have := injOn_segParam hdb ⟨by linarith [hx.2], by linarith [hx.1]⟩
      ⟨by linarith [hy.2], by linarith [hy.1]⟩ hxy
    linarith
  · rw [hu0, hv0]; exact hab.1.2.2
  · rw [hu1, hv1]; exact hcd.1.2.2
  · rw [huI, hvI, hsep, hu0, hu1]

end Sec7

end InteractingSLE
