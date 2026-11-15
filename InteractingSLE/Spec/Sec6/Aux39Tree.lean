/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Sep

/-!
# The incoming tree in a fixed chart separates the two gates

Lemma 1.3 of the ZTip-elimination note (ruling R41), finite-junction case, planar step: in a
half-plane chart the incoming tree consists of two simple arms `A₁, A₂` from the real gates
`q₁ < q₂` to an interior junction `z` and a third arm `A₃` from `z` towards infinity. Its central
face `F` is the inner side of `Γ = A₁ ∪ A₂ ∪ [q₁, q₂]`. A preconnected subset of `ℍ̄` avoiding `F`,
the open arms, the junction, the third arm and `(q₁, q₂)` cannot contain both gates.

Here the third arm is truncated at a radius `R` beyond the set: `A₃` runs from `z` to a point `e`
with `‖e‖ = R`. The exterior curves are closed through segments of `ℝ` and arcs of the circle of
radius `R`:
`Ξ₁ = A₁ ∪ A₃ ∪ [−R, q₁] ∪ (arc from −R to e)`, `Ξ₂ = A₂ ∪ A₃ ∪ [q₂, R] ∪ (arc from R to e)`,
and the abstract separation `false_of_isPreconnected_gates` applies.

## Main result

* `false_of_isPreconnected_tree`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-! ### Points of the closing pieces -/

theorem mem_H_iff_im_pos {w : ℂ} : w ∈ H ↔ 0 < w.im := Iff.rfl

theorem ofReal_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := by
  show 0 ≤ (x : ℂ).im; simp

theorem not_mem_H_ofReal (x : ℝ) : (x : ℂ) ∉ H := by
  intro h; have : (0 : ℝ) < (x : ℂ).im := h; simp at this

/-- A sphere point of `ℍ̄` lies on one of the two closing arcs `circPath R 0 θ` (from `R` to `e`)
and `circPath R π θ` (from `−R` to `e`), `θ = arg e ∈ (0, π)`. -/
theorem mem_circArcs_of_norm_eq {R θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) {w : ℂ}
    (hw : ‖w‖ = R) (hwim : 0 ≤ w.im) :
    w ∈ circPath R 0 θ '' Icc 0 1 ∨ w ∈ circPath R Real.pi θ '' Icc 0 1 := by
  have hpi := Real.pi_pos
  set φ := arg w with hφ
  have hφ0 : 0 ≤ φ := arg_nonneg_iff.2 hwim
  have hφπ : φ ≤ Real.pi := arg_le_pi w
  have hw' : w = (R : ℂ) * exp ((φ : ℂ) * I) := by
    rw [← hw]; exact (norm_mul_exp_arg_mul_I w).symm
  rcases le_total φ θ with h | h
  · left
    refine ⟨φ / θ, ⟨div_nonneg hφ0 hθ.1.le, (div_le_one hθ.1).2 h⟩, ?_⟩
    have hang : (0 + φ / θ * (θ - 0) : ℝ) = φ := by
      rw [zero_add, sub_zero]; exact div_mul_cancel₀ φ hθ.1.ne'
    rw [hw', circPath, hang]
  · right
    have hd : 0 < Real.pi - θ := by linarith [hθ.2]
    refine ⟨(Real.pi - φ) / (Real.pi - θ), ⟨div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith)⟩, ?_⟩
    have hang : (Real.pi + (Real.pi - φ) / (Real.pi - θ) * (θ - Real.pi) : ℝ) = φ := by
      have hd' : Real.pi - θ ≠ 0 := hd.ne'
      field_simp
      ring
    rw [hw', circPath, hang]

/-- Real points of `circPath R 0 θ` (`θ ∈ (0, π)`): only its start `R`. -/
theorem circPath_zero_real {R θ t : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 Real.pi)
    (ht : t ∈ Icc (0 : ℝ) 1) (him : (circPath R 0 θ t).im = 0) : t = 0 := by
  rw [im_circPath] at him
  have hs : Real.sin (0 + t * (θ - 0)) = 0 := (mul_eq_zero.1 him).resolve_left hR.ne'
  by_contra ht0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hpos : 0 < Real.sin (0 + t * (θ - 0)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [hθ.1]
    · nlinarith [hθ.2, ht.2, Real.pi_pos]
  linarith

/-- Real points of `circPath R π θ` (`θ ∈ (0, π)`): only its start `−R`. -/
theorem circPath_pi_real {R θ t : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 Real.pi)
    (ht : t ∈ Icc (0 : ℝ) 1) (him : (circPath R Real.pi θ t).im = 0) : t = 0 := by
  rw [im_circPath] at him
  have hs : Real.sin (Real.pi + t * (θ - Real.pi)) = 0 := (mul_eq_zero.1 him).resolve_left hR.ne'
  by_contra ht0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hpos : 0 < Real.sin (Real.pi + t * (θ - Real.pi)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [hθ.1, ht.2, Real.pi_pos]
    · nlinarith [hθ.2]
  linarith

theorem circPath_zero_start {R θ : ℝ} : circPath R 0 θ 0 = (R : ℂ) := by
  simp [circPath]

theorem circPath_pi_start {R θ : ℝ} : circPath R Real.pi θ 0 = -(R : ℂ) := by
  simp [circPath, exp_pi_mul_I]

theorem circPath_end {R θ₀ θ : ℝ} {e : ℂ} (he : e = (R : ℂ) * exp ((θ : ℂ) * I)) :
    circPath R θ₀ θ 1 = e := by
  rw [circPath_one, he]

/-- The two closing arcs meet only at `e`. -/
theorem circArcs_inter {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo 0 Real.pi) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (h : circPath R 0 θ t = circPath R Real.pi θ s) : t = 1 ∧ s = 1 := by
  have hpi := Real.pi_pos
  have htθ : t * θ ≤ θ := mul_le_of_le_one_left hθ.1.le ht.2
  have htθ0 : 0 ≤ t * θ := mul_nonneg ht.1 hθ.1.le
  have hsθ : s * (Real.pi - θ) ≤ Real.pi - θ := mul_le_of_le_one_left (by linarith [hθ.2]) hs.2
  have hsθ0 : 0 ≤ s * (Real.pi - θ) := mul_nonneg hs.1 (by linarith [hθ.2])
  have h1 : 0 + t * (θ - 0) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by rw [zero_add, sub_zero]; linarith, by rw [zero_add, sub_zero]; linarith [hθ.2]⟩
  have h2 : Real.pi + s * (θ - Real.pi) ∈ Ioc (-Real.pi) Real.pi := by
    have e : s * (θ - Real.pi) = -(s * (Real.pi - θ)) := by ring
    rw [e]; constructor <;> linarith [hθ.1]
  have := eq_of_mul_exp_eq hR h1 h2 h
  -- `t θ = π + s (θ − π)`, with `t θ ≤ θ ≤ π + s (θ − π)`
  have ha : t * θ ≤ θ := by nlinarith [hθ.1, ht.2]
  have hb : θ ≤ Real.pi + s * (θ - Real.pi) := by nlinarith [hθ.2, hs.2]
  constructor
  · by_contra ht1
    have : t < 1 := lt_of_le_of_ne ht.2 ht1
    have : t * θ < θ := by nlinarith [hθ.1]
    linarith
  · by_contra hs1
    have : s < 1 := lt_of_le_of_ne hs.2 hs1
    have : θ < Real.pi + s * (θ - Real.pi) := by nlinarith [hθ.2]
    linarith

theorem im_eq_zero_of_mem_ofReal_image {S : Set ℝ} {w : ℂ} (hw : w ∈ ofReal '' S) : w.im = 0 := by
  obtain ⟨x, -, rfl⟩ := hw; simp

theorem norm_eq_of_mem_circPath_image {R θ₀ θ₁ : ℝ} (hR : 0 ≤ R) {w : ℂ}
    (hw : w ∈ circPath R θ₀ θ₁ '' Icc 0 1) : ‖w‖ = R := by
  obtain ⟨t, -, rfl⟩ := hw; exact norm_circPath hR θ₀ θ₁ t

theorem im_nonneg_circPath {R θ₀ θ₁ t : ℝ} (hR : 0 ≤ R) (h₀ : θ₀ ∈ Icc 0 Real.pi)
    (h₁ : θ₁ ∈ Icc 0 Real.pi) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (circPath R θ₀ θ₁ t).im := by
  rw [im_circPath]
  refine mul_nonneg hR (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · have := circPath_angle_mem (θ₀ := θ₀) (θ₁ := θ₁) ht
    rcases le_total θ₀ θ₁ with h | h
    · rw [uIcc_of_le h] at this; linarith [this.1, h₀.1]
    · rw [uIcc_of_ge h] at this; linarith [this.1, h₁.1]
  · have := circPath_angle_mem (θ₀ := θ₀) (θ₁ := θ₁) ht
    rcases le_total θ₀ θ₁ with h | h
    · rw [uIcc_of_le h] at this; linarith [this.2, h₁.2]
    · rw [uIcc_of_ge h] at this; linarith [this.2, h₀.2]

theorem image_Icc_eq_Ico_union {f : ℝ → ℂ} : f '' Icc 0 1 = f '' Ico 0 1 ∪ {f 1} := by
  rw [← Ico_union_right zero_le_one, image_union, image_singleton]

theorem isPreconnected_image_Ico {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) :
    IsPreconnected (f '' Ico 0 1) :=
  isPreconnected_Ico.image f (hf.mono Ico_subset_Icc_self)

theorem isPreconnected_image_Icc {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) :
    IsPreconnected (f '' Icc 0 1) :=
  isPreconnected_Icc.image f hf

/-- **The incoming tree separates the two gates** (finite junction, third arm truncated at
radius `R`): a preconnected subset of `ℍ̄ ∩ ball 0 R` containing both gates `q₁ < q₂` meets the
central face `F = innerSide Γ`, the (truncated) third arm, or `(q₁, q₂)`. (It may touch the two
selected arms.) -/
theorem false_of_isPreconnected_tree {q₁ q₂ R : ℝ} {z e : ℂ} {a₁ a₂ a₃ : ℝ → ℂ}
    (hq : q₁ < q₂) (hR : 0 < R)
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₃ : ContinuousOn a₃ (Icc 0 1)) (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1))
    (ha₃i : InjOn a₃ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z)
    (ha₂1 : a₂ 1 = z) (ha₃0 : a₃ 0 = z) (ha₃1 : a₃ 1 = e)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₃H : ∀ t ∈ Icc (0 : ℝ) 1, a₃ t ∈ H) (ha₁B : ∀ t ∈ Icc (0 : ℝ) 1, ‖a₁ t‖ < R)
    (ha₂B : ∀ t ∈ Icc (0 : ℝ) 1, ‖a₂ t‖ < R) (ha₃B : ∀ t ∈ Ico (0 : ℝ) 1, ‖a₃ t‖ < R)
    (he : ‖e‖ = R) (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z})
    (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Icc 0 1 ⊆ {z}) (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Icc 0 1 ⊆ {z})
    {P : Set ℂ} (hP : IsPreconnected P) (hPB : P ⊆ ball 0 R) (hPH : P ⊆ Hbar)
    (hq₁P : (q₁ : ℂ) ∈ P) (hq₂P : (q₂ : ℂ) ∈ P)
    (hPF : Disjoint P (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂)))
    (hP₃ : Disjoint P (a₃ '' Icc 0 1)) (hPI : Disjoint P (ofReal '' Ioo q₁ q₂)) : False := by
  have hpi := Real.pi_pos
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set A₁ := a₁ '' Icc 0 1 with hA₁
  set A₂ := a₂ '' Icc 0 1 with hA₂
  set A₃ := a₃ '' Icc 0 1 with hA₃
  -- the gates are inside the disc
  have hq₁R : |q₁| < R := by
    have := ha₁B 0 hI0; rwa [ha₁0, norm_real, Real.norm_eq_abs] at this
  have hq₂R : |q₂| < R := by
    have := ha₂B 0 hI0; rwa [ha₂0, norm_real, Real.norm_eq_abs] at this
  have hq₁R' := abs_lt.1 hq₁R
  have hq₂R' := abs_lt.1 hq₂R
  -- the end of the third arm
  have heH : e ∈ H := ha₃1 ▸ ha₃H 1 hI1
  set θ := arg e with hθdef
  have hθ : θ ∈ Ioo 0 Real.pi := by
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le (arg_nonneg_iff.2 (le_of_lt (show (0:ℝ) < e.im from heH))) with h | h
      · exact h
      · exfalso
        have := (arg_eq_zero_iff.1 h.symm).2
        have h' : (0 : ℝ) < e.im := heH
        linarith
    · exact arg_lt_pi_iff.2 (Or.inr (ne_of_gt (show (0:ℝ) < e.im from heH)))
  have he' : e = (R : ℂ) * exp ((θ : ℂ) * I) := by
    rw [← he]; exact (norm_mul_exp_arg_mul_I e).symm
  have hθ0 : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, hpi.le⟩
  have hθπ : Real.pi ∈ Icc 0 Real.pi := ⟨hpi.le, le_rfl⟩
  have hθm : θ ∈ Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  -- point classification
  have hA₁r : ∀ w ∈ A₁, w.im = 0 → w = q₁ := by
    rintro _ ⟨t, ht, rfl⟩ him
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ha₁0]
    · have : (0 : ℝ) < (a₁ t).im := ha₁H t ⟨h, ht.2⟩
      linarith
  have hA₂r : ∀ w ∈ A₂, w.im = 0 → w = q₂ := by
    rintro _ ⟨t, ht, rfl⟩ him
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ha₂0]
    · have : (0 : ℝ) < (a₂ t).im := ha₂H t ⟨h, ht.2⟩
      linarith
  have hA₃H : ∀ w ∈ A₃, 0 < w.im := by
    rintro _ ⟨t, ht, rfl⟩; exact ha₃H t ht
  have hA₁B : ∀ w ∈ A₁, ‖w‖ < R := by rintro _ ⟨t, ht, rfl⟩; exact ha₁B t ht
  have hA₂B : ∀ w ∈ A₂, ‖w‖ < R := by rintro _ ⟨t, ht, rfl⟩; exact ha₂B t ht
  have hA₃e : ∀ w ∈ A₃, ‖w‖ = R → w = e := by
    rintro _ ⟨t, ht, rfl⟩ hn
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, ha₃1]
    · exact absurd hn (ne_of_lt (ha₃B t ⟨ht.1, h⟩))
  -- the closing pieces
  set Seg₀ : Set ℂ := ofReal '' Icc q₁ q₂ with hSeg₀
  set Seg₁ : Set ℂ := ofReal '' Icc (-R) q₁ with hSeg₁
  set Seg₂ : Set ℂ := ofReal '' Icc q₂ R with hSeg₂
  set C₁ : Set ℂ := circPath R Real.pi θ '' Icc 0 1 with hC₁
  set C₂ : Set ℂ := circPath R 0 θ '' Icc 0 1 with hC₂
  have hC₁n : ∀ w ∈ C₁, ‖w‖ = R := fun w hw => norm_eq_of_mem_circPath_image hR.le hw
  have hC₂n : ∀ w ∈ C₂, ‖w‖ = R := fun w hw => norm_eq_of_mem_circPath_image hR.le hw
  have hC₁r : ∀ w ∈ C₁, w.im = 0 → w = -(R : ℂ) := by
    rintro _ ⟨t, ht, rfl⟩ him
    rw [circPath_pi_real hR hθ ht him, circPath_pi_start]
  have hC₂r : ∀ w ∈ C₂, w.im = 0 → w = (R : ℂ) := by
    rintro _ ⟨t, ht, rfl⟩ him
    rw [circPath_zero_real hR hθ ht him, circPath_zero_start]
  have hC₁₂ : ∀ w ∈ C₁, w ∈ C₂ → w = e := by
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    obtain ⟨-, hs1⟩ := circArcs_inter hR hθ ht hs hts
    rw [hs1, circPath_end he']
  have hC₁H : C₁ ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩; exact im_nonneg_circPath hR.le hθπ hθm ht
  have hC₂H : C₂ ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩; exact im_nonneg_circPath hR.le hθ0 hθm ht
  have hSegr : ∀ {S : Set ℝ} {w : ℂ}, w ∈ ofReal '' S → w.im = 0 :=
    fun hw => im_eq_zero_of_mem_ofReal_image hw
  have hSegH : ∀ S : Set ℝ, ofReal '' S ⊆ Hbar := by
    rintro S _ ⟨x, -, rfl⟩; exact ofReal_mem_Hbar x
  have hA₁H : A₁ ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ha₁0]; exact ofReal_mem_Hbar q₁
    · exact (show (0 : ℝ) < (a₁ t).im from ha₁H t ⟨h, ht.2⟩).le
  have hA₂H : A₂ ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ha₂0]; exact ofReal_mem_Hbar q₂
    · exact (show (0 : ℝ) < (a₂ t).im from ha₂H t ⟨h, ht.2⟩).le
  have hA₃H' : A₃ ⊆ Hbar := fun w hw => le_of_lt (hA₃H w hw)
  -- membership in real segments
  have hmemSeg : ∀ {x y w : ℝ}, (w : ℂ) ∈ ofReal '' Icc x y ↔ w ∈ Icc x y := by
    intro x y w
    constructor
    · rintro ⟨v, hv, hvw⟩; rw [ofReal_injective hvw] at hv; exact hv
    · intro hw; exact ⟨w, hw, rfl⟩
  have hzA₃ : z ∈ A₃ := ⟨0, hI0, ha₃0⟩
  have heA₃ : e ∈ A₃ := ⟨1, hI1, ha₃1⟩
  have hzA₁ : z ∈ A₁ := ⟨1, hI1, ha₁1⟩
  have hzA₂ : z ∈ A₂ := ⟨1, hI1, ha₂1⟩
  have hq₁A₁ : (q₁ : ℂ) ∈ A₁ := ⟨0, hI0, ha₁0⟩
  have hq₂A₂ : (q₂ : ℂ) ∈ A₂ := ⟨0, hI0, ha₂0⟩
  -- the curve `Ξ₁`
  have hjv₁ : segPath (q₁ : ℂ) ((-R : ℝ) : ℂ) 1 = circPath R Real.pi θ 0 := by
    rw [segPath_one, circPath_pi_start]; push_cast; ring
  have hSeg₁img : segPath (q₁ : ℂ) ((-R : ℝ) : ℂ) '' Icc 0 1 = Seg₁ :=
    image_segPath_ofReal' (by linarith)
  have hΞ₁J : LQGMetric.JordanMap.IsJordanCurve (A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁)) := by
    have hJ := Sec7.isJordanCurve_image_union (u := arcJoin a₁ a₃)
      (v := arcJoin (segPath (q₁ : ℂ) ((-R : ℝ) : ℂ)) (circPath R Real.pi θ))
      (continuousOn_arcJoin ha₁ ha₃ (ha₁1.trans ha₃0.symm))
      (continuousOn_arcJoin (continuous_segPath _ _).continuousOn
        (continuous_circPath _ _ _).continuousOn hjv₁)
      (injOn_arcJoin ha₁i ha₃i (ha₁1.trans ha₃0.symm)
        fun w hw => by rw [mem_singleton_iff, ha₁1]; exact h13 hw)
      (injOn_arcJoin (injOn_segPath (by
          intro h; have := congrArg Complex.re h; simp at this; linarith))
        (injOn_circPath hR (ne_of_gt hθ.2) hθπ hθm) hjv₁ (by
          rintro w ⟨hw1, hw2⟩
          rw [hSeg₁img] at hw1
          rw [mem_singleton_iff, segPath_one, hC₁r w hw2 (hSegr hw1)]; push_cast; ring))
      (by rw [arcJoin_zero, arcJoin_zero, segPath_zero, ha₁0])
      (by rw [arcJoin_one, arcJoin_one, ha₃1, circPath_end he'])
      (by
        rw [image_arcJoin (ha₁1.trans ha₃0.symm), image_arcJoin hjv₁, hSeg₁img, arcJoin_zero,
          arcJoin_one, ha₁0, ha₃1]
        rintro w ⟨hw1 | hw1, hw2 | hw2⟩
        · exact Or.inl (hA₁r w hw1 (hSegr hw2))
        · exact absurd (hC₁n w hw2) (ne_of_lt (hA₁B w hw1))
        · exact absurd (hSegr hw2) (ne_of_gt (hA₃H w hw1))
        · exact Or.inr (hA₃e w hw1 (hC₁n w hw2)))
    rwa [image_arcJoin (ha₁1.trans ha₃0.symm), image_arcJoin hjv₁, hSeg₁img] at hJ
  -- the curve `Ξ₂`
  have hjv₂ : segPath (q₂ : ℂ) (R : ℂ) 1 = circPath R 0 θ 0 := by
    rw [segPath_one, circPath_zero_start]
  have hSeg₂img : segPath (q₂ : ℂ) (R : ℂ) '' Icc 0 1 = Seg₂ :=
    image_segPath_ofReal (by linarith)
  have hΞ₂J : LQGMetric.JordanMap.IsJordanCurve (A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂)) := by
    have hJ := Sec7.isJordanCurve_image_union (u := arcJoin a₂ a₃)
      (v := arcJoin (segPath (q₂ : ℂ) (R : ℂ)) (circPath R 0 θ))
      (continuousOn_arcJoin ha₂ ha₃ (ha₂1.trans ha₃0.symm))
      (continuousOn_arcJoin (continuous_segPath _ _).continuousOn
        (continuous_circPath _ _ _).continuousOn hjv₂)
      (injOn_arcJoin ha₂i ha₃i (ha₂1.trans ha₃0.symm)
        fun w hw => by rw [mem_singleton_iff, ha₂1]; exact h23 hw)
      (injOn_arcJoin (injOn_segPath (by
          intro h; have := congrArg Complex.re h; simp at this; linarith))
        (injOn_circPath hR (ne_of_lt hθ.1) hθ0 hθm) hjv₂ (by
          rintro w ⟨hw1, hw2⟩
          rw [hSeg₂img] at hw1
          rw [mem_singleton_iff, segPath_one, hC₂r w hw2 (hSegr hw1)]))
      (by rw [arcJoin_zero, arcJoin_zero, segPath_zero, ha₂0])
      (by rw [arcJoin_one, arcJoin_one, ha₃1, circPath_end he'])
      (by
        rw [image_arcJoin (ha₂1.trans ha₃0.symm), image_arcJoin hjv₂, hSeg₂img, arcJoin_zero,
          arcJoin_one, ha₂0, ha₃1]
        rintro w ⟨hw1 | hw1, hw2 | hw2⟩
        · exact Or.inl (hA₂r w hw1 (hSegr hw2))
        · exact absurd (hC₂n w hw2) (ne_of_lt (hA₂B w hw1))
        · exact absurd (hSegr hw2) (ne_of_gt (hA₃H w hw1))
        · exact Or.inr (hA₃e w hw1 (hC₂n w hw2)))
    rwa [image_arcJoin (ha₂1.trans ha₃0.symm), image_arcJoin hjv₂, hSeg₂img] at hJ
  -- the curve `Γ`
  have hjvΓ : segPath (q₁ : ℂ) (q₂ : ℂ) 1 = a₂ 0 := by rw [segPath_one, ha₂0]
  have hSeg₀img : segPath (q₁ : ℂ) (q₂ : ℂ) '' Icc 0 1 = Seg₀ := image_segPath_ofReal hq.le
  have hΓJ : LQGMetric.JordanMap.IsJordanCurve (A₁ ∪ A₂ ∪ Seg₀) := by
    have hJ := Sec7.isJordanCurve_image_union (u := a₁)
      (v := arcJoin (segPath (q₁ : ℂ) (q₂ : ℂ)) a₂) ha₁
      (continuousOn_arcJoin (continuous_segPath _ _).continuousOn ha₂ hjvΓ) ha₁i
      (injOn_arcJoin (injOn_segPath (by
          intro h; have := congrArg Complex.re h; simp at this; linarith)) ha₂i hjvΓ (by
          rintro w ⟨hw1, hw2⟩
          rw [hSeg₀img] at hw1
          rw [mem_singleton_iff, segPath_one, hA₂r w hw2 (hSegr hw1)]))
      (by rw [arcJoin_zero, segPath_zero, ha₁0])
      (by rw [arcJoin_one, ha₁1, ha₂1])
      (by
        rw [image_arcJoin hjvΓ, hSeg₀img, ha₁0, ha₁1]
        rintro w ⟨hw1, hw2 | hw2⟩
        · exact Or.inl (hA₁r w hw1 (hSegr hw2))
        · exact Or.inr (h12 ⟨hw1, hw2⟩))
    rw [image_arcJoin hjvΓ, hSeg₀img] at hJ
    have e : A₁ ∪ (Seg₀ ∪ A₂) = A₁ ∪ A₂ ∪ Seg₀ := by
      rw [union_comm Seg₀ A₂, union_assoc]
    rwa [e] at hJ
  -- the pieces `S₁`, `S₂`
  set B₁ := a₁ '' Ico 0 1 with hB₁
  set B₂ := a₂ '' Ico 0 1 with hB₂
  set D₁ := circPath R Real.pi θ '' Ico 0 1 with hD₁
  set D₂ := circPath R 0 θ '' Ico 0 1 with hD₂
  have hA₁eq : A₁ = B₁ ∪ {z} := by rw [hA₁, image_Icc_eq_Ico_union, ha₁1]
  have hA₂eq : A₂ = B₂ ∪ {z} := by rw [hA₂, image_Icc_eq_Ico_union, ha₂1]
  have hC₁eq : C₁ = D₁ ∪ {e} := by rw [hC₁, image_Icc_eq_Ico_union, circPath_end he']
  have hC₂eq : C₂ = D₂ ∪ {e} := by rw [hC₂, image_Icc_eq_Ico_union, circPath_end he']
  have hB₁z : ∀ w ∈ B₁, w ≠ z := by
    rintro _ ⟨t, ht, rfl⟩ h
    have := ha₁i (Ico_subset_Icc_self ht) hI1 (h.trans ha₁1.symm)
    exact absurd this (ne_of_lt ht.2)
  have hB₂z : ∀ w ∈ B₂, w ≠ z := by
    rintro _ ⟨t, ht, rfl⟩ h
    have := ha₂i (Ico_subset_Icc_self ht) hI1 (h.trans ha₂1.symm)
    exact absurd this (ne_of_lt ht.2)
  have hD₁e : ∀ w ∈ D₁, w ≠ e := by
    rintro _ ⟨t, ht, rfl⟩ h
    have := injOn_circPath hR (ne_of_gt hθ.2) hθπ hθm (Ico_subset_Icc_self ht) hI1
      (h.trans (circPath_end he').symm)
    exact absurd this (ne_of_lt ht.2)
  have hD₂e : ∀ w ∈ D₂, w ≠ e := by
    rintro _ ⟨t, ht, rfl⟩ h
    have := injOn_circPath hR (ne_of_lt hθ.1) hθ0 hθm (Ico_subset_Icc_self ht) hI1
      (h.trans (circPath_end he').symm)
    exact absurd this (ne_of_lt ht.2)
  have hB₁A₁ : B₁ ⊆ A₁ := image_mono Ico_subset_Icc_self
  have hB₂A₂ : B₂ ⊆ A₂ := image_mono Ico_subset_Icc_self
  have hD₁C₁ : D₁ ⊆ C₁ := image_mono Ico_subset_Icc_self
  have hD₂C₂ : D₂ ⊆ C₂ := image_mono Ico_subset_Icc_self
  have hΞ₁eq : A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁) = (B₁ ∪ Seg₁ ∪ D₁) ∪ A₃ := by
    apply Subset.antisymm
    · rintro w ((hw | hw) | hw | hw)
      · rw [hA₁eq] at hw
        rcases hw with hw | hw
        · exact Or.inl (Or.inl (Or.inl hw))
        · rw [mem_singleton_iff] at hw; rw [hw]; exact Or.inr hzA₃
      · exact Or.inr hw
      · exact Or.inl (Or.inl (Or.inr hw))
      · rw [hC₁eq] at hw
        rcases hw with hw | hw
        · exact Or.inl (Or.inr hw)
        · rw [mem_singleton_iff] at hw; rw [hw]; exact Or.inr heA₃
    · rintro w (((hw | hw) | hw) | hw)
      · exact Or.inl (Or.inl (hB₁A₁ hw))
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (hD₁C₁ hw))
      · exact Or.inl (Or.inr hw)
  have hΞ₂eq : A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂) = (B₂ ∪ Seg₂ ∪ D₂) ∪ A₃ := by
    apply Subset.antisymm
    · rintro w ((hw | hw) | hw | hw)
      · rw [hA₂eq] at hw
        rcases hw with hw | hw
        · exact Or.inl (Or.inl (Or.inl hw))
        · rw [mem_singleton_iff] at hw; rw [hw]; exact Or.inr hzA₃
      · exact Or.inr hw
      · exact Or.inl (Or.inl (Or.inr hw))
      · rw [hC₂eq] at hw
        rcases hw with hw | hw
        · exact Or.inl (Or.inr hw)
        · rw [mem_singleton_iff] at hw; rw [hw]; exact Or.inr heA₃
    · rintro w (((hw | hw) | hw) | hw)
      · exact Or.inl (Or.inl (hB₂A₂ hw))
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (hD₂C₂ hw))
      · exact Or.inl (Or.inr hw)
  have hq₁Seg₁ : (q₁ : ℂ) ∈ Seg₁ := hmemSeg.2 ⟨by linarith, le_rfl⟩
  have hq₂Seg₂ : (q₂ : ℂ) ∈ Seg₂ := hmemSeg.2 ⟨le_rfl, by linarith⟩
  have hnRSeg₁ : (-(R : ℂ)) ∈ Seg₁ := by
    have : ((-R : ℝ) : ℂ) ∈ Seg₁ := hmemSeg.2 ⟨le_rfl, by linarith⟩
    simpa using this
  have hRSeg₂ : (R : ℂ) ∈ Seg₂ := hmemSeg.2 ⟨by linarith, le_rfl⟩
  have hS₁p : IsPreconnected (B₁ ∪ Seg₁ ∪ D₁) := by
    have h1 : IsPreconnected (B₁ ∪ Seg₁) :=
      IsPreconnected.union (q₁ : ℂ) ⟨0, ⟨le_rfl, zero_lt_one⟩, ha₁0⟩ hq₁Seg₁
        (isPreconnected_image_Ico ha₁) (isPreconnected_Icc.image _ continuous_ofReal.continuousOn)
    exact IsPreconnected.union (-(R : ℂ)) (Or.inr hnRSeg₁)
      ⟨0, ⟨le_rfl, zero_lt_one⟩, circPath_pi_start⟩ h1
      (isPreconnected_image_Ico (continuous_circPath _ _ _).continuousOn)
  have hS₂p : IsPreconnected (B₂ ∪ Seg₂ ∪ D₂) := by
    have h1 : IsPreconnected (B₂ ∪ Seg₂) :=
      IsPreconnected.union (q₂ : ℂ) ⟨0, ⟨le_rfl, zero_lt_one⟩, ha₂0⟩ hq₂Seg₂
        (isPreconnected_image_Ico ha₂) (isPreconnected_Icc.image _ continuous_ofReal.continuousOn)
    exact IsPreconnected.union (R : ℂ) (Or.inr hRSeg₂)
      ⟨0, ⟨le_rfl, zero_lt_one⟩, circPath_zero_start⟩ h1
      (isPreconnected_image_Ico (continuous_circPath _ _ _).continuousOn)
  -- real points of the segments
  have hSegre : ∀ {x y : ℝ} {w : ℂ}, w ∈ ofReal '' Icc x y → w.re ∈ Icc x y ∧ w = (w.re : ℂ) := by
    rintro x y _ ⟨v, hv, rfl⟩; simpa using hv
  have hB₁r : ∀ w ∈ B₁, w.im = 0 → w = q₁ := fun w hw => hA₁r w (hB₁A₁ hw)
  have hB₂r : ∀ w ∈ B₂, w.im = 0 → w = q₂ := fun w hw => hA₂r w (hB₂A₂ hw)
  have hD₁r : ∀ w ∈ D₁, w.im = 0 → w = -(R : ℂ) := fun w hw => hC₁r w (hD₁C₁ hw)
  have hD₂r : ∀ w ∈ D₂, w.im = 0 → w = (R : ℂ) := fun w hw => hC₂r w (hD₂C₂ hw)
  have hreR : ∀ x : ℝ, ((x : ℂ)).re = x := fun x => ofReal_re x
  -- `S₁` misses `Ξ₂`
  have hS₁Ξ₂ : Disjoint (B₁ ∪ Seg₁ ∪ D₁) (A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂)) := by
    rw [Set.disjoint_left]
    rintro w ((hw | hw) | hw) ((hw' | hw') | hw' | hw')
    · exact hB₁z w hw (h12 ⟨hB₁A₁ hw, hw'⟩)
    · exact hB₁z w hw (h13 ⟨hB₁A₁ hw, hw'⟩)
    · have h1 := hB₁r w hw (hSegr hw')
      rw [h1] at hw'
      have := (hmemSeg.1 hw').1; linarith
    · exact absurd (hC₂n w hw') (ne_of_lt (hA₁B w (hB₁A₁ hw)))
    · have h1 := hA₂r w hw' (hSegr hw)
      rw [h1] at hw
      have := (hmemSeg.1 hw).2; linarith
    · exact absurd (hSegr hw) (ne_of_gt (hA₃H w hw'))
    · obtain ⟨h1, h2⟩ := hSegre hw
      obtain ⟨h3, -⟩ := hSegre hw'
      linarith [h1.2, h3.1]
    · have h1 := hC₂r w hw' (hSegr hw)
      rw [h1] at hw
      have := (hmemSeg.1 hw).2; linarith
    · exact absurd (hC₁n w (hD₁C₁ hw)) (ne_of_lt (hA₂B w hw'))
    · exact hD₁e w hw (hA₃e w hw' (hC₁n w (hD₁C₁ hw)))
    · have h1 := hD₁r w hw (hSegr hw')
      rw [h1] at hw'
      have := (hSegre hw').1
      simp only [neg_re, ofReal_re] at this
      linarith [this.1]
    · exact hD₁e w hw (hC₁₂ w (hD₁C₁ hw) hw')
  -- `S₂` misses `Ξ₁`
  have hS₂Ξ₁ : Disjoint (B₂ ∪ Seg₂ ∪ D₂) (A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁)) := by
    rw [Set.disjoint_left]
    rintro w ((hw | hw) | hw) ((hw' | hw') | hw' | hw')
    · exact hB₂z w hw (h12 ⟨hw', hB₂A₂ hw⟩)
    · exact hB₂z w hw (h23 ⟨hB₂A₂ hw, hw'⟩)
    · have h1 := hB₂r w hw (hSegr hw')
      rw [h1] at hw'
      have := (hmemSeg.1 hw').2; linarith
    · exact absurd (hC₁n w hw') (ne_of_lt (hA₂B w (hB₂A₂ hw)))
    · have h1 := hA₁r w hw' (hSegr hw)
      rw [h1] at hw
      have := (hmemSeg.1 hw).1; linarith
    · exact absurd (hSegr hw) (ne_of_gt (hA₃H w hw'))
    · obtain ⟨h1, -⟩ := hSegre hw
      obtain ⟨h3, -⟩ := hSegre hw'
      linarith [h1.1, h3.2]
    · have h1 := hC₁r w hw' (hSegr hw)
      rw [h1] at hw
      have := (hSegre hw).1
      simp only [neg_re, ofReal_re] at this
      linarith [this.1]
    · exact absurd (hC₂n w (hD₂C₂ hw)) (ne_of_lt (hA₁B w hw'))
    · exact hD₂e w hw (hA₃e w hw' (hC₂n w (hD₂C₂ hw)))
    · have h1 := hD₂r w hw (hSegr hw')
      rw [h1] at hw'
      have := (hmemSeg.1 hw').2; linarith
    · exact hD₂e w hw (hC₁₂ w hw' (hD₂C₂ hw))
  -- the intersections used by Janiszewski
  have hΓΞ₁eq : (A₁ ∪ A₂ ∪ Seg₀) ∩ (A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁)) = A₁ := by
    apply Subset.antisymm
    · rintro w ⟨(hw | hw) | hw, (hw' | hw') | hw' | hw'⟩
      all_goals first
        | exact hw
        | exact hw'
        | skip
      · rw [h23 ⟨hw, hw'⟩]; exact hzA₁
      · rw [hA₂r w hw (hSegr hw')] at hw'
        have := (hmemSeg.1 hw').2; linarith
      · exact absurd (hC₁n w hw') (ne_of_lt (hA₂B w hw))
      · exact absurd (hSegr hw) (ne_of_gt (hA₃H w hw'))
      · obtain ⟨h1, h1'⟩ := hSegre hw
        obtain ⟨h3, -⟩ := hSegre hw'
        have : w.re = q₁ := le_antisymm h3.2 h1.1
        rw [h1', this]; exact hq₁A₁
      · have h1 := hC₁r w hw' (hSegr hw)
        rw [h1] at hw
        have := (hSegre hw).1
        simp only [neg_re, ofReal_re] at this
        linarith [this.1]
    · intro w hw; exact ⟨Or.inl (Or.inl hw), Or.inl (Or.inl hw)⟩
  have hΓΞ₁Ξ₂eq : (A₁ ∪ A₂ ∪ Seg₀ ∪ (A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁))) ∩ (A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂)) =
      A₂ ∪ A₃ := by
    apply Subset.antisymm
    · rintro w ⟨hw, hw'⟩
      rw [hΞ₂eq] at hw'
      rcases hw' with hw' | hw'
      · rcases hw with ((hw | hw) | hw) | hw
        · exact absurd hw' (Set.disjoint_right.1 hS₂Ξ₁ (Or.inl (Or.inl hw)))
        · exact Or.inl hw
        · -- a point of `[q₁, q₂]` in `S₂` is `q₂`
          rcases hw' with (hw' | hw') | hw'
          · rw [hB₂r w hw' (hSegr hw)]; exact Or.inl hq₂A₂
          · obtain ⟨h1, h1'⟩ := hSegre hw
            obtain ⟨h3, -⟩ := hSegre hw'
            have : w.re = q₂ := le_antisymm h1.2 h3.1
            rw [h1', this]; exact Or.inl hq₂A₂
          · have h1 := hD₂r w hw' (hSegr hw)
            rw [h1] at hw
            have := (hmemSeg.1 hw).2; linarith
        · exact absurd hw' (Set.disjoint_right.1 hS₂Ξ₁ hw)
      · exact Or.inr hw'
    · rintro w (hw | hw)
      · exact ⟨Or.inl (Or.inl (Or.inr hw)), Or.inl (Or.inl hw)⟩
      · exact ⟨Or.inr (Or.inl (Or.inr hw)), Or.inl (Or.inr hw)⟩
  -- the cover of the half-disc boundary
  have hcover : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ R → w ∉ ball 0 R ∩ H →
      w ∈ A₁ ∪ A₂ ∪ Seg₀ ∪ (A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁)) ∪ (A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂)) := by
    intro w hwim hwR hwn
    rcases eq_or_lt_of_le hwR with h | h
    · rcases mem_circArcs_of_norm_eq hθ h hwim with h' | h'
      · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h')))
    · have hwH : ¬ (0 < w.im) := fun hpos => hwn ⟨mem_ball_zero_iff.2 h, hpos⟩
      have hw0 : w.im = 0 := le_antisymm (not_lt.1 hwH) hwim
      have hwr : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw0]
      have hre : |w.re| < R := by
        have : ‖w‖ = |w.re| := by rw [hwr, norm_real, Real.norm_eq_abs, ofReal_re]
        rw [← this]; exact h
      have hre' := abs_lt.1 hre
      rw [hwr]
      rcases le_total w.re q₁ with h1 | h1
      · exact Or.inl (Or.inr (Or.inr (Or.inl (hmemSeg.2 ⟨hre'.1.le, h1⟩))))
      rcases le_total w.re q₂ with h2 | h2
      · exact Or.inl (Or.inl (Or.inr (hmemSeg.2 ⟨h1, h2⟩)))
      · exact Or.inr (Or.inr (Or.inl (hmemSeg.2 ⟨h2, hre'.2.le⟩)))
  -- the set avoids `Γ \ (Ξ₁ ∪ Ξ₂)`
  have hPΓ : Disjoint P ((A₁ ∪ A₂ ∪ Seg₀) \
      ((A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁)) ∪ (A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂)))) := by
    rw [Set.disjoint_left]
    rintro w hwP ⟨(hw | hw) | hw, hwn⟩
    · exact hwn (Or.inl (Or.inl (Or.inl hw)))
    · exact hwn (Or.inr (Or.inl (Or.inl hw)))
    · obtain ⟨h1, h1'⟩ := hSegre hw
      rcases eq_or_lt_of_le h1.1 with h | h
      · exact hwn (Or.inl (Or.inr (Or.inl (by rw [h1', ← h]; exact hq₁Seg₁))))
      rcases eq_or_lt_of_le h1.2 with h' | h'
      · exact hwn (Or.inr (Or.inr (Or.inl (by rw [h1', h']; exact hq₂Seg₂))))
      exact Set.disjoint_left.1 hPI hwP ⟨w.re, ⟨h, h'⟩, h1'.symm⟩
  have hΓH : A₁ ∪ A₂ ∪ Seg₀ ⊆ Hbar := union_subset (union_subset hA₁H hA₂H) (hSegH _)
  have hΞ₁H : A₁ ∪ A₃ ∪ (Seg₁ ∪ C₁) ⊆ Hbar :=
    union_subset (union_subset hA₁H hA₃H') (union_subset (hSegH _) hC₁H)
  have hΞ₂H : A₂ ∪ A₃ ∪ (Seg₂ ∪ C₂) ⊆ Hbar :=
    union_subset (union_subset hA₂H hA₃H') (union_subset (hSegH _) hC₂H)
  exact false_of_isPreconnected_gates (x₁ := q₁) (x₂ := q₂) (R := R) hΓJ hΞ₁J hΞ₂J hΓH hΞ₁H hΞ₂H
    hΞ₁eq hΞ₂eq hS₁p hS₂p (Or.inl (Or.inl ⟨0, ⟨le_rfl, zero_lt_one⟩, ha₁0⟩))
    (Or.inl (Or.inl ⟨0, ⟨le_rfl, zero_lt_one⟩, ha₂0⟩)) hS₁Ξ₂ hS₂Ξ₁
    (by rw [hΓΞ₁eq]; exact isPreconnected_image_Icc ha₁)
    (by
      rw [hΓΞ₁Ξ₂eq]
      exact IsPreconnected.union z hzA₂ hzA₃ (isPreconnected_image_Icc ha₂)
        (isPreconnected_image_Icc ha₃))
    hcover hP hPB hPH hq₁P hq₂P hP₃ hPF hPΓ

end InteractingSLE.Sec6
