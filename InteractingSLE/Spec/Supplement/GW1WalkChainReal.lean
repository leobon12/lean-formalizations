/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChain

/-! # GW1: parametrizations of finite real connectors and terminal real rays -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkChain

open GW1X GW1Bookkeep Exist.StagedLaw

/-- The oriented real segment from `x` to `y`. -/
def realArc (x y : ℝ) (t : ℝ≥0) : ℂ := AffineMap.lineMap x y (t : ℝ)

theorem realArc_zero (x y : ℝ) : realArc x y 0 = (x : ℂ) := by
  simp only [realArc, NNReal.coe_zero, AffineMap.lineMap_apply_zero]

theorem realArc_one (x y : ℝ) : realArc x y 1 = (y : ℂ) := by
  simp only [realArc, NNReal.coe_one, AffineMap.lineMap_apply_one]

theorem isArc_realArc {x y : ℝ} (hxy : x ≠ y) : IsArc (realArc x y) := by
  refine ⟨by unfold realArc; fun_prop, ?_⟩
  intro s _ t _ heq
  exact NNReal.coe_injective
    ((AffineMap.lineMap_injective ℝ hxy) (Complex.ofReal_injective heq))

theorem realArc_upper (x y : ℝ) (t : ℝ≥0) : 0 ≤ (realArc x y t).im := by
  simp only [realArc, Complex.ofReal_im, le_refl]

theorem image_realArc (x y : ℝ) :
    realArc x y '' Iic 1 = ((↑) : ℝ → ℂ) '' Icc (min x y) (max x y) := by
  have ht : ((↑) : ℝ≥0 → ℝ) '' Iic 1 = Icc (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, by exact_mod_cast (mem_Iic.1 hs)⟩
    · intro hs
      exact ⟨⟨t, hs.1⟩, mem_Iic.2 (by exact_mod_cast hs.2), rfl⟩
  calc
    _ = ((↑) : ℝ → ℂ) '' (AffineMap.lineMap x y ''
        (((↑) : ℝ≥0 → ℝ) '' Iic 1)) := by rw [image_image, image_image]; rfl
    _ = _ := by rw [ht, ← segment_eq_image_lineMap, segment_eq_Icc']

/-- A real ray with its direction retained. -/
def realRay (right : Bool) (q : ℝ) (t : ℝ≥0) : ℂ :=
  if right then ((q + (t : ℝ) : ℝ) : ℂ) else ((q - (t : ℝ) : ℝ) : ℂ)

theorem realRay_zero (right : Bool) (q : ℝ) : realRay right q 0 = (q : ℂ) := by
  cases right <;>
    simp only [realRay, Bool.false_eq_true, ↓reduceIte, NNReal.coe_zero, sub_zero, add_zero]

theorem isProperCurve_realRay (right : Bool) (q : ℝ) : Supp9B.IsProperCurve (realRay right q) := by
  refine ⟨by
    cases right <;> unfold realRay <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop,
    ?_, ?_, ?_⟩
  · intro s t heq
    cases right <;> simp only [realRay, Bool.false_eq_true, ↓reduceIte] at heq
    · exact NNReal.coe_injective (sub_right_injective (Complex.ofReal_injective heq))
    · exact NNReal.coe_injective (add_left_cancel (Complex.ofReal_injective heq))
  · intro t
    cases right <;> simp only [realRay, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_im, le_refl]
  · have hlin : Tendsto (fun t : ℝ≥0 => (t : ℝ) + (-|q|)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (NNReal.tendsto_coe_atTop.2 tendsto_id)
    apply tendsto_atTop_mono _ hlin
    intro t
    cases right <;>
      simp only [realRay, Bool.false_eq_true, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    · linarith only [neg_le_abs (q - (t : ℝ)), le_abs_self q]
    · linarith only [le_abs_self (q + (t : ℝ)), neg_le_abs q]

theorem range_realRay (right : Bool) (q : ℝ) :
    range (realRay right q) = ((↑) : ℝ → ℂ) '' (if right then Ici q else Iic q) := by
  ext z
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · constructor
    · rintro ⟨t, rfl⟩
      exact ⟨q - (t : ℝ), mem_Iic.2 (sub_le_self _ t.2), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨q - x, sub_nonneg.2 (mem_Iic.1 hx)⟩, ?_⟩
      change ((q - (q - x) : ℝ) : ℂ) = (x : ℂ)
      rw [sub_sub_cancel]
  · constructor
    · rintro ⟨t, rfl⟩
      exact ⟨q + (t : ℝ), mem_Ici.2 (le_add_of_nonneg_right t.2), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x - q, sub_nonneg.2 (mem_Ici.1 hx)⟩, ?_⟩
      change ((q + (x - q) : ℝ) : ℂ) = (x : ℂ)
      congr 1
      ring

/-- Appending a finite connector appends precisely its physical real image. -/
theorem statePhysicalSet_moveAlong (root : ℝ) (s : ExplState) (right : Bool) (x : ℝ) (mark : Bool) :
    statePhysicalSet root (ExplState.moveAlong s right x mark) =
      statePhysicalSet root s ∪ ((↑) : ℝ → ℂ) ''
        (if right then Icc (stPt s) x else Icc x (stPt s)) := by
  cases s
  ext z
  simp only [statePhysicalSet, ExplState.moveAlong, List.mem_append, List.mem_singleton,
    mem_union, mem_iUnion, exists_prop]
  aesop

/-- Appending a terminal connector appends precisely its physical real ray. -/
theorem statePhysicalSet_moveToEnd (root : ℝ) (s : ExplState) (right : Bool) :
    statePhysicalSet root (ExplState.moveToEnd s right) =
      statePhysicalSet root s ∪ range (realRay right (stPt s)) := by
  rw [range_realRay]
  cases s
  ext z
  simp only [statePhysicalSet, ExplState.moveToEnd, List.mem_append, List.mem_singleton,
    mem_union, mem_iUnion, exists_prop]
  aesop

end InteractingSLE.Theorem14.GW1WalkChain
