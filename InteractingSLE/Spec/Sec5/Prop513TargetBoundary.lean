/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetChart

/-! # Exact boundary data and exceptional points of the E-to-Q chart -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Sec7.StripSysField Prop513Schedule

/-- The real forward Möbius coordinate. -/
def realFwd (q y : ℝ) : ℝ := y / (y + (1 + q))

theorem realFwd_realInv {q x : ℝ} (hq : 0 < q) (hx : x ≠ 1) :
    realFwd q (realInv q x) = x := by
  have hc : 1 + q ≠ 0 := by linarith
  have hd : x - 1 ≠ 0 := sub_ne_zero.2 hx
  dsimp only [realFwd, realInv]
  rw [sub_add_cancel]
  field_simp
  ring

theorem realFwd_neg_one (q : ℝ) : realFwd q (-1) = -(1 / q) := by
  dsimp only [realFwd]
  rw [show (-1 : ℝ) + (1 + q) = q by ring]
  rw [neg_div]

theorem realFwd_lower (q t : ℝ) :
    realFwd q (Real.exp (π * t) - 1) =
      (Real.exp (π * t) - 1) / (Real.exp (π * t) + q) := by
  dsimp only [realFwd]
  congr 1
  ring

theorem realFwd_upper (q t : ℝ) :
    realFwd q (-Real.exp (π * t) - 1) =
      (Real.exp (π * t) + 1) / (Real.exp (π * t) - q) := by
  dsimp only [realFwd]
  rw [show -Real.exp (π * t) - 1 = -(Real.exp (π * t) + 1) by ring,
    show -(Real.exp (π * t) + 1) + (1 + q) = -(Real.exp (π * t) - q) by ring,
    neg_div_neg_eq]

/-- Every old exceptional point has its image in the stated Q exception set. -/
theorem realInv_notMem {q x : ℝ} (hq : 0 < q) {JL JU : Finset ℝ}
    (hx : x ∉ stripQHJumps q JL JU) : realInv q x ∉ stripHJumps JL JU := by
  have hx1 : x ≠ 1 := fun he => hx (by simp only [stripQHJumps, Finset.mem_insert]; exact Or.inr (Or.inl he))
  intro hm
  have hf := realFwd_realInv hq hx1
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hm
  apply hx
  rcases hm with he | ⟨t, ht, he⟩ | ⟨t, ht, he⟩
  · rw [he, realFwd_neg_one q] at hf
    exact Finset.mem_insert.2 (Or.inl hf.symm)
  · rw [← he, realFwd_lower] at hf
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.2 ⟨t, ht, hf⟩)))
  · rw [← he, realFwd_upper] at hf
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨t, ht, hf⟩)))

theorem realInv_add_one {q x : ℝ} (hx : x ≠ 1) :
    realInv q x + 1 = (1 + q * x) / (1 - x) := by
  dsimp only [realInv]
  field_simp
  ring

theorem neg_realInv_sub_one {q x : ℝ} (hx : x ≠ 1) :
    -realInv q x - 1 = (q * x + 1) / (x - 1) := by
  dsimp only [realInv]
  field_simp
  ring

theorem liftBoundary_realMiddle_of_lt {q x : ℝ} (hq : 0 < q) (hx : x < 1) :
    liftBoundary (realMiddle q x) = 0 := by
  have hm : 0 < realMiddle q x :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  exact ite_eq_right (not_lt.2 hm.le)

theorem liftBoundary_realMiddle_of_gt {q x : ℝ} (hq : 0 < q) (hx : 1 < x) :
    liftBoundary (realMiddle q x) = -(2 * π) := by
  have hm : realMiddle q x < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith)
  exact ite_eq_left hm

/-- The transported E heights, including the inherited argument, equal the Q
heights at every point other than the two strip ends. -/
theorem data_eq {κ q x : ℝ} (hq : 0 < q) {bL bU : ℝ → ℝ}
    (hx : x ≠ 1) (hxq : x ≠ -(1 / q)) :
    stripHData κ bL bU (realInv q x) + chiC κ * liftBoundary (realMiddle q x) =
      stripQHData κ q bL bU x := by
  rcases lt_or_gt_of_ne hxq with hleft | hright
  · have hxlt : x < 1 := by linarith [neg_one_div_neg hq]
    have hpos := stripQ_upper_left_pos hq hleft
    have hbound : ¬ -1 < realInv q x := by
      have := neg_realInv_sub_one (q := q) hx
      linarith
    rw [stripHData, ite_eq_right hbound, neg_realInv_sub_one hx,
      liftBoundary_realMiddle_of_lt hq hxlt, mul_zero, add_zero, stripQHData_of_lt hleft]
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hpos : 0 < (1 + q * x) / (1 - x) :=
        div_pos (by linarith [(neg_one_lt_mul_iff hq).1 hright]) (by linarith)
      have hbound : -1 < realInv q x := by linarith [realInv_add_one (q := q) hx]
      rw [stripHData, ite_eq_left hbound, realInv_add_one hx,
        liftBoundary_realMiddle_of_lt hq hlt, mul_zero, add_zero, stripQHData_of_mem hright hlt]
    · have hpos := stripQ_upper_right_pos hq hgt
      have hbound : ¬ -1 < realInv q x := by linarith [neg_realInv_sub_one (q := q) hx]
      rw [stripHData, ite_eq_right hbound, neg_realInv_sub_one hx,
        liftBoundary_realMiddle_of_gt hq hgt, stripQHData_of_gt hq hgt]
      ring

end InteractingSLE.Sec5.Prop513Target
