/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Dyn

/-!
# Incident heights when a first-contact side collapses

A collapsed left side exposes the original left limit at the left end of
the filled real base. The right side has the corresponding right limit.
These formulas include repeated word marks at zero.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData

/-- The nonstrict word index counts an initial segment characterized by its
positions. This also applies to words with coincident marks. -/
theorem indexLE_eq_of_iff {c : BoundaryWord} {y : ℝ} {k : ℕ} (hk : k ≤ c.1)
    (he : ∀ i < c.1, c.2.1 i ≤ y ↔ i < k) : c.indexLE y = k := by
  have hset : (Finset.range c.1).filter (fun i => c.2.1 i ≤ y) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hy⟩
      exact (he i hi).1 hy
    · intro hi
      exact ⟨hi.trans_le hk, (he i (hi.trans_le hk)).2 hi⟩
  simp only [BoundaryWord.indexLE, hset, Finset.card_range]

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- Exact left incident height, including the collapsed exposed interval. -/
theorem word_leftLim_zero (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hL hR : ℝ) :
    leftLim (d.word c₀ hL hR ω).fn 0 =
      if d.wordL ω = 0 then leftLim c₀.fn (d.baseL ω) else hL := by
  classical
  by_cases hL0 : d.wordL ω = 0
  · rw [ite_eq_left hL0, BoundaryWord.leftLim_fn, BoundaryWord.leftLim_fn]
    have hi : (d.word c₀ hL hR ω).index 0 = d.wordK c₀ ω := by
      apply BoundaryWord.index_eq_of_iff (by rw [PairData.word_fst]; omega)
      intro i hi
      by_cases hik : i < d.wordK c₀ ω
      · exact iff_of_true (hL0 ▸ hd.word_pos_lt_wordL hE hc₀ hL hR hik) hik
      · have hpos : 0 ≤ (d.word c₀ hL hR ω).2.1 i := by
          by_cases hi3 : i < d.wordK c₀ ω + 3
          · obtain rfl | rfl | rfl : i = d.wordK c₀ ω ∨ i = d.wordK c₀ ω + 1 ∨
                i = d.wordK c₀ ω + 2 := by omega
            · rw [PairData.word_pos_k, hL0]
            · rw [PairData.word_pos_k1]
            · rw [PairData.word_pos_k2]
              exact hd.wordR_nonneg hE
          · exact (hd.wordR_nonneg hE).trans
              (hd.wordR_lt_word_pos hE hc₀ hL hR (not_lt.1 hi3) hi).le
        exact iff_of_false (not_lt_of_ge hpos) hik
    rw [hi, PairData.word_ht_of_le hL hR le_rfl]
    rfl
  · rw [ite_eq_right hL0]
    have hLneg : d.wordL ω < 0 := lt_of_le_of_ne (hd.wordL_nonpos hE) hL0
    exact Sec4.leftLim_eq_of_forall hLneg fun _ hy =>
      hd.word_fn_of_mem_Ioo_left hE hc₀ hL hR hy.1 hy.2

/-- Exact right incident height, including the collapsed exposed interval. -/
theorem word_rightLim_zero (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hL hR : ℝ) :
    rightLim (d.word c₀ hL hR ω).fn 0 =
      if d.wordR ω = 0 then rightLim c₀.fn (d.baseR ω) else hR := by
  classical
  by_cases hR0 : d.wordR ω = 0
  · rw [ite_eq_left hR0, BoundaryWord.rightLim_fn, BoundaryWord.rightLim_fn]
    have hi : (d.word c₀ hL hR ω).indexLE 0 = d.wordK c₀ ω + 3 := by
      apply indexLE_eq_of_iff
        (by rw [PairData.word_fst]; omega)
      intro i hi
      by_cases hi3 : i < d.wordK c₀ ω + 3
      · have hpos : (d.word c₀ hL hR ω).2.1 i ≤ 0 := by
          by_cases hik : i < d.wordK c₀ ω
          · exact (hd.word_pos_lt_wordL hE hc₀ hL hR hik).le.trans (hd.wordL_nonpos hE)
          · obtain rfl | rfl | rfl : i = d.wordK c₀ ω ∨ i = d.wordK c₀ ω + 1 ∨
                i = d.wordK c₀ ω + 2 := by omega
            · rw [PairData.word_pos_k]
              exact hd.wordL_nonpos hE
            · rw [PairData.word_pos_k1]
            · rw [PairData.word_pos_k2, hR0]
        exact iff_of_true hpos hi3
      · have hpos : 0 < (d.word c₀ hL hR ω).2.1 i :=
          hR0 ▸ hd.wordR_lt_word_pos hE hc₀ hL hR (not_lt.1 hi3) hi
        exact iff_of_false (not_le_of_gt hpos) hi3
    rw [hi, PairData.word_ht_of_ge hL hR le_rfl]
    simp only [Nat.sub_self, zero_add]
    rfl
  · rw [ite_eq_right hR0]
    have hRpos : 0 < d.wordR ω := lt_of_le_of_ne (hd.wordR_nonneg hE) (Ne.symm hR0)
    exact Sec4.rightLim_eq_of_forall hRpos fun _ hy =>
      hd.word_fn_of_mem_Ioo_right hE hc₀ hL hR hy.1 hy.2

/-- A collapsed side puts the common contact at the corresponding real base
end. This is a consequence of the existing inverse-chart endpoint formulas. -/
theorem contact_eq_base_of_collapsed (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    (d.wordL ω = 0 → d.η₁ ω (d.s₀ ω) = (d.baseL ω : ℂ)) ∧
      (d.wordR ω = 0 → d.η₁ ω (d.s₀ ω) = (d.baseR ω : ℂ)) := by
  constructor
  · intro he
    have hi := Sec7.SideHeightBox.inv_wordL hd hE
    rw [he, Complex.ofReal_zero, Sec7.SideHeightBox.inv_zero_eq_contact hd hE] at hi
    exact hi
  · intro he
    have hi := Sec7.SideHeightBox.inv_wordR hd hE
    rw [he, Complex.ofReal_zero, Sec7.SideHeightBox.inv_zero_eq_contact hd hE] at hi
    exact hi

end InteractingSLE.Restart.FCPlumb
