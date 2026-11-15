/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GMain
import InteractingSLE.Spec.Supplement.RLCERestart

/-!
# The outer word of a disjoint pair: exposed-side heights and the untouched datum

Packet PROVE-CONDDET-HIST. At a disjoint pair (PROVE-LEMMA76G's pathwise setting `Sec7.Lemma76G.IsSetting`) the zone
word `ZW.word` of the retained chart has the canonical heights on the exposed sides of both prefixes (G7's outer word,
`Supp7.IsRetainedWord`) and the original datum on the untouched real points (`RLC.IsUntouchedWord`). These are the
word clauses of `RLC.RetOrdMeanWordStatement` at the ordinary pairs with disjoint prefixes.

* `im_inv_eq_zero_of_mem_closure`, `im_inv_L₂`, `im_inv_R₂_L₁`, `im_inv_R₁`: the chart inverse is real at the ends of
  the two side intervals (they are limits of chart points of untouched real points);
* `pos_cases`: every position of the zone word is one of the six side points or the chart point of an untouched
  original jump;
* **`isRetainedWord_zoneWord`**, **`isUntouchedWord_zoneWord`**, `zero_lt_M₁`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Sec7.Lemma76G Supp7 Restart

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **A chart point adherent to chart points with real images has a real image** (continuity of `ψ` on `ℝ`). -/
theorem im_inv_eq_zero_of_mem_closure (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {S : Set ℝ}
    (hS : ∀ w ∈ S, (ψ w).im = 0) {Z : ℝ} (hZ : Z ∈ closure S) : (ψ Z).im = 0 := by
  have hψc : Continuous fun w : ℝ => ψ w := hs.ψc.comp_continuous continuous_ofReal ofReal_mem_Hbar
  have hcl : IsClosed {w : ℝ | (ψ w).im = 0} := isClosed_eq (Complex.continuous_im.comp hψc) continuous_const
  exact hcl.closure_subset_iff.2 hS hZ

theorem im_inv_L₂ (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) : (ψ (zoneData φ α a β b).L₂).im = 0 := by
  refine im_inv_eq_zero_of_mem_closure hs (S := Iio (zoneData φ α a β b).L₂) (fun w hw => ?_) ?_
  · rw [(hs.zone₀_of_lt hw).1]; simp
  · rw [closure_Iio]; exact mem_Iic.2 le_rfl

theorem im_inv_R₂_L₁ (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    (ψ (zoneData φ α a β b).R₂).im = 0 ∧ (ψ (zoneData φ α a β b).L₁).im = 0 := by
  have hRL := hs.R₂_lt_L₁
  have hS : ∀ w ∈ Ioo (zoneData φ α a β b).R₂ (zoneData φ α a β b).L₁, (ψ w).im = 0 := fun w hw => by
    rw [(hs.zone₁_of_mem hw.1 hw.2).1]; simp
  have hcl := closure_Ioo hRL.ne
  exact ⟨im_inv_eq_zero_of_mem_closure hs hS (hcl ▸ left_mem_Icc.2 hRL.le),
    im_inv_eq_zero_of_mem_closure hs hS (hcl ▸ right_mem_Icc.2 hRL.le)⟩

theorem im_inv_R₁ (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) : (ψ (zoneData φ α a β b).R₁).im = 0 := by
  rw [hs.inv_R₁]; simp

/-- The first tip's chart point is positive (right of the second tip). -/
theorem zero_lt_M₁ (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) : 0 < (zoneData φ α a β b).M₁ := by
  have hz := hs.zoneData_good
  have h0 : (zoneData φ α a β b).M₂ = 0 := rfl
  linarith [hz.M₂_le, hs.R₂_lt_L₁, hz.L₁_le]

/-- **The positions of the zone word**: each is one of the six side points or the chart point `T(p)` of an untouched
original jump `p`. -/
theorem pos_cases (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {g₁ g₂ g₃ g₄ : ℝ} {i : ℕ}
    (hi : i < ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).1) :
    ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = (zoneData φ α a β b).L₂ ∨
      ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = 0 ∨
      ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = (zoneData φ α a β b).R₂ ∨
      ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = (zoneData φ α a β b).L₁ ∨
      ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = (zoneData φ α a β b).M₁ ∨
      ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i = (zoneData φ α a β b).R₁ ∨
      ∃ j < c₀.1, IsUntouched α a β b (c₀.2.1 j) ∧
        (zoneData φ α a β b).T (c₀.2.1 j) = ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).2.1 i := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  rcases Nat.lt_or_ge i (z.k₁ c₀) with h1 | h1
  · have hiN : i < c₀.1 := lt_of_lt_of_le h1 (ZW.cnt_le _)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hiN, ?_, (ZW.pos_of_lt h1).symm⟩)))))
    exact hs.untouched_of_zone (Or.inl ((ZW.lt_k₁_iff hc₀ hiN).1 h1))
  rcases Nat.lt_or_ge i (z.k₁ c₀ + 3) with h3 | h3
  · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
    · exact Or.inl ZW.pos_k₁
    · exact Or.inr (Or.inl ZW.pos_k₁1)
    · exact Or.inr (Or.inr (Or.inl ZW.pos_k₁2))
  rcases Nat.lt_or_ge i (z.m c₀) with h4 | h4
  · obtain ⟨hmem, hN⟩ := ZW.mid_mem hz hc₀ h3 h4
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hN, ?_, (ZW.pos_mid h3 h4).symm⟩)))))
    exact hs.untouched_of_zone (Or.inr (Or.inl hmem))
  rcases Nat.lt_or_ge i (z.m c₀ + 3) with h5 | h5
  · obtain rfl | rfl | rfl : i = z.m c₀ ∨ i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl ZW.pos_m)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ZW.pos_m1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ZW.pos_m2)))))
  · obtain ⟨hmem, hN⟩ := ZW.right_mem hc₀ h5 hi
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hN, ?_, (ZW.pos_right h5).symm⟩)))))
    exact hs.untouched_of_zone (Or.inr (Or.inr hmem))

/-- The chart point of an untouched real point is none of the six side points. -/
theorem T_ne_sides (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {x : ℝ} (hx : IsUntouched α a β b x) :
    (zoneData φ α a β b).T x ≠ (zoneData φ α a β b).L₂ ∧ (zoneData φ α a β b).T x ≠ 0 ∧
      (zoneData φ α a β b).T x ≠ (zoneData φ α a β b).R₂ ∧ (zoneData φ α a β b).T x ≠ (zoneData φ α a β b).L₁ ∧
      (zoneData φ α a β b).T x ≠ (zoneData φ α a β b).M₁ ∧ (zoneData φ α a β b).T x ≠ (zoneData φ α a β b).R₁ := by
  have hz := hs.zoneData_good
  have hM₂ : (zoneData φ α a β b).M₂ = 0 := rfl
  have hRL := hs.R₂_lt_L₁
  have hLM := hz.L₂_le
  have hMR := hz.M₂_le
  have hLM₁ := hz.L₁_le
  have hMR₁ := hz.M₁_le
  rcases (hs.isUntouched_iff x).1 hx with h0 | h1 | h2
  · have := hz.T₀_lt x h0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> linarith
  · have e1 := hz.lt_T₁ x h1
    have e2 := hz.T₁_lt x h1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> linarith
  · have := hz.lt_T₂ x h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> linarith

/-- **G7's outer word at a disjoint pair** (`Supp7.IsRetainedWord`): the zone word has the canonical heights of the
angle-`θ₂` path on both sides of the second prefix and one of the two canonical heights of the angle-`θ₁` path on the
first prefix, and no jump at an interior point of either prefix other than the tips. -/
theorem isRetainedWord_zoneWord (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (κ θ₁ θ₂ : ℝ) :
    IsRetainedWord κ θ₁ θ₂ α a β b ψ ((zoneData φ α a β b).word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₂ * QuantumZipper.chiC κ) (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  have hM₂ : z.M₂ = 0 := rfl
  have hRL := hs.R₂_lt_L₁
  intro y hyH hyβ hyα _
  have hyH' : 0 < (ψ y).im := hyH
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyβ (by simpa using hs.ψ0)
  have hyM₁ : y ≠ z.M₁ := by
    rintro rfl
    exact hyα hs.chartPt_tip₁.2.1
  have hyL₂ : y ≠ z.L₂ := by rintro rfl; linarith [im_inv_L₂ hs]
  have hyR₂ : y ≠ z.R₂ := by rintro rfl; linarith [(im_inv_R₂_L₁ hs).1]
  have hyL₁ : y ≠ z.L₁ := by rintro rfl; linarith [(im_inv_R₂_L₁ hs).2]
  have hyR₁ : y ≠ z.R₁ := by rintro rfl; linarith [im_inv_R₁ hs]
  have hyJ : y ∉ (z.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc.jumps := by
    rw [BoundaryWord.trunc_jumps]
    intro hj
    obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hj
    rcases pos_cases hs hc₀ hi with h | h | h | h | h | h | ⟨j, -, hu, hT⟩
    · exact hyL₂ (hiy ▸ h)
    · exact hy0 (hiy ▸ h)
    · exact hyR₂ (hiy ▸ h)
    · exact hyL₁ (hiy ▸ h)
    · exact hyM₁ (hiy ▸ h)
    · exact hyR₁ (hiy ▸ h)
    · have e : ψ y = ((c₀.2.1 j : ℝ) : ℂ) := by rw [← hiy, ← hT]; exact hs.T_spec hu
      rw [e] at hyH'
      simp at hyH'
  refine ⟨hy0, hyJ, fun hβ' => ?_, fun hα' => ?_⟩
  · have h1 : z.L₂ < y := lt_of_le_of_ne (hs.L₂_le_of_mem₂ hβ') (Ne.symm hyL₂)
    have h2 : y < z.R₂ := lt_of_le_of_ne (hs.le_R₂_of_mem₂ hβ') hyR₂
    refine ⟨fun hneg => ?_, fun hpos => ?_⟩
    · rw [BoundaryWord.trunc_fn]
      exact ZW.fn_side₁ hz hc₀ h1 (hM₂ ▸ hneg)
    · rw [BoundaryWord.trunc_fn]
      exact ZW.fn_side₂ hz hc₀ (hM₂ ▸ hpos) h2
  · have h1 : z.L₁ < y := lt_of_le_of_ne (hs.L₁_le_of_mem₁ hα') (Ne.symm hyL₁)
    have h2 : y < z.R₁ := lt_of_le_of_ne (hs.le_R₁_of_mem₁ hα') hyR₁
    refine ⟨by linarith [hz.M₂_le], ?_⟩
    rcases lt_or_gt_of_ne hyM₁ with h | h
    · left
      rw [BoundaryWord.trunc_fn]
      exact ZW.fn_side₃ hz hc₀ h1 h
    · right
      rw [BoundaryWord.trunc_fn]
      exact ZW.fn_side₄ hz hc₀ h h2

/-- **The untouched datum at a disjoint pair** (`RLC.IsUntouchedWord`): at a chart real whose image is a real point off
both prefixes and off the original jumps, the zone word has no jump and carries the original datum. -/
theorem isUntouchedWord_zoneWord (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {bd : ℝ → ℝ} {J : Finset ℝ} (hc₀J : c₀.jumps = J)
    (hc₀b : ∀ y ∉ J, c₀.fn y = bd y) (g₁ g₂ g₃ g₄ : ℝ) :
    IsUntouchedWord bd J (α '' Icc 0 a ∪ β '' Icc 0 b) ψ ((zoneData φ α a β b).word c₀ g₁ g₂ g₃ g₄).trunc := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  intro y hy0 hyA hyJ
  obtain ⟨-, hx, hT⟩ := hs.untouched_cases ⟨hy0, hyA⟩
  rw [BoundaryWord.trunc_jumps, BoundaryWord.trunc_fn]
  have hfn : (z.word c₀ g₁ g₂ g₃ g₄).fn y = c₀.fn (ψ y).re := by
    have key : (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T (ψ y).re) = c₀.fn (ψ y).re := by
      rcases (hs.isUntouched_iff _).1 hx with h0 | h1 | h2
      · exact ZW.fn_zone₀ hz hc₀ h0
      · exact ZW.fn_zone₁ hz hc₀ h1
      · exact ZW.fn_zone₂ hz hc₀ h2
    rwa [hT] at key
  refine ⟨fun hj => ?_, hfn.trans (hc₀b _ hyJ)⟩
  obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hj
  have hTpos : z.T (ψ y).re = (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := hT.trans hiy.symm
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := T_ne_sides hs hx
  rcases pos_cases hs hc₀ hi with h | h | h | h | h | h | ⟨j, hjN, hu, hTj⟩
  · exact n1 (hTpos.trans h)
  · exact n2 (hTpos.trans h)
  · exact n3 (hTpos.trans h)
  · exact n4 (hTpos.trans h)
  · exact n5 (hTpos.trans h)
  · exact n6 (hTpos.trans h)
  · have e : (((c₀.2.1 j : ℝ) : ℂ)) = (((ψ y).re : ℝ) : ℂ) := by
      rw [← hs.T_spec hu, ← hs.T_spec hx]
      exact congrArg (fun w : ℝ => ψ w) (hTj.trans hTpos.symm)
    have e' : c₀.2.1 j = (ψ y).re := ofReal_injective e
    exact hyJ (hc₀J ▸ BoundaryWord.mem_jumps.2 ⟨j, hjN, e'⟩)

end RLC

end InteractingSLE
