/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyWord

/-!
# ROOT2's structure of the dilated base word, read on the base word (input (N3) of the near words)

Packet PROVE-GW2-SDE (round 12). Input (N3) of `GW2Sdy.frameNNearWord_withNear` asks ROOT2's upper or lower structure
(`NearStructTop`/`NearStructBot`) of the history's DILATED base word `nearDilWord s flip c`. Once STAGEMEAN's word map
gives the base word `c`, the structure is checked on `c` itself, at distance `3√s` from the tip. This file reduces it:

* `mem_jumps_dilW_iff`, `fn_dilW_apply`, **`flowLineXL_dilW_lastL`**, **`flowLineXR_dilW_lastR`** (the dilated word's
  outermost labels are the dilated outermost labels);
* **`nearStructTop_false_of`**, **`nearStructBot_false_of`** (even histories): the structure of `dilW (√s)⁻¹ c` from
  that of `c` with `3` replaced by `3√s`;
* `nearDilWord_true`, **`nearStructTop_true_of`**, **`nearStructBot_true_of`** (odd histories): the same for the sorted
  mirror word `sreflWord c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdz

open Restart GW2Sdy GW2TipSystem.RootH10

section Dil

variable {a : ℝ}

theorem mem_jumps_dilW_iff (ha : 0 < a) (c : BoundaryWord) (y : ℝ) : y ∈ (dilW a c).jumps ↔ y / a ∈ c.jumps := by
  rw [jumps_dilW, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_div_cancel_left₀ _ ha.ne']
  · intro h
    exact ⟨y / a, h, mul_div_cancel₀ _ ha.ne'⟩

theorem fn_dilW_apply (ha : 0 < a) (c : BoundaryWord) (y : ℝ) : (dilW a c).fn y = c.fn (y / a) := by
  rw [fn_dilW ha]

/-- The flow-line positions of the dilated word, with the casts of `isFlowType_of_dilW`. -/
theorem exists_flowLine_dilW (ha : 0 < a) (c : BoundaryWord) :
    ∃ (eL : flowLineNL c.fn c.jumps 0 = flowLineNL (dilW a c).fn (dilW a c).jumps 0)
      (eR : flowLineNR c.fn c.jumps 0 = flowLineNR (dilW a c).fn (dilW a c).jumps 0),
      (fun i => a⁻¹ * flowLineXL (dilW a c).fn (dilW a c).jumps 0 (Fin.cast eL i)) = flowLineXL c.fn c.jumps 0 ∧
      (fun j => a⁻¹ * flowLineXR (dilW a c).fn (dilW a c).jumps 0 (Fin.cast eR j)) = flowLineXR c.fn c.jumps 0 := by
  have htriv : FCDet.IsFlowType 1 0 (dilW a c) (flowLineXL (dilW a c).fn (dilW a c).jumps 0)
      (flowLineXR (dilW a c).fn (dilW a c).jumps 0) (flowLineRhoL 1 (dilW a c).fn (dilW a c).jumps 0 0)
      (flowLineRhoR 1 (dilW a c).fn (dilW a c).jumps 0 0) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eL, eR, hxL, hxR, -, -⟩ := isFlowType_of_dilW ha htriv
  exact ⟨eL, eR, hxL, hxR⟩

/-- **The outermost left label of the dilated word is the dilated outermost left label.** -/
theorem flowLineXL_dilW_lastL (ha : 0 < a) (c : BoundaryWord) :
    flowLineXL (dilW a c).fn (dilW a c).jumps 0 (GW2TipStage.lastL (dilW a c).fn (dilW a c).jumps) =
      a * flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) := by
  obtain ⟨eL, -, hxL, -⟩ := exists_flowLine_dilW ha c
  have h := congrFun hxL (GW2TipStage.lastL c.fn c.jumps)
  have hc : Fin.cast eL (GW2TipStage.lastL c.fn c.jumps) = GW2TipStage.lastL (dilW a c).fn (dilW a c).jumps :=
    Fin.ext (by simp only [Fin.val_cast, GW2TipStage.lastL, eL])
  simp only [hc] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- **The outermost right label of the dilated word is the dilated outermost right label.** -/
theorem flowLineXR_dilW_lastR (ha : 0 < a) (c : BoundaryWord) :
    flowLineXR (dilW a c).fn (dilW a c).jumps 0 (GW2TipStage.lastR (dilW a c).fn (dilW a c).jumps) =
      a * flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) := by
  obtain ⟨-, eR, -, hxR⟩ := exists_flowLine_dilW ha c
  have h := congrFun hxR (GW2TipStage.lastR c.fn c.jumps)
  have hc : Fin.cast eR (GW2TipStage.lastR c.fn c.jumps) = GW2TipStage.lastR (dilW a c).fn (dilW a c).jumps :=
    Fin.ext (by simp only [Fin.val_cast, GW2TipStage.lastR, eR])
  simp only [hc] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

end Dil

section Struct

variable {κ : ℝ} {s : ℝ≥0}

theorem sqrt_pos_of_ne (hs : s ≠ 0) : 0 < Real.sqrt s := Real.sqrt_pos.2 (by positivity)

theorem div_inv_sqrt (s : ℝ≥0) (y : ℝ) : y / (Real.sqrt s)⁻¹ = y * Real.sqrt s := by
  rw [div_inv_eq_mul]

/-- **The upper structure on even histories from the base word** (`3` becomes `3√s`). -/
theorem nearStructTop_false_of (hs : s ≠ 0) {c : BoundaryWord}
    (hOldL : ∀ y ∈ Set.Ioo (-(3 * Real.sqrt s)) 0, y ∉ c.jumps → c.fn y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ c.jumps → c.fn y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ c.fn y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hxm : flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) ≤ -(3 * Real.sqrt s))
    (hxp : 0 < flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps))
    (hfarL : ∀ y, y < flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) → y ∉ c.jumps →
      c.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) < y → y ∉ c.jumps →
      c.fn y = sleLambda (16 / κ) - Real.pi * chiC κ) :
    NearStructTop κ s false c := by
  have hq := sqrt_pos_of_ne hs
  have ha : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 hq
  change NearStructTop κ s false c
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_, ?_, ?_, fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · change (dilW (Real.sqrt s)⁻¹ c).fn y ∈ _
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    exact hOldL _ ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩ hyJ
  · change (dilW (Real.sqrt s)⁻¹ c).fn y ∈ _ ∨ ∃ S : ℝ, -2 < S ∧ (dilW (Real.sqrt s)⁻¹ c).fn y = _
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    exact hR _ (mul_pos hy hq) hyJ
  · change flowLineXL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) ≤ -3
    rw [flowLineXL_dilW_lastL ha]
    have : (Real.sqrt s)⁻¹ * (-(3 * Real.sqrt s)) = -3 := by field_simp
    calc (Real.sqrt s)⁻¹ * flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps)
        ≤ (Real.sqrt s)⁻¹ * (-(3 * Real.sqrt s)) := mul_le_mul_of_nonneg_left hxm ha.le
      _ = -3 := this
  · change 0 < flowLineXR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps)
    rw [flowLineXR_dilW_lastR ha]
    exact mul_pos ha hxp
  · change (dilW (Real.sqrt s)⁻¹ c).fn y = _
    change y < flowLineXL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) at hy
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [flowLineXL_dilW_lastL ha] at hy
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    refine hfarL _ ?_ hyJ
    have := mul_lt_mul_of_pos_right hy hq
    rwa [mul_comm (Real.sqrt s)⁻¹, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] at this
  · change (dilW (Real.sqrt s)⁻¹ c).fn y = _
    change flowLineXR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) < y at hy
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [flowLineXR_dilW_lastR ha] at hy
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    refine hfarR _ ?_ hyJ
    have := mul_lt_mul_of_pos_right hy hq
    rwa [mul_comm (Real.sqrt s)⁻¹, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] at this

/-- **The lower structure on even histories from the base word** (`3` becomes `3√s`). -/
theorem nearStructBot_false_of (hs : s ≠ 0) {c : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ c.fn y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 (3 * Real.sqrt s), y ∉ c.jumps → c.fn y ∈ oldRightHeights κ)
    (hxm : flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) < 0)
    (hxp : 3 * Real.sqrt s ≤ flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps))
    (hfarL : ∀ y, y < flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) → y ∉ c.jumps →
      c.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) < y → y ∉ c.jumps →
      c.fn y = sleLambda (16 / κ) - Real.pi * chiC κ) :
    NearStructBot κ s false c := by
  have hq := sqrt_pos_of_ne hs
  have ha : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 hq
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_, ?_, ?_, fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · change (dilW (Real.sqrt s)⁻¹ c).fn y ∈ _ ∨ ∃ S : ℝ, -2 < S ∧ (dilW (Real.sqrt s)⁻¹ c).fn y = _
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    exact hL _ (mul_neg_of_neg_of_pos hy hq) hyJ
  · change (dilW (Real.sqrt s)⁻¹ c).fn y ∈ _
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    exact hOldR _ ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩ hyJ
  · change flowLineXL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) < 0
    rw [flowLineXL_dilW_lastL ha]
    exact mul_neg_of_pos_of_neg ha hxm
  · change 3 ≤ flowLineXR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps)
    rw [flowLineXR_dilW_lastR ha]
    have : (Real.sqrt s)⁻¹ * (3 * Real.sqrt s) = 3 := by field_simp
    calc (3 : ℝ) = (Real.sqrt s)⁻¹ * (3 * Real.sqrt s) := this.symm
      _ ≤ (Real.sqrt s)⁻¹ * flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) :=
        mul_le_mul_of_nonneg_left hxp ha.le
  · change (dilW (Real.sqrt s)⁻¹ c).fn y = _
    change y < flowLineXL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastL (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) at hy
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [flowLineXL_dilW_lastL ha] at hy
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    refine hfarL _ ?_ hyJ
    have := mul_lt_mul_of_pos_right hy hq
    rwa [mul_comm (Real.sqrt s)⁻¹, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] at this
  · change (dilW (Real.sqrt s)⁻¹ c).fn y = _
    change flowLineXR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps 0
      (GW2TipStage.lastR (dilW (Real.sqrt s)⁻¹ c).fn (dilW (Real.sqrt s)⁻¹ c).jumps) < y at hy
    change y ∉ (dilW (Real.sqrt s)⁻¹ c).jumps at hyJ
    rw [flowLineXR_dilW_lastR ha] at hy
    rw [fn_dilW_apply ha, div_inv_sqrt s]
    rw [mem_jumps_dilW_iff ha, div_inv_sqrt s] at hyJ
    refine hfarR _ ?_ hyJ
    have := mul_lt_mul_of_pos_right hy hq
    rwa [mul_comm (Real.sqrt s)⁻¹, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] at this

/-- On odd histories the dilated word is that of the sorted mirror word on an even history. -/
theorem nearDilWord_true (s : ℝ≥0) (c : BoundaryWord) :
    nearDilWord s true c = nearDilWord s false (FCPlumb.FCKerD.sreflWord c) := rfl

/-- **The upper structure on odd histories from the sorted mirror word.** -/
theorem nearStructTop_true_of {c : BoundaryWord} (h : NearStructTop κ s false (FCPlumb.FCKerD.sreflWord c)) :
    NearStructTop κ s true c :=
  ⟨h.oldL, h.right, h.xm, h.xp, h.farL, h.farR⟩

/-- **The lower structure on odd histories from the sorted mirror word.** -/
theorem nearStructBot_true_of {c : BoundaryWord} (h : NearStructBot κ s false (FCPlumb.FCKerD.sreflWord c)) :
    NearStructBot κ s true c :=
  ⟨h.left, h.oldR, h.xm, h.xp, h.farL, h.farR⟩

end Struct

end InteractingSLE.Theorem14.GW2Sdz
