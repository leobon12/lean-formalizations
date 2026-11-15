/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH10Prefix
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.CS3

/-!
# Root-word margins with bad far attracting groups

Continuation of PROVE-T14-GW2ROOT2. Old angle-side heights give the GB7
margin. On the opposite original side, CS3 gives strict admissibility
under only `S > -2`. These boundary profiles imply the required strict
prefix sums of the actual flow-line word, with no condition on far
attracting heights. Identifying the retained boundary with these profiles
is a separate geometric obligation.
-/

set_option autoImplicit false

noncomputable section

open Set Finset

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH10

open QuantumZipper

/-- Boundary heights on the left of an earlier angle-side segment. -/
def oldLeftHeights (κ : ℝ) : Set ℝ :=
  (fun α => -sleLambda κ - α * chiC κ) ''
    Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- Boundary heights on the right of an earlier angle-side segment. -/
def oldRightHeights (κ : ℝ) : Set ℝ :=
  (fun α => sleLambda κ - α * chiC κ) ''
    Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- Old left angle sides have the non-boundary-intersection lower bound
at every current angle in the permitted closed interval. -/
theorem oldLeft_weight_lower {κ θ h : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hh : h ∈ oldLeftHeights κ) :
    κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (h + θ * chiC κ) := by
  obtain ⟨α, hα, rfl⟩ := hh
  rw [Sec4.le_cumWeightLeft_iff hκ]
  have hd : θ - α ≤ Real.pi := by linarith only [hθ.2, hα.1]
  have hm := mul_le_mul_of_nonneg_right hd (Sec4.chiC_pos hκ hκ4).le
  linarith only [hm]

/-- The reflected old right angle-side lower bound. -/
theorem oldRight_weight_lower {κ θ h : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hh : h ∈ oldRightHeights κ) :
    κ / 2 - 2 ≤ Sec4.cumWeightRight κ (h + θ * chiC κ) := by
  obtain ⟨α, hα, rfl⟩ := hh
  rw [Sec4.le_cumWeightRight_iff hκ]
  have hd : α - θ ≤ Real.pi := by linarith only [hα.2, hθ.1]
  have hm := mul_le_mul_of_nonneg_right hd (Sec4.chiC_pos hκ hκ4).le
  linarith only [hm]

/-- At the upper extreme, all left labels inside `(-3,0]` and all right
labels have strict cumulative sums. Far left heights are unrestricted. -/
theorem strict_prefixes_top {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hOldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ J → b y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ J → b y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ) :
    (∀ i : Fin (flowLineNL b J 0), -3 < flowLineXL b J 0 i →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i),
        flowLineRhoL κ b J 0 (Real.pi / 2) j) ∧
    ∀ i : Fin (flowLineNR b J 0),
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i),
        flowLineRhoR κ b J 0 (Real.pi / 2) j := by
  have hθ : Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith only [Real.pi_pos], le_rfl⟩
  constructor
  · intro i hi
    rw [GW3Word.filter_le_eq_filter_le_flowLineXL]
    have hxi := GW3Word.flowLineXL_nonpos b J i
    obtain ⟨y, hy1, hy2, hyJ, heq⟩ :=
      exists_left_prefix_height hκ hb (Real.pi / 2) hi hxi
    rw [heq]
    have hlo := oldLeft_weight_lower hκ hκ4 hθ
      (hOldL y ⟨hy1, hy2.trans_le hxi⟩ hyJ)
    linarith only [hlo, hκ]
  · intro i
    rw [GW3Word.filter_le_eq_filter_flowLineXR_le]
    have hxi := GW3Word.flowLineXR_nonneg b J i
    obtain ⟨y, hy1, _, hyJ, heq⟩ := exists_right_prefix_height hκ hb
      (Real.pi / 2) hxi (lt_add_one (flowLineXR b J 0 i))
    rw [heq]
    rcases hR y (hxi.trans_lt hy1) hyJ with hold | ⟨S, hS, hval⟩
    · have hlo := oldRight_weight_lower hκ hκ4 hθ hold
      linarith only [hlo, hκ]
    · rw [hval]
      exact CS3.cs3_rR_half_pi_gt hκ hS

/-- At the lower extreme, all left labels and right labels inside `[0,3)`
are admissible. Far right heights are unrestricted. -/
theorem strict_prefixes_bottom {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ y, y < 0 → y ∉ J → b y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 3, y ∉ J → b y ∈ oldRightHeights κ) :
    (∀ i : Fin (flowLineNL b J 0),
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i),
        flowLineRhoL κ b J 0 (-(Real.pi / 2)) j) ∧
    ∀ i : Fin (flowLineNR b J 0), flowLineXR b J 0 i < 3 →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i),
        flowLineRhoR κ b J 0 (-(Real.pi / 2)) j := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_rfl, by linarith only [Real.pi_pos]⟩
  constructor
  · intro i
    rw [GW3Word.filter_le_eq_filter_le_flowLineXL]
    have hxi := GW3Word.flowLineXL_nonpos b J i
    obtain ⟨y, _, hy2, hyJ, heq⟩ := exists_left_prefix_height hκ hb
      (-(Real.pi / 2)) (sub_one_lt (flowLineXL b J 0 i)) hxi
    rw [heq]
    rcases hL y (hy2.trans_le hxi) hyJ with hold | ⟨S, hS, hval⟩
    · have hlo := oldLeft_weight_lower hκ hκ4 hθ hold
      linarith only [hlo, hκ]
    · rw [hval]
      exact CS3.cs3_rL_neg_half_pi_gt hκ hS
  · intro i hi
    rw [GW3Word.filter_le_eq_filter_flowLineXR_le]
    have hxi := GW3Word.flowLineXR_nonneg b J i
    obtain ⟨y, hy1, hy2, hyJ, heq⟩ :=
      exists_right_prefix_height hκ hb (-(Real.pi / 2)) hxi hi
    rw [heq]
    have hlo := oldRight_weight_lower hκ hκ4 hθ
      (hOldR y ⟨hxi.trans_lt hy1, hy2⟩ hyJ)
    linarith only [hlo, hκ]

end InteractingSLE.Theorem14.GW2TipSystem.RootH10
