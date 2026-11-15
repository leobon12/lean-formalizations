/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpInv
import InteractingSLE.Spec.Supplement.GW2SdzStruct
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Sec7.CounterflowCentering

/-!
# The near structure (N3), steps B and C: the junction span and the structure from the side invariant

Packet PROVE-GW2-SDE (round 15).

* **`le_markPos_sub_markPosL`**: the two junction images separate: `aR − aL ≤ markPos aR − markPosL aL` for
  `aL ≤ 0 ≤ aR` (absolute images move outward; the centring cancels). `pastFirst`, **`junction_span`**: along a
  past, the junction span after the first piece never shrinks.
* `negFar_notMem_oldLeftHeights`, `posFar_notMem_oldRightHeights` (`κ < 4`): the far heights are not old side heights.
* **`nearStructTop_of_sideInv`**, **`nearStructBot_of_sideInv`**: a word with the side invariant, its left (right)
  junction beyond `3√s`, the other junction off the tip, the root heights beyond the far junction's opposite side of the
  right form, and the two far heights, has ROOT2's upper (lower) structure at the near scale `s` (even histories).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb GW2TipSystem.RootH10 MartChar.RealFlow

/-! ### The junction span -/

/-- **The two junction images separate** (absolute images move outward, the centring cancels). -/
theorem le_markPos_sub_markPosL {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {aL aR : ℝ} (haL : aL ≤ 0) (haR : 0 ≤ aR) : aR - aL ≤ markPos w T aR - markPosL w T aL := by
  have hR : aR - w T ≤ markPos w T aR := by
    have h1 := Sec5.CrossCond.Gen.rightImg_sub_le_markPos_of_nonneg hw hw0 hT haR
    have h2 : aR ≤ rightImg w aR T := by
      have := rightImg_mono_time hw aR le_rfl hT
      rwa [rightImg_zero hw hw0 haR] at this
    linarith
  have hL : markPosL w T aL ≤ aL - w T := by
    have h1 := Sec5.CrossCond.Gen.rightImg_sub_le_markPos_of_nonneg (w := fun s => -w s) hw.neg (by simp [hw0])
      hT (neg_nonneg.2 haL)
    have h2 : -aL ≤ rightImg (fun s => -w s) (-aL) T := by
      have := rightImg_mono_time (w := fun s => -w s) hw.neg (-aL) le_rfl hT
      rwa [rightImg_zero (w := fun s => -w s) hw.neg (by simp [hw0]) (neg_nonneg.2 haL)] at this
    unfold markPosL
    linarith
  linarith

variable {S : Type v}

/-- The first record's prefix of a past. -/
def pastFirst : (n : ℕ) → GW2JDetR5.Past S (n + 1) → GW2JDetR5.Past S 1
  | 0 => fun x => x
  | n + 1 => fun x => pastFirst n x.1

theorem junctionL_nonpos : ∀ (n : ℕ) (x : GW2JDetR5.Past S n), junctionL n x ≤ 0
  | 0, _ => le_rfl
  | n + 1, x => markPosL_nonpos (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2) (junctionL_nonpos n x.1)

theorem junctionR_nonneg : ∀ (n : ℕ) (x : GW2JDetR5.Past S n), 0 ≤ junctionR n x
  | 0, _ => le_rfl
  | n + 1, x => markPos_nonneg (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2) (junctionR_nonneg n x.1)

/-- **The junction span after the first piece never shrinks.** -/
theorem junction_span : ∀ (n : ℕ) (x : GW2JDetR5.Past S (n + 1)),
    junctionR 1 (pastFirst n x) - junctionL 1 (pastFirst n x) ≤ junctionR (n + 1) x - junctionL (n + 1) x
  | 0, _ => le_rfl
  | n + 1, x => (junction_span n x.1).trans (le_markPos_sub_markPosL (continuous_rdrv x.2) (rdrv_zero x.2)
      (rtime_nonneg x.2) (junctionL_nonpos (n + 1) x.1) (junctionR_nonneg (n + 1) x.1))

/-! ### The far heights are not old side heights -/

theorem sleLambda_sixteen_div_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : sleLambda (16 / κ) < sleLambda κ := by
  unfold sleLambda
  have h16 : κ < 16 / κ := by rw [lt_div_iff₀ hκ]; nlinarith
  exact div_lt_div_of_pos_left Real.pi_pos (Real.sqrt_pos.2 hκ) (Real.sqrt_lt_sqrt hκ.le h16)

theorem negFar_notMem_oldLeftHeights {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    -sleLambda (16 / κ) + Real.pi * chiC κ ∉ oldLeftHeights κ := by
  rintro ⟨α, ⟨hα1, -⟩, h⟩
  have hχ : 0 ≤ chiC κ := by
    have := Sec4.pi_mul_chiC_nonneg hκ hκ4.le
    exact nonneg_of_mul_nonneg_right (by linarith) Real.pi_pos
  have h1 : -(Real.pi / 2) * chiC κ ≤ α * chiC κ := mul_le_mul_of_nonneg_right hα1 hχ
  have hpc := Sec4.pi_mul_chiC_nonneg hκ hκ4.le
  have hlt := sleLambda_sixteen_div_lt hκ hκ4
  simp only at h
  nlinarith

theorem posFar_notMem_oldRightHeights {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    sleLambda (16 / κ) - Real.pi * chiC κ ∉ oldRightHeights κ := by
  rintro ⟨α, ⟨-, hα2⟩, h⟩
  have hχ : 0 ≤ chiC κ := by
    have := Sec4.pi_mul_chiC_nonneg hκ hκ4.le
    exact nonneg_of_mul_nonneg_right (by linarith) Real.pi_pos
  have h1 : α * chiC κ ≤ Real.pi / 2 * chiC κ := mul_le_mul_of_nonneg_right hα2 hχ
  have hpc := Sec4.pi_mul_chiC_nonneg hκ hκ4.le
  have hlt := sleLambda_sixteen_div_lt hκ hκ4
  simp only at h
  nlinarith

/-! ### The structure from the side invariant -/

/-- A point off the jumps has a value-preserving neighbour on each side, off the jumps. -/
theorem exists_near_right (c : BoundaryWord) {y : ℝ} (hy : y ∉ c.jumps) :
    ∃ z, y < z ∧ z ∉ c.jumps ∧ c.fn z = c.fn y := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (c.isPiecewiseConstantBoundaryData y hy)
  obtain ⟨z, hz1, hz2, hzJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (show y < y + ε by linarith)
  refine ⟨z, hz1, hzJ, hball ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem exists_near_left (c : BoundaryWord) {y : ℝ} (hy : y ∉ c.jumps) :
    ∃ z, z < y ∧ z ∉ c.jumps ∧ c.fn z = c.fn y := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (c.isPiecewiseConstantBoundaryData y hy)
  obtain ⟨z, hz1, hz2, hzJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (show y - ε < y by linarith)
  refine ⟨z, hz2, hzJ, hball ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

section Struct

variable {κ : ℝ} {s : ℝ≥0} {c : BoundaryWord} {aL aR : ℝ} {HL HR : Set ℝ}

/-- **The upper structure from the side invariant** (even histories). -/
theorem nearStructTop_of_sideInv (hκ : 0 < κ) (hκ4 : κ < 4) (hs : s ≠ 0) (h : SideInv κ c aL aR HL HR)
    (haL : aL ≤ -(3 * Real.sqrt s)) (haR : 0 < aR)
    (hHR : ∀ x ∈ HR, x ∈ oldRightHeights κ ∨ ∃ S : ℝ, -2 < S ∧ x = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : ∀ y, y < flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) → y ∉ c.jumps →
      c.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) < y → y ∉ c.jumps →
      c.fn y = sleLambda (16 / κ) - Real.pi * chiC κ) :
    GW2Sdy.NearStructTop κ s false c := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 (by exact_mod_cast pos_iff_ne_zero.2 hs)
  refine GW2Sdz.nearStructTop_false_of hs (fun y hy hyJ => h.oldL y (haL.trans_lt hy.1) hy.2 hyJ)
    (fun y hy hyJ => ?_) ?_ ?_ hfarL hfarR
  · rcases lt_trichotomy y aR with hya | rfl | hya
    · exact Or.inl (h.oldR y hy hya hyJ)
    · obtain ⟨z, hz, hzJ, hzv⟩ := exists_near_right c hyJ
      rw [← hzv]
      rcases hHR _ (h.rootR z hz hzJ) with h1 | ⟨S, hS, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨S, hS, h2⟩
    · rcases hHR _ (h.rootR y hya hyJ) with h1 | ⟨S, hS, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨S, hS, h2⟩
  · by_contra hcon
    have hm0 : flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) ≤ 0 := GW3Word.flowLineXL_nonpos _ _ _
    obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (not_le.1 hcon)
    have hold := h.oldL y (haL.trans_lt hy1) (hy2.trans_le hm0) hyJ
    rw [hfarL y hy2 hyJ] at hold
    exact negFar_notMem_oldLeftHeights hκ hκ4 hold
  · by_contra hcon
    have hm0 : flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) ≤ 0 := not_lt.1 hcon
    obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps haR
    have hold := h.oldR y hy1 hy2 hyJ
    rw [hfarR y (hm0.trans_lt hy1) hyJ] at hold
    exact posFar_notMem_oldRightHeights hκ hκ4 hold

/-- **The lower structure from the side invariant** (even histories). -/
theorem nearStructBot_of_sideInv (hκ : 0 < κ) (hκ4 : κ < 4) (hs : s ≠ 0) (h : SideInv κ c aL aR HL HR)
    (haR : 3 * Real.sqrt s ≤ aR) (haL : aL < 0)
    (hHL : ∀ x ∈ HL, x ∈ oldLeftHeights κ ∨ ∃ S : ℝ, -2 < S ∧ x = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hfarL : ∀ y, y < flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) → y ∉ c.jumps →
      c.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) < y → y ∉ c.jumps →
      c.fn y = sleLambda (16 / κ) - Real.pi * chiC κ) :
    GW2Sdy.NearStructBot κ s false c := by
  refine GW2Sdz.nearStructBot_false_of hs (fun y hy hyJ => ?_)
    (fun y hy hyJ => h.oldR y hy.1 (hy.2.trans_le haR) hyJ) ?_ ?_ hfarL hfarR
  · rcases lt_trichotomy y aL with hya | rfl | hya
    · rcases hHL _ (h.rootL y hya hyJ) with h1 | ⟨S, hS, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨S, hS, h2⟩
    · obtain ⟨z, hz, hzJ, hzv⟩ := exists_near_left c hyJ
      rw [← hzv]
      rcases hHL _ (h.rootL z hz hzJ) with h1 | ⟨S, hS, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨S, hS, h2⟩
    · exact Or.inl (h.oldL y hya hy hyJ)
  · by_contra hcon
    have hm0 : 0 ≤ flowLineXL c.fn c.jumps 0 (GW2TipStage.lastL c.fn c.jumps) := not_lt.1 hcon
    obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps haL
    have hold := h.oldL y hy1 hy2 hyJ
    rw [hfarL y (hy2.trans_le hm0) hyJ] at hold
    exact negFar_notMem_oldLeftHeights hκ hκ4 hold
  · by_contra hcon
    have hm0 : 0 ≤ flowLineXR c.fn c.jumps 0 (GW2TipStage.lastR c.fn c.jumps) := GW3Word.flowLineXR_nonneg _ _ _
    obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (not_le.1 hcon)
    have hold := h.oldR y (hm0.trans_lt hy1) (hy2.trans_le haR) hyJ
    rw [hfarR y hy1 hyJ] at hold
    exact posFar_notMem_oldRightHeights hκ hκ4 hold

end Struct

end InteractingSLE.Theorem14.GW2Sdp
