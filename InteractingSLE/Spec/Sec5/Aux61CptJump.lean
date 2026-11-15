/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm
import InteractingSLE.Spec.Sec7.Aux37SideGerm

/-!
# The returned counterflow word has no jumps on the eastern side

Packet PROVE-AUX61-CAPTURE (ruling R103), the jump half of the open step. The jumps of the returned counterflow word
(`returnedCfJumps`) are `0` and the returns `−1/V` of the centred force positions `V` of the counterflow word at time
`s`. The left positions lie left of the left base image `L = −g^{−w}_s(0) − w(s) ≤ 0` and the right positions right of the
right base image `R = g_s(0⁺) − w(s) ≥ 0` (`rightImg_mono`).

* `notMem_returnedCfJumps_of_junR_lt`: if `L < 0`, no jump lies strictly right of the right junction
  `junR = −1/L`, i.e. on the whole exposed eastern side of the counterflow chart, where the window events land.
* `im_cfBdry_eq_zero_of_mem_returnedCfJumps`: without any gap hypothesis, every nonzero jump coordinate has a real
  physical point (the side lemmas `lt_rightImg_sub_of_extendFrom_mem_H`, `neg_rightImg_sub_lt_of_extendFrom_mem_H`).
  So a coordinate whose physical point is in `ℍ` is not a jump.

Deterministic; R48/R77 respected. Nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Sec7.StripSysField MartChar.RealFlow CrossCond.Word49 Aux61Cmp LawUnique

/-- The driver at a time lies left of the right image of `0⁺`. -/
theorem le_rightImg_zero {w : ℝ → ℝ} (hw : Continuous w) {s : ℝ} (hs : 0 ≤ s) : w s ≤ rightImg w 0 s :=
  le_csInf (imgSet_nonempty hw 0 hs) fun _ ⟨_, _, hy, hg⟩ => hg ▸ (hy.lt_gImg hw ⟨hs, le_rfl⟩).le

/-- Membership in the returned jumps, unfolded: `0` or the return of a centred force position. -/
theorem mem_returnedCfJumps_iff {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ℝ≥0} {y : HistorySpace 0 0} {x : ℝ} :
    x ∈ returnedCfJumps κ b J s y ↔ x = 0 ∨
      ∃ V ∈ forceJumpFinset (cfPosL κ b J (Sec4.regPath (cfStop s y)) s)
        (cfPosR κ b J (Sec4.regPath (cfStop s y)) s), -V⁻¹ = x := by
  simp only [returnedCfJumps, returnExcept, Finset.mem_insert, Finset.mem_image]

/-- The centred left force positions lie left of the left base image. -/
theorem cfPosL_le {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous (Ito.rpath w))
    {s : ℝ≥0} (i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps J) 0)) :
    cfPosL κ b J w s i ≤ -rightImg (fun r => -Ito.rpath w r) 0 s - Ito.rpath w s := by
  have h := Sec7.Aux37Side.rightImg_mono (w := fun r => -Ito.rpath w r) hw.neg
    (neg_nonneg.2 (GlueImg.flowLineXL_zero_nonpos (counterflowData κ b) (counterflowJumps J) i))
    (x := 0) (NNReal.coe_nonneg s)
  have hws : Ito.rpath w (s : ℝ) = w s := by simp [Ito.rpath]
  simp only [cfPosL, hws]
  linarith

/-- The centred right force positions lie right of the right base image, hence are nonnegative. -/
theorem rightImg_sub_le_cfPosR {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous (Ito.rpath w))
    {s : ℝ≥0} (j : Fin (flowLineNR (counterflowData κ b) (counterflowJumps J) 0)) :
    rightImg (Ito.rpath w) 0 s - Ito.rpath w s ≤ cfPosR κ b J w s j := by
  have h := Sec7.Aux37Side.rightImg_mono hw
    (GlueImg.flowLineXR_zero_nonneg (counterflowData κ b) (counterflowJumps J) j)
    (x := 0) (NNReal.coe_nonneg s)
  have hws : Ito.rpath w (s : ℝ) = w s := by simp [Ito.rpath]
  simp only [cfPosR, hws]
  linarith

theorem cfPosR_nonneg {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous (Ito.rpath w))
    {s : ℝ≥0} (j : Fin (flowLineNR (counterflowData κ b) (counterflowJumps J) 0)) :
    0 ≤ cfPosR κ b J w s j := by
  have h1 := rightImg_sub_le_cfPosR (κ := κ) (b := b) (J := J) hw (s := s) j
  have h2 := le_rightImg_zero hw (NNReal.coe_nonneg s)
  linarith

/-- **No returned jump right of the right junction** (given a strict left gap): the exposed eastern side of the
counterflow chart carries a jump-free returned word. -/
theorem notMem_returnedCfJumps_of_junR_lt {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ℝ≥0}
    {y : HistorySpace 0 0} (hw : Continuous (Ito.rpath (Sec4.regPath (cfStop s y))))
    (hgap : -rightImg (fun r => -Ito.rpath (Sec4.regPath (cfStop s y)) r) 0 s -
      Ito.rpath (Sec4.regPath (cfStop s y)) s < 0)
    {x : ℝ} (hx : junR (Ito.rpath (Sec4.regPath (cfStop s y))) s < x) :
    x ∉ returnedCfJumps κ b J s y := by
  set w := Sec4.regPath (cfStop s y)
  set L := -rightImg (fun r => -Ito.rpath w r) 0 s - Ito.rpath w s with hL
  have hjR : junR (Ito.rpath w) s = -1 / L := rfl
  have hj0 : 0 < junR (Ito.rpath w) s := by
    rw [hjR, neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hgap)
  have hx0 : 0 < x := hj0.trans hx
  rw [mem_returnedCfJumps_iff]
  rintro (h0 | ⟨V, hV, hVx⟩)
  · exact hx0.ne' h0
  · simp only [forceJumpFinset, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hV
    rcases hV with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [inv_zero, neg_zero] at hVx
      exact hx0.ne hVx
    · have hle := cfPosL_le (κ := κ) (b := b) (J := J) hw (s := s) i
      set V := cfPosL κ b J w s i
      have hVneg : V < 0 := lt_of_le_of_lt hle hgap
      have h1 : 1 / L ≤ 1 / V := one_div_le_one_div_of_neg_of_le hgap hle
      have h2 : -V⁻¹ ≤ -1 / L := by rw [neg_div, ← one_div]; linarith
      rw [hVx, ← hjR] at h2
      exact absurd hx (not_lt.2 h2)
    · have hnn := cfPosR_nonneg (κ := κ) (b := b) (J := J) hw (s := s) j
      set V := cfPosR κ b J w s j
      have h1 : -V⁻¹ ≤ 0 := neg_nonpos.2 (inv_nonneg.2 hnn)
      rw [hVx] at h1
      exact absurd hx0 (not_lt.2 h1)

/-- **A nonzero returned jump coordinate has a real physical point** (no gap hypothesis): its physical point is the
inverse counterflow map's boundary value at a force position, which the side lemmas keep off `ℍ`. -/
theorem im_cfBdry_eq_zero_of_mem_returnedCfJumps {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ℝ≥0}
    {y : HistorySpace 0 0} {γ : ℝ → ℂ}
    (hw : Continuous (Ito.rpath (Sec4.regPath (cfStop s y))))
    (hw0 : Ito.rpath (Sec4.regPath (cfStop s y)) 0 = 0)
    (hγ : IsLoewnerTrace (Ito.rpath (Sec4.regPath (cfStop s y))) γ)
    {x : ℝ} (hx0 : x ≠ 0) (hx : x ∈ returnedCfJumps κ b J s y) :
    (cfBdry (Ito.rpath (Sec4.regPath (cfStop s y))) s x).im = 0 := by
  set w := Sec4.regPath (cfStop s y)
  have hs : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
  rw [mem_returnedCfJumps_iff] at hx
  obtain ⟨V, hV, hVx⟩ := hx.resolve_left hx0
  have hneg : negInv (x : ℂ) = (V : ℂ) := by
    rw [← hVx]
    simp only [negInv, Complex.ofReal_neg, Complex.ofReal_inv, inv_neg, inv_inv, neg_neg]
  have hnotH : extendFrom H (fwdMapInv (Ito.rpath w) s) (V : ℂ) ∉ H := by
    intro hH
    simp only [forceJumpFinset, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hV
    rcases hV with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [inv_zero, neg_zero] at hVx
      exact hx0 hVx.symm
    · have h1 := neg_rightImg_sub_lt_of_extendFrom_mem_H hγ hw hw0 hs hH
      have h2 := cfPosL_le (κ := κ) (b := b) (J := J) hw (s := s) i
      linarith
    · have h1 := lt_rightImg_sub_of_extendFrom_mem_H hγ hw hw0 hs hH
      have h2 := rightImg_sub_le_cfPosR (κ := κ) (b := b) (J := J) hw (s := s) j
      linarith
  have hbar : extendFrom H (fwdMapInv (Ito.rpath w) s) (V : ℂ) ∈ Hbar := by
    have := Prop49Exit.extendFrom_mem_Hbar hγ hw hw0 hs V
    simpa only [Complex.ofReal_re] using this
  have him : (extendFrom H (fwdMapInv (Ito.rpath w) s) (V : ℂ)).im = 0 :=
    le_antisymm (not_lt.1 hnotH) hbar
  rw [cfBdry, hneg]
  generalize extendFrom H (fwdMapInv (Ito.rpath w) s) (V : ℂ) = v at him
  simp only [negInv, Complex.neg_im, Complex.inv_im, him, neg_zero, zero_div]

end InteractingSLE.Sec5.Aux61Cpt
