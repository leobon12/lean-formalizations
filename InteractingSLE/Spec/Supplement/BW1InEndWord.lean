/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeSafe
import InteractingSLE.Spec.Supplement.GB6RestartProofWord

/-!
# Proposition BW1: the relative word is GB6's conditional word; admissibility and the protected tails

Packet PROVE-BW1-INPUTS (the endpoint, its kernel half). BW1's conditional relative word
`bwRelWord κ θ c₀ r = cfWordOf κ (stopWord κ (c₀, θ, r))` is GB6's conditional word `gb6WordOfRec κ θ c₀ r` (the
returned stop word with constant `πχ` and lift coefficient `χ`; BW1, p. 614: "Use the same inversion logarithm and
compatible inverse lift as GB6"). Hence, for **every** record:

* the word is admissible in GB6's data form (`isGB6AdmData_bwRelWord`, from (BW1.2) and the ambient bounds);
* beyond the right junction `jROfRec r = −1/V̂^{0,L}` the word is at least `Λ(1 + c)` as soon as the left seed image is
  nondegenerate (`rightTail_bwRelWord`), and beyond the left junction it is at most `−Λ(1 + c)` as soon as the right
  seed image is (`leftTail_bwRelWord`) (BW1, p. 614: "An active flow-side interval has one of the terminal counterflow
  sums (BW1.2). Both are at least `c` … GB5 protects every finite incident image of the retained flow range").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.BW1In

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6

variable {κ : ℝ}

/-- **The counterflow word is GB6's returned word** `retWord (πχ) χ` (the constants of `cfWordOf` are
`cfOffset κ − 2π cfCoeff κ = πχ` and `−cfCoeff κ = χ`, since `χ(16/κ) = −χ(κ)`). -/
theorem cfWordOf_eq_retWord (hκ : 0 < κ) (c : BoundaryWord) :
    GW1Laws.cfWordOf κ c = GW2JointKernel.retWord (Real.pi * chiC κ) (chiC κ) c := by
  have h1 : Sec7.StripSysField.cfOffset κ - 2 * Real.pi * Sec7.StripSysField.cfCoeff κ = Real.pi * chiC κ := by
    unfold Sec7.StripSysField.cfOffset Sec7.StripSysField.cfCoeff
    rw [Sec4.chiC_sixteen_div hκ]
    ring
  have h2 : -Sec7.StripSysField.cfCoeff κ = chiC κ := by
    unfold Sec7.StripSysField.cfCoeff
    rw [Sec4.chiC_sixteen_div hκ, neg_neg]
  unfold GW1Laws.cfWordOf
  rw [h1, h2]

/-- **BW1's relative word is GB6's conditional word.** -/
theorem bwRelWord_eq_gb6WordOfRec (hκ : 0 < κ) (θ : ℝ) (c₀ : BoundaryWord) (r : RecData) :
    bwRelWord κ θ c₀ r = gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) r := by
  unfold bwRelWord gb6WordOfRec
  exact cfWordOf_eq_retWord hκ _

/-- **BW1's relative word is admissible in GB6's data form**, for every record (the counterflow data of an admissible
stop word, as in `BW1Life.partialSums_cfWordOf`). -/
theorem isGB6AdmData_bwRelWord (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {c₀ : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ c₀.jumps → c₀.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ c₀.jumps → -sleLambda κ < c₀.fn y + Real.pi / 2 * chiC κ) (r : RecData) :
    IsGB6AdmData κ (bwRelWord κ θ c₀ r) := by
  have hc₀w : BoundaryWord.shiftW 0 c₀ = c₀ := by
    obtain ⟨n, p, v⟩ := c₀
    simp [BoundaryWord.shiftW]
  have hg : GW1Laws.IsCfGoodWord κ (stopWord κ (BoundaryWord.shiftW 0 c₀, θ, r)) := by
    rw [hc₀w]; exact isCfGoodWord_stopWord hκ hκ4 hθ hL hR r
  obtain ⟨hc, hgL, hgR⟩ := hg
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  set c := stopWord κ (BoundaryWord.shiftW 0 c₀, θ, r) with hcdef
  set c' := GW1Laws.cfWordOf κ c with hc'
  change IsGB6AdmData κ c'
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · rw [GW1Laws.fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_pos hκ c.fn hy]
    rw [GW1Laws.jumps_cfWordOf κ hc] at hyJ
    have hx : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
    have := hgL (-y⁻¹) hx (Sec7.StripSysField.negInv_notMem_of_notMem_returnExcept hyJ)
    change -sleLambda (16 / κ) < _
    rw [hΛ]
    linarith
  · rw [GW1Laws.fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_neg hκ c.fn hy]
    rw [GW1Laws.jumps_cfWordOf κ hc] at hyJ
    have hx : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have := hgR (-y⁻¹) hx (Sec7.StripSysField.negInv_notMem_of_notMem_returnExcept hyJ)
    change _ < sleLambda (16 / κ)
    rw [hΛ]
    linarith

/-- **The right protected tail of BW1's relative word**: if the left seed image of the record is nondegenerate, then
beyond the right junction the word is at least `Λ(1 + c)` (the image of the left flow flank `−λ − θχ`). -/
theorem rightTail_bwRelWord (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ₁ : -(Real.pi / 2) ≤ θ) (c₀ : BoundaryWord)
    {r : RecData} (hL : markPosL (rdrv r) (rtime r) 0 < 0) :
    ∀ y, jROfRec r < y → y ∉ (bwRelWord κ θ c₀ r).jumps → tailLevel κ ≤ (bwRelWord κ θ c₀ r).fn y := by
  intro y hy hyJ
  rw [bwRelWord_eq_gb6WordOfRec hκ θ c₀ r] at hyJ ⊢
  set c := BoundaryWord.shiftW 0 c₀
  have hΛ := bigLambda_pos hκ
  have hjR : 0 < jROfRec r := by unfold jROfRec; rw [← inv_neg]; exact inv_pos.2 (neg_pos.2 hL)
  obtain ⟨h1, h2⟩ := negInv_mem_of_gt hL hy
  have hy0 : 0 < y := lt_trans hjR hy
  rw [gb6WordOfRec_fn_of_pos θ c r hy0 hyJ,
    stopWord_fn_flank_left c θ r h1 h2 (negInv_notMem_stopWord_jumps θ c r hyJ)]
  have hv := rightValue_eq hκ θ
  rw [chiC_sixteen_div hκ] at hv
  have hS := protLevel_le_sumR hκ hκ4 hθ₁
  unfold tailLevel
  have : bigLambda κ * (protLevel κ + 1) ≤ bigLambda κ * (1 + sumR κ θ) := by nlinarith
  linarith

/-- **The left protected tail of BW1's relative word**: if the right seed image of the record is nondegenerate, then
beyond the left junction the word is at most `−Λ(1 + c)` (the image of the right flow flank `λ − θχ`). -/
theorem leftTail_bwRelWord (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ₂ : θ ≤ Real.pi / 2) (c₀ : BoundaryWord)
    {r : RecData} (hR : 0 < markPos (rdrv r) (rtime r) 0) :
    ∀ y, y < jLOfRec r → y ∉ (bwRelWord κ θ c₀ r).jumps → (bwRelWord κ θ c₀ r).fn y ≤ -tailLevel κ := by
  intro y hy hyJ
  rw [bwRelWord_eq_gb6WordOfRec hκ θ c₀ r] at hyJ ⊢
  set c := BoundaryWord.shiftW 0 c₀
  have hΛ := bigLambda_pos hκ
  obtain ⟨h1, h2⟩ := negInv_mem_of_lt hR hy
  have hy0 : y < 0 := lt_trans hy (neg_neg_of_pos (inv_pos.2 hR))
  rw [gb6WordOfRec_fn_of_neg θ c r hy0 hyJ,
    stopWord_fn_flank_right c θ r h1 h2 (negInv_notMem_stopWord_jumps θ c r hyJ)]
  have hv := leftValue_eq hκ θ
  have hS := protLevel_le_sumL hκ hκ4 hθ₂
  unfold tailLevel
  have : bigLambda κ * (protLevel κ + 1) ≤ bigLambda κ * (1 + sumL κ θ) := by nlinarith
  linarith

end InteractingSLE.Theorem14.BW1In
