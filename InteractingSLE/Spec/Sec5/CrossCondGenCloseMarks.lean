/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenCloseAdapt
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalFlow
import InteractingSLE.Spec.Sec5.CrossRestartKernelQData

/-!
# Record positions of every image mark, including swallowed marks

PROVE-CROSSCOND-GEN. Extend the staged law's seed identity to every original
boundary mark. Transport of finite boundary-data agreement then applies to the
actual killed geometric word, without an interior-trace or strict-gap premise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (fwdMap)
open scoped NNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Exist.StagedLaw MartChar.RealFlow Sec7.StripSideHeightProb WangWu.ImgWord

/-- The rational record construction dominates the geometric image of any
nonnegative initial mark, including after its first collision. -/
theorem rightImg_sub_le_markPos_of_nonneg {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    rightImg w x t - w t ≤ markPos w t x := by
  classical
  have hlow : ∀ q : ℚ, ((rightImg w x t - w t : ℝ) : EReal) ≤ markTerm w t x q := by
    intro q
    unfold markTerm
    split_ifs with hq
    · obtain ⟨hxq, u, hu⟩ := hq
      have halive : Alive w q t := Sec7.Lemma76E.alive_of_isForwardSol hw ht
        (by rw [hw0]; exact hx.trans_lt hxq) hu
      have h1 := rightImg_le_gImg hw ht hxq halive
      have hf := fwdMap_eq_of_isForwardSol hw (WangWu.isForwardSol_of_alive hw halive) ⟨ht, le_rfl⟩
      rw [hf]
      simp only [gImg] at h1
      exact EReal.coe_le_coe_iff.2 (by simp; linarith)
    · exact le_top
  have hge := le_iInf hlow
  have hbot := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
  unfold markPos
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal (ne_top_iInf_markTerm hw ht x) hbot]
  exact hge

/-- Every nonnegative boundary mark has the same record and geometric image.
The infimum construction retains the mark after swallowing. -/
theorem markPos_eq_rightImg_of_nonneg {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    markPos w t x = rightImg w x t - w t := by
  classical
  refine le_antisymm ?_ (rightImg_sub_le_markPos_of_nonneg hw hw0 ht hx)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y, hxy, hyA, hyg⟩ := exists_lt_of_rightImg_lt hw ht
    (show rightImg w x t < rightImg w x t + ε / 2 by linarith)
  obtain ⟨q, hyq, hqy⟩ := exists_rat_btwn (show y < y + ε / 2 by linarith)
  have hqA : Alive w q t := hyA.of_le hw hyq.le ht
  have hlip := abs_gImg_sub_le hw ht hyA hqA
  rw [abs_of_pos (by linarith : (0 : ℝ) < q - y)] at hlip
  have hgq : gImg w q t < rightImg w x t + ε := by
    have := (abs_le.1 hlip).2
    linarith
  have hu := WangWu.isForwardSol_of_alive hw hqA
  have hf := fwdMap_eq_of_isForwardSol hw hu ⟨ht, le_rfl⟩
  have hterm : markTerm w t x q = (((fwdMap w t ((q : ℝ) : ℂ)).re : ℝ) : EReal) := by
    unfold markTerm
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hxy.trans hyq, _, hu⟩)
  have hre : (fwdMap w t ((q : ℝ) : ℂ)).re = gImg w q t - w t := by
    rw [hf]
    simp only [gImg]
    simp
  have hle : (⨅ q' : ℚ, markTerm w t x q') ≤ (((gImg w q t - w t : ℝ)) : EReal) := by
    rw [← hre, ← hterm]
    exact iInf_le _ q
  have hbot : (⨅ q' : ℚ, markTerm w t x q') ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (zero_le_iInf_markTerm hw hw0 ht hx)
  have h1 : markPos w t x ≤ gImg w q t - w t := by
    unfold markPos
    have := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  linarith

/-- The corresponding identity for every nonpositive left boundary mark. -/
theorem markPosL_eq_rightImg_of_nonpos {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : x ≤ 0) :
    markPosL w t x = -rightImg (fun s => -w s) (-x) t - w t := by
  have h := markPos_eq_rightImg_of_nonneg hw.neg (by simp [hw0]) ht (neg_nonneg.2 hx)
  change markPos (fun s => -w s) t (-x) = rightImg (fun s => -w s) (-x) t - (-w t) at h
  unfold markPosL
  rw [h]
  ring

/-- Initial boundary-data agreement transports to all record marks of a
continuous driver. Every original label remains present after mergers. -/
theorem exists_finset_record_boundary_eq {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) (κ : ℝ)
    {nL nR mL mR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hyL : ∀ i, yL i ≤ 0) (hyR : ∀ j, 0 ≤ yR j)
    {E : Finset ℝ} (h0 : ∀ x ∉ E,
      forceBoundaryData κ ρL ρR xL xR x = forceBoundaryData κ σL σR yL yR x) :
    ∃ F : Finset ℝ, ∀ y ∉ F,
      forceBoundaryData κ ρL ρR (fun i => markPosL w t (xL i))
        (fun j => markPos w t (xR j)) y =
      forceBoundaryData κ σL σR (fun i => markPosL w t (yL i))
        (fun j => markPos w t (yR j)) y := by
  simpa only [markPos_eq_rightImg_of_nonneg hw hw0 ht (hxR _),
    markPosL_eq_rightImg_of_nonpos hw hw0 ht (hxL _),
    markPos_eq_rightImg_of_nonneg hw hw0 ht (hyR _),
    markPosL_eq_rightImg_of_nonpos hw hw0 ht (hyL _)] using
    CrossRestart.KernelQ.exists_finset_forceBoundaryData_flow_eq hw ht κ
      ρL ρR σL σR hxL hxR hyL hyR h0

end InteractingSLE.Sec5.CrossCond.Gen
