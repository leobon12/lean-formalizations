/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalWord
import InteractingSLE.Spec.Sec7.StripDetWord

/-!
# The two-sweep step for the stage words (deterministic)

PROVE-GW2-ROOTX round 6. The `startsU` clause of the slow shell ("every right mark other than the first at absolute
position `≥ 7/4`", p. 146) rests on one step of the stage words: a positive jump of a stop word is the record image
`markPos` of a right mark of the previous word (`Sec5.CrossCond.StagedFinal.mem_jumps_stopWord`), and right marks move
right in absolute terms (`g_T(x) ≥ x`).

* `le_markPos_add`: `x ≤ markPos w T x + w T` for `x ≥ 0`;
* `nonneg_add_rdrv_of_mem_jumps_stopWord`: a positive jump `y` of a stop word has `0 ≤ y + U(T)`;
* `rdrv_rtime_stgRec`: a stage piece's record reads its driver's increment;
* **`le_add_of_mem_jumps_stageWord_pastOf`**: for the stage words flowed through a driver's pieces, every positive jump
  `y` after `n + 1` pieces has `R(b n) ≤ R(b (n+1)) + y`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Ru

open Restart Exist.Staged Exist.StagedLaw GW2Wm

/-- **A right mark at a nonnegative position moves right in absolute terms**: `x ≤ g_T(x) = markPos w T x + w T`. -/
theorem le_markPos_add {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    x ≤ markPos w T x + w T := by
  rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hw hw0 hT hx, sub_add_cancel]
  calc x = MartChar.RealFlow.rightImg w x 0 := (MartChar.RealFlow.rightImg_zero hw hw0 hx).symm
    _ ≤ _ := MartChar.RealFlow.rightImg_mono_time hw x le_rfl hT

/-- **One step of the two-sweep**: a positive jump of a stop word is the record image of a right mark of the word
(`Sec5.CrossCond.StagedFinal.mem_jumps_stopWord`), so it lies right of the piece's start tip in absolute terms:
`0 ≤ y + U(T)` for the record's driver `U` and time `T`. -/
theorem nonneg_add_rdrv_of_mem_jumps_stopWord {κ θ : ℝ} {c : BoundaryWord} {r : RecData} {y : ℝ}
    (hy : y ∈ (stopWord κ (c, θ, r)).jumps) (hy0 : 0 < y) : 0 ≤ y + rdrv r (rtime r) := by
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT : 0 ≤ rtime r := Sec7.StripDet.rtime_nonneg r
  rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hy with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
  · exfalso
    have := Sec7.StripDet.markPosL_nonpos hw hw0 hT (GW3Word.flowLineXL_nonpos c.fn c.jumps i)
    linarith
  · exact absurd hy0 (lt_irrefl 0)
  · have := le_markPos_add hw hw0 hT (GW3Word.flowLineXR_nonneg c.fn c.jumps j)
    have hp := GW3Word.flowLineXR_nonneg c.fn c.jumps j
    linarith


/-- The record of a stage piece reads its driver's increment at its own time. -/
theorem rdrv_rtime_stgRec {R : ℝ≥0 → ℝ} (hR : Continuous R) {a b : ℝ≥0} (hab : a ≤ b) :
    rdrv (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤))
        (rtime (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤))) = R b - R a := by
  have he := GW2TipSystem.Gm.isRegularDriver_top (GW2Rd.continuous_stgDrv hR a) (GW2Rd.stgDrv_zero R a)
  have hfin : min ((b - a : ℝ≥0) : ℝ≥0∞) ((fun u => GW2Rd.stgDrv R a u, (⊤ : ℝ≥0∞)) :
      (ℝ≥0 → ℝ) × ℝ≥0∞).2 ≠ ⊤ := by
    simp only [min_top_right]
    exact ENNReal.coe_ne_top
  have ht : rtime (recOf ((b - a : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤)) = ((b - a : ℝ≥0) : ℝ) := by
    rw [rtime_recOf_coe]
    simp only [min_top_right, ENNReal.toNNReal_coe]
  rw [ht, GW2TipSystem.Gm.rdrv_recOf_eq he hfin (GW2Rd.continuous_stgDrv hR a).continuousOn (b - a)]
  simp only [min_top_right, ENNReal.toNNReal_coe, min_self, GW2Rd.stgDrv, add_tsub_cancel_of_le hab]

/-- **The two-sweep on the stage words flowed through a driver's pieces**: every positive jump `y` of the stage word
after `n + 1` pieces lies, in absolute position `R(b (n+1)) + y`, right of the tip `R(b n)` at the previous
boundary. -/
theorem le_add_of_mem_jumps_stageWord_pastOf {κ : ℝ} {W₀ : RecData → BoundaryWord} {θ : ℕ → ℝ} {cf : RecData}
    {R : ℝ≥0 → ℝ} (hR : Continuous R) {b : ℕ → ℝ≥0} {n : ℕ} (hb : b n ≤ b (n + 1)) {y : ℝ}
    (hy : y ∈ (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) (pastOf cf R b (n + 1))).jumps) (hy0 : 0 < y) :
    R (b n) ≤ R (b (n + 1)) + y := by
  have h := nonneg_add_rdrv_of_mem_jumps_stopWord hy hy0
  change 0 ≤ y + rdrv (recOf ((b (n + 1) - b n : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))
    (rtime (recOf ((b (n + 1) - b n : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))) at h
  rw [rdrv_rtime_stgRec hR hb] at h
  linarith

end InteractingSLE.Theorem14.GW2Ru
