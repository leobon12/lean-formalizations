/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitKilled
import InteractingSLE.Spec.Sec5.CrossCondMart

/-!
# Proposition 4.9's image word satisfies the strip hypotheses of Aux. lemma 22

Packet PROVE-GLUECOND9. The image word of the flow line in the counterflow chart (`Sec5.CrossCond.Word49`, corrected
junction weights of ruling R57: `cL6 κ Σ = κ − 4 − Σ`, `cR6 κ Σ = κ/2 − 2 − Σ`) has left weights
`jwL cL6 κ ρL = (ρL, κ − 4 − Σρ_L)` and right weights `jwR cR6 κ ρR = (ρR, κ/2 − 2 − Σρ_R)`. For an ordered (4.4)
word (`Sec4.Cond44`: left prefix sums at least `κ/2 − 2`, right prefix sums nonnegative) and `0 < κ < 4`, these
satisfy the hypotheses of the left strip end (`Prop49QExitKilled.ae_leftExit_of_killed`):

* `hasStripPrefixSums_jw`: the left prefix sums before the junction and all right prefix sums are at least
  `κ/2 − 2` (the right total is exactly `κ/2 − 2`);
* `abs_charge_jw_lt`: the cumulative left weight through the junction is `κ − 4 ∈ (κ/2 − 4, κ/2 − 2)`, i.e.
  `|q₊ − q₋| = |2 − κ| < 2`.

This is the source's count (Remark 4.10 with the corrected chart heights, PROVE-GLUECOND7 "Weights"): the left
cumulative image weight `κ − 4 < κ/2 − 2` lets the image curve exit beyond the left junction, the right one
`κ/2 − 2` is critical.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop49Exit

open CrossCond.Word49

variable {nL nR : ℕ}

/-- The prefix `{i | i.val < j + 1}` of `Fin n` is `Iic j`. -/
theorem filter_val_lt_succ_eq_Iic {n : ℕ} (j : Fin n) :
    (univ.filter fun i : Fin n => i.val < j.val + 1) = Iic j := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_Iic, Fin.le_def]
  omega

/-- The left prefix sums of an ordered (4.4) word, in `Iic` form. -/
theorem le_sum_Iic_left {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h44 : Sec4.Cond44 κ ρL ρR) (j : Fin nL) :
    κ / 2 - 2 ≤ ∑ i ∈ Iic j, ρL i := by
  have h := h44.1 (j.val + 1) (by omega) (by omega)
  rwa [filter_val_lt_succ_eq_Iic] at h

/-- The right prefix sums of an ordered (4.4) word, in `Iic` form. -/
theorem le_sum_Iic_right {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h44 : Sec4.Cond44 κ ρL ρR) (j : Fin nR) :
    0 ≤ ∑ i ∈ Iic j, ρR i := by
  have h := h44.2 (j.val + 1) (by omega) (by omega)
  rwa [filter_val_lt_succ_eq_Iic] at h

/-- A prefix sum of `Fin.snoc f c` before the last index is a prefix sum of `f`. -/
theorem sum_Iic_snoc_castSucc {n : ℕ} (f : Fin n → ℝ) (c : ℝ) (k : Fin n) :
    ∑ i ∈ Iic k.castSucc, (Fin.snoc f c : Fin (n + 1) → ℝ) i = ∑ i ∈ Iic k, f i := by
  have e : Iic k.castSucc = (Iic k).map Fin.castSuccEmb := by
    ext i
    simp only [mem_Iic, mem_map, Fin.castSuccEmb_apply]
    constructor
    · intro hi
      refine ⟨i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt hi (Fin.castSucc_lt_last k))), ?_, by simp⟩
      rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]
      exact hi
    · rintro ⟨a, ha, rfl⟩
      exact Fin.castSucc_le_castSucc_iff.2 ha
  rw [e, sum_map]
  simp

/-- The full prefix sum of `Fin.snoc f c`. -/
theorem sum_Iic_snoc_last {n : ℕ} (f : Fin n → ℝ) (c : ℝ) :
    ∑ i ∈ Iic (Fin.last n), (Fin.snoc f c : Fin (n + 1) → ℝ) i = (∑ i, f i) + c := by
  have e : Iic (Fin.last n) = (univ : Finset (Fin (n + 1))) := by
    ext i; simp [Fin.le_last]
  rw [e, Fin.sum_univ_castSucc]
  simp

/-- **The strip prefix sums of the image word** (`0 < κ < 4`, an ordered (4.4) word). -/
theorem hasStripPrefixSums_jw {κ : ℝ} (hκ4 : κ < 4) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h44 : Sec4.Cond44 κ ρL ρR) :
    Strip.HasStripPrefixSums κ (Fin.init (jwL cL6 κ ρL)) (jwR cR6 κ ρR) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have e : Fin.init (jwL cL6 κ ρL) = ρL := by simp [jwL]
    rw [e]
    exact le_sum_Iic_left h44 j
  · induction j using Fin.lastCases with
    | last =>
      simp only [jwR, cR6]
      rw [sum_Iic_snoc_last]
      linarith
    | cast k =>
      simp only [jwR]
      rw [sum_Iic_snoc_castSucc]
      linarith [le_sum_Iic_right h44 k]

/-- **The charge condition of the image word**: `q₋ = κ − 4`, `q₊ = −2`, `|q₊ − q₋| = |2 − κ| < 2`. -/
theorem abs_charge_jw_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    |Strip.chargePlus κ (Fin.init (jwL cL6 κ ρL)) (jwR cR6 κ ρR) (jwL cL6 κ ρL (Fin.last nL)) -
      Strip.chargeMinus (Fin.init (jwL cL6 κ ρL)) (jwL cL6 κ ρL (Fin.last nL))| < 2 := by
  have hm : Strip.chargeMinus (Fin.init (jwL cL6 κ ρL)) (jwL cL6 κ ρL (Fin.last nL)) = κ - 4 := by
    simp only [Strip.chargeMinus, jwL, cL6, Fin.init_snoc, Fin.snoc_last]
    ring
  have hsum := Strip.chargePlus_add_chargeMinus κ (Fin.init (jwL cL6 κ ρL)) (jwR cR6 κ ρR)
    (jwL cL6 κ ρL (Fin.last nL))
  rw [abs_lt]
  constructor <;> linarith

end InteractingSLE.Sec5.Prop49Exit
