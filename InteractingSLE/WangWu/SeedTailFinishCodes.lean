/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailBarrier
import InteractingSLE.Spec.Sec5.Prop49QExitRestart
import InteractingSLE.Spec.Sec5.CfBarrier

/-!
# The Borel right-gap event for restarting the shifted killed word

PROVE-WW-B27 continuation. Uniform positive bounds on rational points of compact
positive-time intervals encode strict positivity of a continuous force gap.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec7.RandRestart Sec5.Prop49Exit

/-- Countably many positive lower bounds away from time zero. -/
def GapBounds (w v : ℝ≥0 → ℝ) : Prop :=
  ∀ m n : ℕ, ∃ k : ℕ, ∀ q : ℚ,
    1 / ((m : ℝ) + 1) ≤ (q : ℝ) → (q : ℝ) ≤ (n : ℝ) + 1 →
    1 / ((k : ℝ) + 1) ≤ v (q : ℝ).toNNReal - w (q : ℝ).toNNReal

theorem gapBounds_of_pos {w v : ℝ≥0 → ℝ} (hw : Continuous w) (hv : Continuous v)
    (hp : ∀ t : ℝ≥0, 0 < t → w t < v t) : GapBounds w v := by
  intro m n
  let l : ℝ≥0 := 1 / ((m : ℝ≥0) + 1)
  let r : ℝ≥0 := n + 1
  have hl : 0 < l := by dsimp [l]; positivity
  have hlr : l ≤ r := by
    have hl1 : l ≤ 1 := (div_le_one (by positivity)).2 (by simp)
    exact hl1.trans (by dsimp [r]; exact le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ n from bot_le))
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hlr)
    (hv.sub hw).continuousOn
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (hp t (hl.trans_le ht.1)))
  refine ⟨k, fun q hq hqr => hk.le.trans (hmin ?_)⟩
  have hq0 : 0 ≤ (q : ℝ) := (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1)).trans hq
  constructor
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    simpa only [l, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast] using hq
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    simpa only [r, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hqr

theorem pos_of_gapBounds {w v : ℝ≥0 → ℝ} (hw : Continuous w) (hv : Continuous v)
    (hb : GapBounds w v) (t : ℝ≥0) (ht : 0 < t) : w t < v t := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t by exact_mod_cast ht)
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨k, hk⟩ := hb m n
  have hcast : ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) = 1 / ((m : ℝ) + 1) := by push_cast; rfl
  have hlow : ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) ≤ t := by rw [hcast]; exact hm.le
  have hupp : (t : ℝ) < ((n : ℚ) + 1 : ℚ) := by exact_mod_cast (lt_add_one _ |>.trans_le' hn.le)
  have hcl := mem_closure_ratWindow hlow hupp
  have hcont : Continuous (fun s : ℝ => v s.toNNReal - w s.toNNReal) :=
    (hv.sub hw).comp continuous_real_toNNReal
  have hle : 1 / ((k : ℝ) + 1) ≤ v t - w t := by
    have h := ContinuousWithinAt.closure_le hcl continuousWithinAt_const hcont.continuousAt.continuousWithinAt
      (fun q hq => by
        obtain ⟨q, rfl, hqm, hqn⟩ := hq
        apply hk q
        · rw [← hcast]
          exact_mod_cast hqm
        · exact_mod_cast hqn)
    simpa only [Real.toNNReal_coe] using h
  exact sub_pos.1 (lt_of_lt_of_le (by positivity) hle)

/-- The canonical solution has infinite lifetime and a positive first right gap. -/
def rightGapCode {nL : ℕ} : Set (XCode nL 2) :=
  {x | cζ x = ⊤ ∧ GapBounds (cw x) (cvR x 0)}

theorem measurableSet_rightGapCode {nL : ℕ} : MeasurableSet (rightGapCode (nL := nL)) := by
  refine (measurableSet_eq_fun measurable_cζ measurable_const).inter ?_
  refine measurableSet_setOfPred.2 (Measurable.forall fun m => Measurable.forall fun n =>
    Measurable.exists fun k => Measurable.forall fun q => ?_)
  exact Measurable.imp measurable_const (Measurable.imp measurable_const
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const
      ((measurable_cvR_at 0 _).sub (measurable_cw_at _)))))

theorem rightGapCode_pos {nL : ℕ} {κ : ℝ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin 2 → ℝ}
    {x : XCode nL 2} (hx : x ∈ CRel κ xL xR ρL ρR) (hS : x ∈ rightGapCode) :
    ∀ t : ℝ≥0, 0 < t → cw x t < cvR x 0 t := by
  have hw : Continuous (cw x) := continuousOn_univ.1
    (hx.1.1.continuousOn_w.mono fun t _ => by rw [hS.1]; exact ENNReal.coe_lt_top)
  have hv : Continuous (cvR x 0) := continuousOn_univ.1
    ((hx.1.1.continuousOn_vR 0).mono fun t _ => by rw [hS.1]; exact ENNReal.coe_lt_top)
  exact pos_of_gapBounds hw hv hS.2

/-- Both shifted prefix sums stay above `-1`, uniformly in the mark positions. -/
theorem shifted_groupEndSums {rL rR δ : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hd : 0 ≤ δ) (hd1 : δ < 1) (xL xR : Fin 2 → ℝ) :
    Sec4.HasGroupEndSums (-1) ![rL, -rL - δ] (-xL) ∧
      Sec4.HasGroupEndSums 0 ![rR, -rR + δ] xR := by
  constructor
  · intro j _
    fin_cases j
    · change -1 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ![rL, -rL - δ] i
      rw [show Finset.univ.filter (fun i : Fin 2 => i ≤ 0) = {0} from by decide]
      simp only [Finset.sum_singleton, Matrix.cons_val_zero]
      linarith only [hL]
    · change -1 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 1), ![rL, -rL - δ] i
      rw [show Finset.univ.filter (fun i : Fin 2 => i ≤ 1) = Finset.univ from by decide, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith only [hd1]
  · intro j _
    fin_cases j
    · change 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ![rR, -rR + δ] i
      rw [show Finset.univ.filter (fun i : Fin 2 => i ≤ 0) = {0} from by decide]
      simpa only [Finset.sum_singleton, Matrix.cons_val_zero] using hR
    · change 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 1), ![rR, -rR + δ] i
      rw [show Finset.univ.filter (fun i : Fin 2 => i ≤ 1) = Finset.univ from by decide, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith only [hd]

end InteractingSLE.WangWu.SeedTail
