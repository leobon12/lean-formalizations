/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Pos
import InteractingSLE.Spec.Exist.StagedLaw3Word

/-!
# The word of the conditional law at the stop

Packet PROVE-STAGEDLAW3. The word `β (c, θ, r)` of `StopCondLawStatement`: the sorted word (`forceWord`) of the
force data of the angle-`θ` flow line from the seed `0` of the datum `c` (`padFL`), at the mark positions read from the
record `r` (`markPosL`, `markPos` with the record driver `rdrv r` at the record time `rtime r`), shifted by `−θχ`.

* `rdrv`, `rtime`: the driver and the time of a record (`rdrv (recOf t e) = recDrv t e`, `rtime (recOf t e) =
  stopTime t e`);
* `padFL_weights`: the weights of the padded flow-line word are affine in `θ` (only the seed weights depend on `θ`);
* `stopWord κ`, **`measurable_stopWord`**, `isSorted_stopWord`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Restart Staged

/-! ### The driver and the time of a record -/

/-- The driver read from a record (continuous for every record). -/
def rdrv (r : RecData) : ℝ → ℝ := fun x => LocalExt.histDrv (recHist r) x.toNNReal

/-- The time of a record (`0` for an infinite stop). -/
def rtime (r : RecData) : ℝ := (r.2.1.toNNReal : ℝ)

theorem continuous_rdrv (r : RecData) : Continuous (rdrv r) :=
  (LocalExt.continuous_histDrv _).comp continuous_real_toNNReal

theorem rdrv_zero (r : RecData) : rdrv r 0 = 0 := by
  simp only [rdrv, Real.toNNReal_zero, LocalExt.histDrv_zero]

theorem rtime_nonneg (r : RecData) : 0 ≤ rtime r := NNReal.coe_nonneg _

theorem measurable_rdrv_apply (x : ℝ) : Measurable fun r : RecData => rdrv r x :=
  (LocalExt.measurable_histDrv_apply x.toNNReal).comp measurable_recHist

theorem measurable_rtime : Measurable rtime :=
  measurable_coe_nnreal_real.comp ((measurable_fst.comp measurable_snd).ennreal_toNNReal)

theorem rdrv_recOf (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : rdrv (recOf t e) = recDrv t e := rfl

theorem rtime_recOf (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : rtime (recOf t e) = stopTime t e := rfl

/-! ### The weights of the padded flow-line word -/

theorem padFL_fst (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) : (padFL κ θ b J).1 = (padFL 0 0 b J).1 := rfl

/-- **Only the seed weights depend on `θ`.** -/
theorem padFL_weights (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    (padFL κ θ b J).2 =
      ((fun i => (padFL κ 0 b J).2.1 i - if i = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0),
        fun j => (padFL κ 0 b J).2.2 j + if j = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0) := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · change (if hi : i < flowLineNL b J 0 then flowLineRhoL κ b J 0 θ ⟨i, hi⟩ else 0) =
      (if hi : i < flowLineNL b J 0 then flowLineRhoL κ b J 0 0 ⟨i, hi⟩ else 0) -
        if i = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0
    by_cases hi : i < flowLineNL b J 0
    · rw [dite_eq_left hi, dite_eq_left hi]
      unfold flowLineRhoL
      rcases i with _ | k
      · rw [ite_eq_left rfl]
        change -(PiecewiseConstantBoundaryData.leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 =
          -(PiecewiseConstantBoundaryData.leftLim b 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1 -
            θ * QuantumZipper.chiC κ / sleLambda κ
        ring
      · rw [ite_eq_right (Nat.succ_ne_zero k), sub_zero]
        rfl
    · have h0 : i ≠ 0 := fun h => hi (by rw [h]; unfold flowLineNL; omega)
      rw [dite_eq_right hi, dite_eq_right hi, ite_eq_right h0, sub_zero]
  · change (if hj : j < flowLineNR b J 0 then flowLineRhoR κ b J 0 θ ⟨j, hj⟩ else 0) =
      (if hj : j < flowLineNR b J 0 then flowLineRhoR κ b J 0 0 ⟨j, hj⟩ else 0) +
        if j = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0
    by_cases hj : j < flowLineNR b J 0
    · rw [dite_eq_left hj, dite_eq_left hj]
      unfold flowLineRhoR
      rcases j with _ | k
      · rw [ite_eq_left rfl]
        change (PiecewiseConstantBoundaryData.rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 =
          (PiecewiseConstantBoundaryData.rightLim b 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1 +
            θ * QuantumZipper.chiC κ / sleLambda κ
        ring
      · rw [ite_eq_right (Nat.succ_ne_zero k), add_zero]
        rfl
    · have h0 : j ≠ 0 := fun h => hj (by rw [h]; unfold flowLineNR; omega)
      rw [dite_eq_right hj, dite_eq_right hj, ite_eq_right h0, add_zero]

/-! ### The word -/

/-- **The word of the conditional law at the stop**: the sorted force word of the angle-`θ` flow line of `c` at the
mark positions read from the record `r`, shifted by `−θχ`. -/
def stopWord (κ : ℝ) (x : BoundaryWord × ℝ × RecData) : BoundaryWord :=
  forceWord κ (flowLineNL x.1.fn x.1.jumps 0) (flowLineNR x.1.fn x.1.jumps 0)
    (fun i => markPosL (rdrv x.2.2) (rtime x.2.2) ((padFL 0 0 x.1.fn x.1.jumps).1.1 i))
    (fun j => markPos (rdrv x.2.2) (rtime x.2.2) ((padFL 0 0 x.1.fn x.1.jumps).1.2 j))
    (padFL κ x.2.1 x.1.fn x.1.jumps).2.1 (padFL κ x.2.1 x.1.fn x.1.jumps).2.2 (x.2.1 * QuantumZipper.chiC κ)

theorem isSorted_stopWord (κ : ℝ) (x : BoundaryWord × ℝ × RecData) : (stopWord κ x).IsSorted :=
  isSorted_forceWord _ _ _ _ _ _ _ _

theorem measurable_padFL_weights (κ : ℝ) :
    Measurable fun x : BoundaryWord × ℝ × RecData => (padFL κ x.2.1 x.1.fn x.1.jumps).2 := by
  have h0 : Measurable fun x : BoundaryWord × ℝ × RecData => padFL κ 0 x.1.fn x.1.jumps := by
    have hc : Measurable fun x : BoundaryWord × ℝ × RecData => x.1 := measurable_fst
    have h := (wordMeasStatement.2.2 κ 0).comp hc
    exact h
  have hθ : Measurable fun x : BoundaryWord × ℝ × RecData => x.2.1 := measurable_fst.comp measurable_snd
  have e : (fun x : BoundaryWord × ℝ × RecData => (padFL κ x.2.1 x.1.fn x.1.jumps).2) = fun x =>
      ((fun i => (padFL κ 0 x.1.fn x.1.jumps).2.1 i -
          if i = 0 then x.2.1 * QuantumZipper.chiC κ / sleLambda κ else 0),
        fun j => (padFL κ 0 x.1.fn x.1.jumps).2.2 j +
          if j = 0 then x.2.1 * QuantumZipper.chiC κ / sleLambda κ else 0) := by
    funext x
    exact padFL_weights κ x.2.1 x.1.fn x.1.jumps
  rw [e]
  have hc : ∀ i : ℕ, Measurable fun x : BoundaryWord × ℝ × RecData =>
      if i = 0 then x.2.1 * QuantumZipper.chiC κ / sleLambda κ else 0 := fun i => by
    split_ifs
    · exact (hθ.mul_const _).div_const _
    · exact measurable_const
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun j => ?_)
  · exact (((measurable_pi_apply i).comp measurable_fst).comp (measurable_snd.comp h0)).sub (hc i)
  · exact (((measurable_pi_apply j).comp measurable_snd).comp (measurable_snd.comp h0)).add (hc j)

/-- **The word of the conditional law at the stop is jointly measurable.** -/
theorem measurable_stopWord (κ : ℝ) : Measurable (stopWord κ) := by
  have hc : Measurable fun x : BoundaryWord × ℝ × RecData => x.1 := measurable_fst
  have hr : Measurable fun x : BoundaryWord × ℝ × RecData => x.2.2 := measurable_snd.comp measurable_snd
  have hpos : Measurable fun x : BoundaryWord × ℝ × RecData => padFL 0 0 x.1.fn x.1.jumps := by
    have h := (wordMeasStatement.2.2 0 0).comp hc
    exact h
  have hW : ∀ t, Measurable fun x : BoundaryWord × ℝ × RecData => rdrv x.2.2 t := fun t =>
    (measurable_rdrv_apply t).comp hr
  have hτ : Measurable fun x : BoundaryWord × ℝ × RecData => rtime x.2.2 := measurable_rtime.comp hr
  have hw := measurable_padFL_weights κ
  refine measurable_forceWord κ (wordMeasStatement.1.comp hc) (wordMeasStatement.2.1.comp hc) ?_ ?_
    (measurable_fst.comp hw) (measurable_snd.comp hw) ((measurable_fst.comp measurable_snd).mul_const _)
  · refine measurable_pi_iff.2 fun i => ?_
    exact measurable_markPosL (fun x => continuous_rdrv _) hW (fun x => rdrv_zero _) hτ (fun x => rtime_nonneg _)
      (((measurable_pi_apply i).comp measurable_fst).comp (measurable_fst.comp hpos))
  · refine measurable_pi_iff.2 fun j => ?_
    exact measurable_markPos (fun x => continuous_rdrv _) hW (fun x => rdrv_zero _) hτ (fun x => rtime_nonneg _)
      (((measurable_pi_apply j).comp measurable_snd).comp (measurable_fst.comp hpos))

end StagedLaw

end Exist

end InteractingSLE
