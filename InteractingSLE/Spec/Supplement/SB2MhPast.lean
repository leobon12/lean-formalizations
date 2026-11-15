/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideInputs

/-!
# The capped retained pasts increase with the cap

Packet PROVE-SB2-LCMEAN, round 5. K2's line filtration at SB2(2)'s lower piece `ℓ` is the retained past of the capped
program `capSpec w ℓ θ τ` after `ℓ + 1` instructions, indexed by the cap `τ` (the piece's own time). The landed
`WalkSide.pastSigma_capSpec_le` compares a rational cap with the unstopped piece only. Here two caps are compared:

* `capRecFrom σ r`: the record of a piece stopped at the rational time `σ`, read from its record stopped at any later
  time (stop `min σ L`, threshold flag `b && (L ≤ σ)`);
* **`readRec_retOf_capFrom`**: for `σ ≤ t`, `readRec (retOf σ e) = capRecFrom σ (readRec (retOf t e))`;
* **`pastSigma_capSpec_mono`**: for a rational `σ ≤ t`, the capped past at `σ` lies in the capped past at `t`.

Deterministic bookkeeping of the run records; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Mh

open Exist Exist.Staged Exist.StagedLaw WalkSide

/-- The record of a piece stopped at the rational time `σ`, read from its record stopped at a later time. -/
def capRecFrom (σ : ℚ≥0) (r : RecData) : RecData :=
  (fun q : ℚ => r.1 (min q (σ : ℚ)), min ((σ : ℝ≥0) : ℝ≥0∞) r.2.1, r.2.2 && decide (r.2.1 ≤ ((σ : ℝ≥0) : ℝ≥0∞)))

theorem measurable_capRecFrom (σ : ℚ≥0) : Measurable (capRecFrom σ) := by
  have hdec : (fun r : RecData => r.2.2 && decide (r.2.1 ≤ ((σ : ℝ≥0) : ℝ≥0∞))) =
      fun r => if r.2.1 ≤ ((σ : ℝ≥0) : ℝ≥0∞) then r.2.2 else false := by
    funext r
    by_cases hr : r.2.1 ≤ ((σ : ℝ≥0) : ℝ≥0∞) <;> simp [hr]
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst)
    (Measurable.prodMk (measurable_const.min (measurable_fst.comp measurable_snd)) ?_)
  rw [hdec]
  exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
    (measurable_snd.comp measurable_snd) measurable_const

/-- **The record at a rational cap is read from the record at any later cap.** -/
theorem readRec_retOf_capFrom (σ : ℚ≥0) {t : ℝ≥0∞} (hσt : ((σ : ℝ≥0) : ℝ≥0∞) ≤ t)
    (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : readRec (retOf ((σ : ℝ≥0) : ℝ≥0∞) e) = capRecFrom σ (readRec (retOf t e)) := by
  have hmin : min ((σ : ℝ≥0) : ℝ≥0∞) (min t e.2) = min ((σ : ℝ≥0) : ℝ≥0∞) e.2 := by
    rw [← min_assoc, min_eq_left hσt]
  simp only [readRec, retOf, capRecFrom]
  refine Prod.ext (funext fun q => ?_) (Prod.ext hmin.symm ?_)
  · have e1 : (((min q (σ : ℚ) : ℚ) : ℝ).toNNReal : ℝ≥0∞) =
        min ((q : ℝ).toNNReal : ℝ≥0∞) ((σ : ℝ≥0) : ℝ≥0∞) := by
      rw [Rat.cast_min, Monotone.map_min (fun _ _ h => Real.toNNReal_le_toNNReal h), ENNReal.coe_min]
      rw [show ((σ : ℚ) : ℝ) = ((σ : ℝ≥0) : ℝ) by norm_cast, Real.toNNReal_coe]
    simp only [e1, min_assoc, hmin]
  · by_cases hζ : e.2 ≤ t
    · have hL : min t e.2 = e.2 := min_eq_right hζ
      simp only [hL, hζ, decide_true, Bool.true_and]
    · have hσζ : ¬ e.2 ≤ ((σ : ℝ≥0) : ℝ≥0∞) := fun h => hζ (h.trans hσt)
      simp only [hζ, hσζ, decide_false, Bool.false_and]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ}

/-- **The capped retained pasts increase with the cap** (a rational cap below any later cap; instruction `ℓ` an
angle-`θ` flow of `w`). -/
theorem pastSigma_capSpec_mono {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hℓ : ℓ ≤ w.2.2.length) {t₀ : ℝ≥0∞}
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t₀))) (σ : ℚ≥0) {t : ℝ≥0∞} (hσt : ((σ : ℝ≥0) : ℝ≥0∞) ≤ t) :
    pastSigma κ b jumps (capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ≤
      pastSigma κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) := by
  rw [pastSigma_eq_comap (spec := capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞))]
  let _ : MeasurableSpace Ω := pastSigma κ b jumps (capSpec w ℓ θ t) E (ℓ + 1)
  have hpm : Measurable (pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1)) :=
    comap_measurable (pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1))
  refine Measurable.comap_le (measurable_pi_iff.2 fun i => ?_)
  have hp : Measurable fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i :=
    (measurable_pi_apply i).comp hpm
  by_cases hi : (i : ℕ) < ℓ
  · have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ω i) =
        fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        readRec ((ExplState.run κ b jumps (capSpec w ℓ θ t) (fun j => E j ω) (ℓ + 1)).2.2.1 i)
      rw [retained_run_succ_of_lt _ _ hi, retained_run_succ_of_lt _ _ hi,
        run_capSpec_of_le (τ := ((σ : ℝ≥0) : ℝ≥0∞)) hℓ _ le_rfl, run_capSpec_of_le (τ := t) hℓ _ le_rfl]
    rw [e]
    exact hp
  · have hiℓ : (i : ℕ) = ℓ := le_antisymm (Nat.lt_succ_iff.1 i.2) (not_lt.1 hi)
    have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ω i) =
        capRecFrom σ ∘ fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ ((σ : ℝ≥0) : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        capRecFrom σ (readRec ((ExplState.run κ b jumps (capSpec w ℓ θ t) (fun j => E j ω) (ℓ + 1)).2.2.1 i))
      rw [hiℓ, retained_run_succ_self, retained_run_succ_self, launches_run_capSpec_succ hℓ hwℓ,
        launches_run_capSpec_succ hℓ hwℓ, instrTime_capSpec hℓ, instrTime_capSpec hℓ]
      split_ifs
      · simp [capRecFrom, readRec]
      · exact readRec_retOf_capFrom σ hσt _
    rw [e]
    exact (measurable_capRecFrom σ).comp hp

end InteractingSLE.Theorem14.SB.Mh
