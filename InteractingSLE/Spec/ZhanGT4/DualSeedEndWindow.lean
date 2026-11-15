/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndRestart

/-!
# Cutting an original-clock stochastic sum at a deterministic time

Packet PROVE-ZHAN-GT4-A22. The difference between an interval increment
and the coefficient killed before its left endpoint is confined to the
single crossing cell. The checked boundary-error lemma controls it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*}

/-- Keep an original-clock coefficient only from `ε` onwards. -/
def seedEndWindow (ε : ℝ≥0) (c : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if ε ≤ u then c u ω else 0

/-- Exact cell algebra for cutting at `ε`; only a strict crossing remains. -/
theorem seedEndWindow_cell (c B : ℝ≥0 → Ω → ℝ) (ε a b : ℝ≥0) (hab : a ≤ b) (ω : Ω) :
    c a ω * (B b ω - B a ω) - c (min a ε) ω * (B (min b ε) ω - B (min a ε) ω) -
      seedEndWindow ε c a ω * (B b ω - B a ω) =
        if a < ε ∧ ε < b then c a ω * (B b ω - B ε ω) else 0 := by
  by_cases ha : ε ≤ a
  · simp only [seedEndWindow, ha, ite_true, min_eq_right ha, min_eq_right (ha.trans hab),
      not_lt_of_ge ha, false_and, ite_false, sub_self, mul_zero, sub_zero]
  · have ha' := lt_of_not_ge ha
    by_cases hb : b ≤ ε
    · simp only [seedEndWindow, ha, ite_false, min_eq_left ha'.le, min_eq_left hb,
        not_lt_of_ge hb, and_false, sub_self, zero_mul]
    · simp only [seedEndWindow, ha, ite_false, min_eq_left ha'.le, min_eq_right (le_of_not_ge hb),
        ha', lt_of_not_ge hb, and_self, ite_true, zero_mul, sub_zero]
      ring

/-- The error of the finite cut sum is bounded by the existing crossing
remainder for the continuous path `u ↦ B(max u ε)`. -/
theorem abs_seedEndWindow_error_le {c B : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hc : ∀ u ω, |c u ω| ≤ C) {ε t : ℝ≥0} (hεt : ε ≤ t) (n : ℕ) (ω : Ω) :
    |riemannSum B c n t ω - riemannSum B c n ε ω - riemannSum B (seedEndWindow ε c) n t ω| ≤
      C * seedCrossingRemainder (fun u ω => B (max u ε) ω)
        (fun _ _ => 0) (fun _ _ => 0) B ε t ω n := by
  let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
  have hq (k : ℕ) : min (grid n k) ε = min (p k) ε := by
    dsimp only [p]
    rw [min_assoc, min_eq_right hεt]
  rw [seed_riemannSum_clamped, seed_riemannSum_clamped, seed_riemannSum_clamped,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp only [hq]
  calc _ ≤ ∑ k ∈ Finset.range (cells n),
      |c (p k) ω * (B (p (k + 1)) ω - B (p k) ω) -
        c (min (p k) ε) ω * (B (min (p (k + 1)) ε) ω - B (min (p k) ε) ω) -
        seedEndWindow ε c (p k) ω * (B (p (k + 1)) ω - B (p k) ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ C * seedCrossingRemainder (fun u ω => B (max u ε) ω)
        (fun _ _ => 0) (fun _ _ => 0) B ε t ω n := by
      rw [seedCrossingRemainder, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [seedEndWindow_cell c B ε (p k) (p (k + 1)) (hp (Nat.le_succ k)) ω]
      split_ifs with hh
      · dsimp only [p] at hh ⊢
        simp only [Ito.itoDefect, max_eq_left hh.2.le, max_eq_right hh.1.le,
          zero_mul, mul_zero, sub_zero, abs_mul]
        exact mul_le_mul_of_nonneg_right (hc _ _) (abs_nonneg _)
      · simp only [abs_zero, mul_zero]
        exact le_rfl

/-- The original-clock cut error tends to zero pathwise. -/
theorem tendsto_seedEndWindow_error {c B : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hc : ∀ u ω, |c u ω| ≤ C) (hB : ∀ ω, Continuous (B · ω))
    {ε t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) :
    Tendsto (fun n => riemannSum B c n t ω - riemannSum B c n ε ω -
      riemannSum B (seedEndWindow ε c) n t ω) atTop (𝓝 0) := by
  have hY : Continuous (fun u => B (max u ε) ω) :=
    (hB ω).comp (continuous_id.max continuous_const)
  have hh := (tendsto_seedCrossingRemainder (c₁ := fun _ _ => 0) (c₂ := fun _ _ => 0) ε t ω hY (hB ω) (C := 0) le_rfl
    (fun _ _ => by simp only [abs_zero, le_refl])
    (fun _ _ => by simp only [abs_zero, le_refl])).const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun n => ?_) (by simpa only [mul_zero] using hh)
  simpa only [Real.norm_eq_abs] using abs_seedEndWindow_error_le hc hεt n ω

end InteractingSLE.ZhanGT4
