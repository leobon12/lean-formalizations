/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishEnumerate

/-!
# Seed limits and individual force jumps

Packet PROVE-CFCHART2. The formulas needed to recover the weights from strictly
ordered force data, using the general one-sided limits and coincident-weight identity.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace InteractingSLE.Sec5.CfFinish

open PiecewiseConstantBoundaryData

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
  (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ)

/-- The left seed limit reads only the left seed weight under strict ordering. -/
theorem leftLim_force_zero (hL : StrictAnti vL) (hL0 : vL 0 = 0) :
    leftLim (forceBoundaryData κ ρL ρR vL vR) 0 = -sleLambda κ * (1 + ρL 0) := by
  classical
  have hf : Finset.univ.filter (fun i => 0 ≤ vL i) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      by_contra hn
      have hl := hL (Fin.pos_iff_ne_zero.2 hn)
      rw [hL0] at hl
      exact not_lt_of_ge hi hl
    · rintro rfl
      exact hL0.ge
  rw [leftLim_force_of_nonpos κ ρL ρR vL vR le_rfl, hf, Finset.sum_singleton]

/-- The right seed limit reads only the right seed weight under strict ordering. -/
theorem rightLim_force_zero (hR : StrictMono vR) (hR0 : vR 0 = 0) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) 0 = sleLambda κ * (1 + ρR 0) := by
  classical
  have hf : Finset.univ.filter (fun j => vR j ≤ 0) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hn
      have hr := hR (Fin.pos_iff_ne_zero.2 hn)
      rw [hR0] at hr
      exact not_lt_of_ge hj hr
    · rintro rfl
      exact hR0.le
  rw [rightLim_force_of_nonneg κ ρL ρR vL vR le_rfl, hf, Finset.sum_singleton]

/-- A strictly separated negative mark has jump exactly `λ` times its weight. -/
theorem jump_force_left_succ (hL : StrictAnti vL) (hL0 : vL 0 = 0) (i : Fin nL) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) (vL i.succ) -
      leftLim (forceBoundaryData κ ρL ρR vL vR) (vL i.succ) = sleLambda κ * ρL i.succ := by
  classical
  have hi : vL i.succ < 0 := by
    rw [← hL0]
    exact hL (show (0 : Fin (nL + 1)) < i.succ from Nat.zero_lt_succ _)
  rw [jump_force_of_neg κ ρL ρR vL vR hi]
  simp only [hL.injective.eq_iff, Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton]

/-- A strictly separated positive mark has jump exactly `λ` times its weight. -/
theorem jump_force_right_succ (hR : StrictMono vR) (hR0 : vR 0 = 0) (j : Fin nR) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) (vR j.succ) -
      leftLim (forceBoundaryData κ ρL ρR vL vR) (vR j.succ) = sleLambda κ * ρR j.succ := by
  classical
  have hj : 0 < vR j.succ := by
    rw [← hR0]
    exact hR (show (0 : Fin (nR + 1)) < j.succ from Nat.zero_lt_succ _)
  rw [jump_force_of_pos κ ρL ρR vL vR hj]
  simp only [hR.injective.eq_iff, Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton]

end InteractingSLE.Sec5.CfFinish
