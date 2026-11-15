/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishJumps

/-!
# The genuine jump sets of a separated nonzero force word

Packet PROVE-CFCHART2. When positions are strictly ordered from their zero seeds and
nonseed weights are nonzero, the genuine jumps are exactly the nonseed positions.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open PiecewiseConstantBoundaryData Cond44Ref

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}

open scoped Classical in
/-- Strictly ordered negative nonseed marks with nonzero weights are exactly the
negative genuine jumps of the force boundary data. -/
theorem left_jumps_force (hκ : 0 < κ) (hL : StrictAnti vL) (hL0 : vL 0 = 0)
    (hρL : ∀ i : Fin nL, ρL i.succ ≠ 0) :
    (jumpSet (forceBoundaryData κ ρL ρR vL vR) (forceJumpFinset vL vR)).filter (· < 0) =
      Finset.univ.image (fun i : Fin nL => vL i.succ) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyJ, hy0⟩ := Finset.mem_filter.1 hy
    have hne := (Finset.mem_filter.1 hyJ).2
    by_contra hn
    have hs : (∑ i ∈ Finset.univ.filter (fun i => vL i = y), ρL i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hei := (Finset.mem_filter.1 hi).2
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [hL0] at hei
        exact False.elim (hy0.ne' hei)
      · exact False.elim (hn (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hei⟩))
    have hj := jump_force_of_neg κ ρL ρR vL vR hy0
    rw [hs, mul_zero, sub_eq_zero] at hj
    exact hne hj.symm
  · intro hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
    have hi0 : vL i.succ < 0 := by
      rw [← hL0]
      exact hL (show (0 : Fin (nL + 1)) < i.succ from Nat.zero_lt_succ _)
    have hf : Finset.univ.filter (fun j => vL j = vL i.succ) = {i.succ} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hL.injective h, fun h => congrArg vL h⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, ?_⟩, hi0⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨i.succ, Finset.mem_univ _, rfl⟩))
    · intro he
      have hj := jump_force_of_neg κ ρL ρR vL vR hi0
      rw [he, sub_self, hf, Finset.sum_singleton] at hj
      exact (mul_ne_zero (Sec4.sleLambda_pos hκ).ne' (hρL i)) hj.symm

open scoped Classical in
/-- Strictly ordered positive nonseed marks with nonzero weights are exactly the
positive genuine jumps of the force boundary data. -/
theorem right_jumps_force (hκ : 0 < κ) (hR : StrictMono vR) (hR0 : vR 0 = 0)
    (hρR : ∀ j : Fin nR, ρR j.succ ≠ 0) :
    (jumpSet (forceBoundaryData κ ρL ρR vL vR) (forceJumpFinset vL vR)).filter (0 < ·) =
      Finset.univ.image (fun j : Fin nR => vR j.succ) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyJ, hy0⟩ := Finset.mem_filter.1 hy
    have hne := (Finset.mem_filter.1 hyJ).2
    by_contra hn
    have hs : (∑ j ∈ Finset.univ.filter (fun j => vR j = y), ρR j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hej := (Finset.mem_filter.1 hj).2
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · rw [hR0] at hej
        exact False.elim (hy0.ne hej)
      · exact False.elim (hn (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hej⟩))
    have hj := jump_force_of_pos κ ρL ρR vL vR hy0
    rw [hs, mul_zero, sub_eq_zero] at hj
    exact hne hj.symm
  · intro hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hy
    have hj0 : 0 < vR j.succ := by
      rw [← hR0]
      exact hR (show (0 : Fin (nR + 1)) < j.succ from Nat.zero_lt_succ _)
    have hf : Finset.univ.filter (fun i => vR i = vR j.succ) = {j.succ} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hR.injective h, fun h => congrArg vR h⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, ?_⟩, hj0⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩))
    · intro he
      have hj := jump_force_of_pos κ ρL ρR vL vR hj0
      rw [he, sub_self, hf, Finset.sum_singleton] at hj
      exact (mul_ne_zero (Sec4.sleLambda_pos hκ).ne' (hρR j)) hj.symm

end InteractingSLE.Sec5.CfFinish
