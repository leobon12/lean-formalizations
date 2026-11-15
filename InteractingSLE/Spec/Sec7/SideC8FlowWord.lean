/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Collar
import InteractingSLE.Spec.Restart.FCAux79MeanFlow

/-!
# The exact word at a surviving incoming real side

PROVE-SIDE-COLLAR2. Reuse Aux. 79's real-flow word preservation. Both
seed images bound the exposed interval, so a surviving initial real point
has zero phase-window contribution for every phase value.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open InteractingSLE.MartChar.RealFlow

namespace InteractingSLE.Sec7.PocketStopSide

/-- At a surviving initial real point the current force word is the
initial word, with no phase contribution from the exposed seed interval. -/
theorem force_word_of_surviving_real {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t x : ℝ} (ht : 0 ≤ t) {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x t a)
    {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (zL : Fin nL) (zR : Fin nR)
    (hL0 : xL zL = 0) (hR0 : xR zR = 0)
    (hx : x ∉ forceJumpSet xL xR)
    (hy : (a t).re ∉ forceJumpSet
      (fun i => -rightImg (fun s => -W s) (-xL i) t - W t)
      (fun j => rightImg W (xR j) t - W t)) (δ : ℝ) :
    forceBoundaryData κ ρL ρR
      (fun i => -rightImg (fun s => -W s) (-xL i) t - W t)
      (fun j => rightImg W (xR j) t - W t) (a t).re +
      δ * (Ioo (-rightImg (fun s => -W s) (-xL zL) t - W t)
        (rightImg W (xR zR) t - W t)).indicator 1 (a t).re =
      forceBoundaryData κ ρL ρR xL xR x := by
  have hxL : ∀ i, xL i ≠ x := fun i h => hx (Or.inr (Or.inl ⟨i, h⟩))
  have hxR : ∀ j, xR j ≠ x := fun j h => hx (Or.inr (Or.inr ⟨j, h⟩))
  rcases Restart.FCAux79.isForwardSol_real_cases hW hW0 ht ha with
    ⟨hx0, hAlive, hValue⟩ | ⟨hx0, hAlive, hValue⟩
  · have hRe : (a t).re = gImg W x t - W t := by rw [hValue, Complex.ofReal_re]
    have hSeed : rightImg W (xR zR) t ≤ gImg W x t := by
      rw [hR0]
      exact rightImg_le_gImg hW ht hx0 hAlive
    have hOutside : (a t).re ∉ Ioo
        (-rightImg (fun s => -W s) (-xL zL) t - W t)
        (rightImg W (xR zR) t - W t) := by
      rw [hRe]
      exact fun h => (not_lt_of_ge (sub_le_sub_right hSeed (W t))) h.2
    rw [indicator_of_notMem hOutside, mul_zero, add_zero, hRe]
    exact Restart.FCAux79.forceBoundaryData_flow_right ρL ρR hW ht hx0 hAlive hxR
  · have hRe : (a t).re = -gImg (fun s => -W s) (-x) t - W t := by
      rw [hValue, Complex.ofReal_re]
    have hSeed : rightImg (fun s => -W s) (-xL zL) t ≤
        gImg (fun s => -W s) (-x) t := by
      rw [hL0, neg_zero]
      exact rightImg_le_gImg hW.neg ht (neg_pos.2 hx0) hAlive
    have hOutside : (a t).re ∉ Ioo
        (-rightImg (fun s => -W s) (-xL zL) t - W t)
        (rightImg W (xR zR) t - W t) := by
      rw [hRe]
      exact fun h => (not_lt_of_ge (sub_le_sub_right (neg_le_neg hSeed) (W t))) h.1
    rw [indicator_of_notMem hOutside, mul_zero, add_zero, hRe]
    have hyL : ∀ i, -gImg (fun s => -W s) (-x) t - W t ≠
        -rightImg (fun s => -W s) (-xL i) t - W t := by
      intro i h
      apply hy
      exact Or.inr (Or.inl ⟨i, by rw [hRe]; exact h.symm⟩)
    simpa only [neg_neg] using Restart.FCAux79.forceBoundaryData_flow_left ρL ρR hW ht
      (neg_pos.2 hx0) hAlive (fun i h => hxL i (neg_injective h)) hyL

end InteractingSLE.Sec7.PocketStopSide
