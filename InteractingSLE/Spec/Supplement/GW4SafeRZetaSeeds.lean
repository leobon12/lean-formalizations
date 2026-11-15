/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.MartingaleFinalImage
import QuantumZipper.Proofs.RS.TraceShift

/-!
# GW4: recent increments have small exposed seed intervals

Continuity at the terminal time and the existing deterministic force-image
bound put both seed images of every sufficiently recent increment in any
prescribed neighborhood of zero. The reference starting time may vary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar.RealFlow

/-- Uniformly over starting times sufficiently close to t, the two seed
images of the increment ending at t lie in `(-r,r)`. -/
theorem exists_recent_restart_seeds {W : ℝ → ℝ} (hW : Continuous W)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < t ∧ ∀ s ∈ Ioo (t - δ) t,
      -r < -rightImg (fun u => -shiftDrive W s u) 0 (t - s) - shiftDrive W s (t - s) ∧
      rightImg (shiftDrive W s) 0 (t - s) - shiftDrive W s (t - s) < r := by
  let ε := r / 8
  have hε : 0 < ε := div_pos hr (by norm_num)
  obtain ⟨d, hd, hNear⟩ := Metric.continuousAt_iff.1 (hW.continuousAt (x := t)) (ε / 2)
    (half_pos hε)
  let δ := min (t / 2) (min d (ε ^ 2))
  have hδ : 0 < δ := lt_min (half_pos ht) (lt_min hd (sq_pos_of_pos hε))
  refine ⟨δ, hδ, (min_le_left _ _).trans_lt (half_lt_self ht), ?_⟩
  intro s hs
  have hΔ : 0 ≤ t - s := sub_nonneg.2 hs.2.le
  have hΔd : t - s < d :=
    (show t - s < δ by linarith only [hs.1]).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hΔε : t - s < ε ^ 2 :=
    (show t - s < δ by linarith only [hs.1]).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hSqrt : Real.sqrt (t - s) < ε := by
    nlinarith only [Real.sq_sqrt hΔ, Real.sqrt_nonneg (t - s), hΔε, hε]
  have hClose : ∀ u ∈ Icc s t, |W u - W t| < ε / 2 := by
    intro u hu
    apply hNear
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hu.2)]
    linarith only [hu.1, hΔd]
  have hOsc : ∀ u ∈ Icc 0 (t - s), |shiftDrive W s u| ≤ ε := by
    intro u hu
    have h1 := hClose (s + u) ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
    have h2 := hClose s ⟨le_rfl, hs.2.le⟩
    change |W (s + u) - W s| ≤ ε
    have htri := abs_add_le (W (s + u) - W t) (W t - W s)
    rw [sub_add_sub_cancel, abs_sub_comm (W t) (W s)] at htri
    linarith only [h1, h2, htri]
  have hBound : ∀ V : ℝ → ℝ, Continuous V → V 0 = 0 →
      (∀ u ∈ Icc 0 (t - s), |V u| ≤ ε) →
      rightImg V 0 (t - s) - V (t - s) < r := by
    intro V hV hV0 hB
    have hImg := rightImg_le_add hV (x := 0) (s := 0) (t := t - s)
      (M := ε) le_rfl hΔ hε
      (by rw [rightImg_zero hV hV0 le_rfl]; exact hε.le)
      (fun u hu => (le_abs_self _).trans (hB u hu))
    have hLast := (neg_le_neg (hB (t - s) ⟨hΔ, le_rfl⟩)).trans (neg_abs_le (V (t - s)))
    simp only [sub_zero] at hImg
    dsimp only [ε] at hε hSqrt hImg hLast
    linarith only [hImg, hSqrt, hLast, hr]
  have hV : Continuous (shiftDrive W s) :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W s 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  refine ⟨?_, hBound _ hV hV0 hOsc⟩
  have hNeg := hBound (fun u => -shiftDrive W s u) hV.neg
    (by rw [hV0, neg_zero]) (fun u hu => by rw [abs_neg]; exact hOsc u hu)
  linarith only [hNeg]

end InteractingSLE.Theorem14.GW4Fix
