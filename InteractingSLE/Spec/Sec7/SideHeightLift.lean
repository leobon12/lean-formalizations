/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Restart.ChartMeasLift
import InteractingSLE.Spec.Sec2.MartingaleLaurent
import InteractingSLE.WangWu.TraceGlue

/-!
# The frozen derivative lift is the canonical one

Packet PROVE-SIDEHEIGHT. The frozen coupling mean uses `arg f_t′ = Im logDerivFwd` (the branch of `log f_t′`
vanishing at `t = 0`); the chart lemmas of Lemma 7.8 (`PairData.IsMeasGood.tendsto_lift_sub_of_transition`,
Aux. lemma 57) use the canonical derivative lift `IsCanonicalDerivLog` (a continuous log of `g′` on `ℍ \ K` equal to
the principal `Log g′` high up). They agree (PROVE-LEMMA76's missing bridge "`logDerivFwd ↔ IsCanonicalDerivLog`"):

* **`isCanonicalDerivLog_fwdMap`**: for a continuous driver with `W₀ = 0`, `logDerivFwd W t` is the canonical lift of
  the mapping-out function `g_t = f_t + W_t` of `K_t` (`log f_t′(z) = −2t/z² + O(|z|⁻³)`, so `|Im logDerivFwd| < π`
  high up and `Log(exp L) = L` there);
* **`isCanonicalDerivLog_fwdMap_rpath`**: the same at times `t < ζ` for a driver continuous before `ζ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H fwdMap fwdHull logDerivFwd)

/-- **`logDerivFwd` is the canonical derivative lift of the Loewner mapping-out function.** -/
theorem isCanonicalDerivLog_fwdMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Restart.IsCanonicalDerivLog (fwdHull W t) (fun z => fwdMap W t z + W t) (logDerivFwd W t) := by
  have hD := isDerivLog_fwdMap hW ht
  have hderiv : ∀ z, deriv (fun z => fwdMap W t z + W t) z = deriv (fwdMap W t) z := fun z =>
    deriv_add_const _
  refine ⟨⟨hD.1, fun z hz => by rw [hderiv, hD.2 z hz]⟩, ?_⟩
  -- a bound for the driver and for the hull
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hW.continuousOn
  have hK' : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ K := fun r hr => by simpa [Real.norm_eq_abs] using hK r hr
  obtain ⟨R, hR⟩ := (WangWu.TraceGlue.isBounded_fwdHull hW (t := t)).subset_closedBall 0
  set D : ℝ := 24 * K + 8 * Real.sqrt t with hD_def
  set Y₀ : ℝ := max (max (2 * D) R) (max 1 ((2 * t + 24 * D * t) / Real.pi)) with hY₀
  refine ⟨Y₀ + 1, fun w hw => ?_⟩
  have hY1 : 1 ≤ Y₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hnorm : Y₀ + 1 < ‖w‖ := hw.trans_le (abs_im_le_norm w |>.trans' (le_abs_self _))
  have hwH : w ∈ H := show 0 < w.im by linarith
  have hwK : w ∉ fwdHull W t := fun h => by
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    have : R ≤ Y₀ := (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hw2D : 2 * D ≤ ‖w‖ := by
    have : 2 * D ≤ Y₀ := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hb := MartChar.norm_logDerivFwd_add_le hW hW0 ht hK' ⟨hwH, hwK⟩ hw2D
  have hw1 : 1 ≤ ‖w‖ := by linarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK' 0 ⟨le_rfl, ht⟩)
  have hD0 : 0 ≤ D := by positivity
  -- `‖L‖ ≤ (2t + 24Dt)/‖w‖ < π`
  have hL : ‖logDerivFwd W t w‖ < Real.pi := by
    have h1 : ‖logDerivFwd W t w‖ ≤ ‖(2 * t / w ^ 2 : ℂ)‖ + 24 * D * t / ‖w‖ ^ 3 := by
      have := norm_sub_le (logDerivFwd W t w + 2 * t / w ^ 2) (2 * t / w ^ 2)
      rw [add_sub_cancel_right] at this
      linarith
    have h2 : ‖(2 * t / w ^ 2 : ℂ)‖ = 2 * t / ‖w‖ ^ 2 := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hw2 : ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have hw3 : ‖w‖ ≤ ‖w‖ ^ 3 := by nlinarith
    have hpos : 0 < ‖w‖ := by linarith
    have h3 : 2 * t / ‖w‖ ^ 2 ≤ 2 * t / ‖w‖ :=
      div_le_div_of_nonneg_left (by positivity) hpos hw2
    have h4 : 24 * D * t / ‖w‖ ^ 3 ≤ 24 * D * t / ‖w‖ :=
      div_le_div_of_nonneg_left (by positivity) hpos hw3
    have h5 : (2 * t + 24 * D * t) / ‖w‖ < Real.pi := by
      rw [div_lt_iff₀ hpos]
      have hle : (2 * t + 24 * D * t) / Real.pi ≤ Y₀ :=
        (le_max_right _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ Real.pi_pos] at hle
      nlinarith [Real.pi_pos]
    rw [add_div] at h5
    linarith
  have him : |(logDerivFwd W t w).im| < Real.pi := (abs_im_le_norm _).trans_lt hL
  rw [hderiv, ← hD.2 w ⟨hwH, hwK⟩, Complex.log_exp (by linarith [neg_abs_le (logDerivFwd W t w).im])
    (by linarith [le_abs_self (logDerivFwd W t w).im])]

/-- **The canonical lift at times before the lifetime** of a driver continuous before `ζ` with `W₀ = 0`. -/
theorem isCanonicalDerivLog_fwdMap_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    Restart.IsCanonicalDerivLog (fwdHull (fun s : ℝ => w s.toNNReal) t)
      (fun z => fwdMap (fun s : ℝ => w s.toNNReal) t z + w t) (logDerivFwd (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨t₂, htt₂, ht₂⟩ := exists_real_btwn_of_lt ht
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have heq : EqOn (fun s : ℝ => w s.toNNReal) (frozenDrive w t₂) (Icc 0 t) := fun r hr =>
    (frozenDrive_eq ⟨hr.1, hr.2.trans htt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (frozenDrive w t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂ fun r hr => (frozenDrive_eq hr).symm
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) t = fwdMap (frozenDrive w t₂) t :=
    funext fun z => Ito.fwdMap_congr_of_eqOn_of_le heq le_rfl
  have hL : logDerivFwd (fun s : ℝ => w s.toNNReal) t = logDerivFwd (frozenDrive w t₂) t :=
    funext fun z => Ito.logDerivFwd_congr_of_eqOn heq t.coe_nonneg le_rfl
  have hWt : w t = frozenDrive w t₂ t := by rw [frozenDrive_eq ⟨t.coe_nonneg, htt₂.le⟩, Real.toNNReal_coe]
  rw [hK, hM, hL, hWt]
  exact isCanonicalDerivLog_fwdMap hW hW0 t.coe_nonneg

end SideHeight

end Sec7

end InteractingSLE
