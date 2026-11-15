/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.T26PvStj
import InteractingSLE.Spec.Sec2.T2426Cert
import InteractingSLE.Foundations.Loewner.Capacity
import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral

/-!
# Theorem 2.6, the provider, part 3: the one-point Loewner coordinates as time integrals

Packet PROVE-T26-PROVIDER. Specification, proof of Theorem 2.6 (`source/spec/p001-048.md` L977–L984): along a
continuous driver `W`, for `z` not swallowed by time `t`,

* `fwdMap_add_eq_add_integral`: `g_t(z) = f_t(z) + W_t = z + ∫₀ᵗ 2/f_s(z) ds`;
* `im_logDerivFwd_eq_integral`: `Im log f_t'(z) = ∫₀ᵗ Im(−2/f_s(z)²) ds`;
* `log_conformalRadius_eq_integral`: "the ordinary Loewner equation, independently of the choice of driving function,
  gives `−d log crad(ℍ ∖ K_t, z) = 4 (Im 1/f_t(z))² dt`", integrated:
  `log (2 Im z / (2 Im f_t(z)/|f_t'(z)|)) = ∫₀ᵗ 4 (Im f_s(z))²/|f_s(z)|⁴ ds`;
* `setIntegral_clk_eq_intervalIntegral`: an integral against the identity clock over `(0, t]` is the interval
  integral over `[0, t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T26Pv

/-- An integral against the identity clock over `(0, t]` is the interval integral over `[0, t]`. -/
theorem setIntegral_clk_eq_intervalIntegral (g : ℝ≥0 → ℝ) (t : ℝ≥0) :
    ∫ u in Ioc 0 t, g u ∂clk.measure = ∫ x in (0 : ℝ)..t, g x.toNNReal := by
  rw [show (∫ u in Ioc 0 t, g u ∂clk.measure) = ∫ u, g u ∂(clk.measure.restrict (Ioc 0 t)) from rfl,
    Ito.GenCont.clockPath_id_restrict]
  exact MathFin.ItoIntegralProcessGeneral.timeMeasure_Ioc_eq_interval t

/-- The same for complex-valued integrands. -/
theorem setIntegral_clk_eq_intervalIntegral_complex (g : ℝ≥0 → ℂ) (t : ℝ≥0) :
    ∫ u in Ioc 0 t, g u ∂clk.measure = ∫ x in (0 : ℝ)..t, g x.toNNReal := by
  rw [show (∫ u in Ioc 0 t, g u ∂clk.measure) = ∫ u, g u ∂(clk.measure.restrict (Ioc 0 t)) from rfl,
    Ito.GenCont.clockPath_id_restrict]
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc 0 t = Set.Ioc 0 (t : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨mod_cast hy1, mod_cast hy2⟩
    · rintro ⟨hx1, hx2⟩
      have hy : (Real.toNNReal x : ℝ) = x := Real.coe_toNNReal x hx1.le
      exact ⟨Real.toNNReal x, ⟨Real.toNNReal_pos.2 hx1, NNReal.coe_le_coe.1 (hy.trans_le hx2)⟩, hy⟩
  have hmap : Measure.map ((↑) : ℝ≥0 → ℝ) (MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 t))
      = volume.restrict (((↑) : ℝ≥0 → ℝ) '' Set.Ioc 0 t) := by
    rw [MathFin.ItoIntegralL2.timeMeasure, MeasurableEmbedding.restrict_comap MathFin.ItoIntegralL2.measurableEmbedding_nnrealCoe,
      MeasurableEmbedding.map_comap MathFin.ItoIntegralL2.measurableEmbedding_nnrealCoe,
      Measure.restrict_restrict MathFin.ItoIntegralL2.measurableEmbedding_nnrealCoe.measurableSet_range,
      Set.inter_eq_right.2 (Set.image_subset_range _ _)]
  calc ∫ s, g s ∂(MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 t))
      = ∫ x, g (Real.toNNReal x) ∂(MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 t)) :=
        integral_congr_ae (.of_forall fun x ↦ by simp only [Real.toNNReal_coe])
    _ = ∫ y, g (Real.toNNReal y) ∂(Measure.map ((↑) : ℝ≥0 → ℝ)
          (MathFin.ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 t))) :=
        (MathFin.ItoIntegralL2.measurableEmbedding_nnrealCoe.integral_map fun y : ℝ ↦ g (Real.toNNReal y)).symm
    _ = ∫ x in Set.Ioc 0 (t : ℝ), g (Real.toNNReal x) := by rw [hmap, himg]
    _ = ∫ x in (0)..(t : ℝ), g (Real.toNNReal x) :=
        (intervalIntegral.integral_of_le (NNReal.coe_nonneg t)).symm

section Loewner

variable {W : ℝ → ℝ} {z : ℂ} {T : ℝ}

open QuantumZipper

/-- **`g_t(z) = z + ∫₀ᵗ 2/f_s(z) ds`**. -/
theorem fwdMap_add_eq_add_integral (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    fwdMap W T z + W T = z + ∫ r in (0 : ℝ)..T, 2 / fwdMap W r z := by
  rw [Ito.fwdMap_eq_sub_add_integral hW hT hz ⟨hT, le_rfl⟩]
  ring

/-- **`Im log f_t'(z) = ∫₀ᵗ Im(−2/f_s(z)²) ds`**. -/
theorem im_logDerivFwd_eq_integral (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    (logDerivFwd W T z).im = ∫ r in (0 : ℝ)..T, ((-2 : ℂ) / fwdMap W r z ^ 2).im := by
  have hint : IntervalIntegrable (fun r => 2 / fwdMap W r z ^ 2) volume 0 T :=
    (Ito.continuousOn_two_div_fwdMap_sq hW hT hz).intervalIntegrable_of_Icc hT
  have h := Complex.imCLM.intervalIntegral_comp_comm hint
  simp only [Complex.imCLM_apply] at h
  rw [logDerivFwd, Complex.neg_im, ← h, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp [neg_div]

/-- **The conformal-radius clock**: `log (2 Im z / (2 Im f_t(z)/|f_t'(z)|)) = ∫₀ᵗ 4 (Im f_s(z))²/|f_s(z)|⁴ ds`. -/
theorem log_conformalRadius_eq_integral (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    Real.log (2 * z.im / (2 * (fwdMap W T z).im / ‖deriv (fwdMap W T) z‖)) =
      ∫ r in (0 : ℝ)..T, 4 * (fwdMap W r z).im ^ 2 / ‖fwdMap W r z‖ ^ 4 := by
  have hsol : ∃ u, IsForwardSol W z T u := Ito.exists_isForwardSol_of_mem hT hz
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => FwdClock.fwdLogCR W s z)
      (-4 * (fwdMap W s z).im ^ 2 / ‖fwdMap W s z‖ ^ 4) (Icc 0 T) s := fun s hs =>
    FwdClock.hasDerivWithinAt_fwdLogCR hW hz.1 hsol hs
  have hcont : ContinuousOn (fun s => -4 * (fwdMap W s z).im ^ 2 / ‖fwdMap W s z‖ ^ 4) (Icc 0 T) := by
    have hf := Ito.continuousOn_fwdMap_time' hW hT hz
    refine ((continuousOn_const.mul ((Complex.continuous_im.comp_continuousOn hf).pow 2)).div
      ((continuous_norm.comp_continuousOn hf).pow 4) fun s hs => ?_)
    exact pow_ne_zero 4 (norm_ne_zero_iff.2 (Ito.fwdMap_ne_zero hW hT hz hs))
  have hftc := Ito.integral_eq_sub_of_hasDerivWithinAt_Icc hderiv hcont hT le_rfl
  have h0 : FwdClock.fwdLogCR W 0 z = Real.log z.im := by
    have hz0 : z ≠ (W 0 : ℂ) := fun h => by
      have := hz.1
      rw [h] at this
      simp [QuantumZipper.H] at this
    simp only [FwdClock.fwdLogCR, logDerivFwd, intervalIntegral.integral_same, neg_zero, Complex.zero_re,
      sub_zero, Certify2426.fwdMap_time_zero W hz0, Complex.sub_im, Complex.ofReal_im]
  have hpos : 0 < (fwdMap W T z).im := Ito.im_fwdMap_pos hW hT hz ⟨hT, le_rfl⟩
  have hzpos : 0 < z.im := hz.1
  rw [show 2 * z.im / (2 * (fwdMap W T z).im / ‖deriv (fwdMap W T) z‖) =
      z.im / ((fwdMap W T z).im / ‖deriv (fwdMap W T) z‖) by
    have hd : ‖deriv (fwdMap W T) z‖ ≠ 0 := by
      intro h0'
      have := InteractingSLE.im_fwdMap_div_norm_deriv_eq_exp hW hT hz
      rw [h0', div_zero] at this
      exact (Real.exp_pos _).ne' this.symm
    field_simp,
    InteractingSLE.im_fwdMap_div_norm_deriv_eq_exp hW hT hz, Real.log_div hzpos.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  have hneg : ∫ r in (0 : ℝ)..T, 4 * (fwdMap W r z).im ^ 2 / ‖fwdMap W r z‖ ^ 4 =
      -∫ r in (0 : ℝ)..T, -4 * (fwdMap W r z).im ^ 2 / ‖fwdMap W r z‖ ^ 4 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  rw [hneg, hftc, h0]
  ring

end Loewner

end InteractingSLE.Sec2.T26Pv
