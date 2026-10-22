import HigherDimLQGMetric.Limits.WeylLimit
import HigherDimLQGMetric.Trunc.Basic

/-! Bounded continuous perturbations of the truncated convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6c_truncMollify_ofCont {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (f : C(Rd d, ℝ)) (z : Rd d) :
    truncMollify κ ε (ofCont f) z =
      ∫ w : Rd d, convKernelEps κ ε (z - w) *
        radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w) * f w := by
  rw [truncMollify, ofCont_apply]
  apply integral_congr_ae
  filter_upwards with w
  rw [l2c_truncTest_apply hd hκ hε]

theorem l6c_truncMollify_addFun {d : ℕ}
    (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d)
    (f : C(Rd d, ℝ)) (z : Rd d) :
    truncMollify κ ε (addFun h f) z =
      truncMollify κ ε h z + truncMollify κ ε (ofCont f) z := by
  rfl

/-- Change variables in a convolution with an extra displacement weight. -/
theorem l6c_weighted_conv_change_variables {d : ℕ}
    (κ : Rd d → ℝ) (f : C(Rd d, ℝ)) (q : Rd d → ℝ)
    {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    (∫ w : Rd d, convKernelEps κ ε (z - w) * q (z - w) * f w) =
      ∫ u : Rd d, convKernel κ u * q (ε • u) * f (z - ε • u) := by
  let F : Rd d → ℝ := fun w =>
    convKernelEps κ ε (z - w) * q (z - w) * f w
  have h := integral_comp_affinePt_abs F (-ε) z
  have hp : |(-ε : ℝ)| ^ d = ε ^ d := by rw [abs_neg, abs_of_pos hε]
  rw [hp] at h
  have heval (u : Rd d) : F ((-ε) • u + z) =
      ε ^ (-(d : ℝ)) * (convKernel κ u * q (ε • u) * f (z - ε • u)) := by
    dsimp [F, convKernelEps]
    have he : z - ((-ε) • u + z) = ε • u := by
      rw [neg_smul]
      abel_nf
    rw [he]
    have he2 : ε⁻¹ • (ε • u) = u := by
      rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [he2]
    rw [neg_smul]
    have he3 : -(ε • u) + z = z - ε • u := by abel_nf
    rw [he3]
    ring
  simp_rw [heval] at h
  rw [integral_const_mul] at h
  have hpow' : ε ^ (-(d : ℝ)) = (ε ^ d)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
  rw [hpow'] at h
  have hn : ε ^ d ≠ 0 := pow_ne_zero _ hε.ne'
  exact (mul_left_cancel₀ (inv_ne_zero hn)) (by
    simpa only [inv_mul_cancel₀ hn, one_mul] using h.symm)

/-- On each fixed displacement the truncation cutoff is eventually one. -/
theorem l6c_truncBump_eventually_one {d : ℕ}
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) (u : Rd d) :
    ∀ᶠ n in atTop,
      radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n))
        (εs n • u) = 1 := by
  have hroot : Tendsto (fun n => Real.sqrt (εs n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hεt
  have ht : Tendsto (fun n => 2 * Real.sqrt (εs n) * ‖u‖) atTop (𝓝 0) := by
    simpa using (hroot.const_mul 2).mul_const ‖u‖
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
  have hs : 0 < Real.sqrt (εs n) := Real.sqrt_pos.2 (hεs n)
  have hnorm : ‖εs n • u‖ ≤ Real.sqrt (εs n) / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hεs n)]
    have hsq : Real.sqrt (εs n) ^ 2 = εs n := Real.sq_sqrt (hεs n).le
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hn.le)]
  exact l2c_radBump_eq_one (by positivity) (by linarith) hnorm

/-- The L¹ mass removed by truncation tends to zero along any positive
cutoff sequence. -/
theorem l6c_trunc_kernel_error_tendsto {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u : Rd d, |convKernel κ u| *
      |1 - radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n))
        (εs n • u)|) atTop (𝓝 0) := by
  have hK : Integrable (fun u : Rd d => |convKernel κ u|) :=
    (integrable_convKernel hd hκ).abs
  let F : ℕ → Rd d → ℝ := fun n u => |convKernel κ u| *
    |1 - radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n)) (εs n • u)|
  have hm (n : ℕ) : AEStronglyMeasurable (F n) := by
    have hb : Continuous (fun u : Rd d =>
        radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n)) (εs n • u)) :=
      (contDiff_radBump (by have hs := Real.sqrt_pos.2 (hεs n); positivity) (by
        have hs := Real.sqrt_pos.2 (hεs n)
        linarith)).continuous.comp (by fun_prop)
    exact ((convKernel_contDiff (by omega) hκ).continuous.abs.mul
      (continuous_const.sub hb).abs).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ u : Rd d ∂volume,
      ‖F n u‖ ≤ |convKernel κ u| := by
    filter_upwards with u
    have hb := l2c_radBump_mem_Icc
      (Real.sqrt (εs n) / 2) (Real.sqrt (εs n)) (εs n • u)
    have hb0 : 0 ≤ F n u := by
      dsimp [F]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hb0]
    dsimp [F]
    have hunit : |1 - radBump (Real.sqrt (εs n) / 2)
      (Real.sqrt (εs n)) (εs n • u)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hb.2])]
      linarith [hb.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hunit
  have hpoint : ∀ᵐ u : Rd d ∂volume,
      Tendsto (fun n => F n u) atTop (𝓝 0) := by
    filter_upwards with u
    have he : (fun n => F n u) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [l6c_truncBump_eventually_one hεs hεt u] with n hn
      simp [F, hn]
    exact tendsto_const_nhds.congr' he.symm
  simpa only [F, integral_zero] using
    tendsto_integral_of_dominated_convergence
      (fun u : Rd d => |convKernel κ u|) hm hK hbound hpoint

/-- Uniform-in-space error bound for truncating a bounded continuous field. -/
theorem l6c_trunc_ofCont_error_bound {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (f : C(Rd d, ℝ))
    (M : ℝ) (hM : ∀ z, |f z| ≤ M) (z : Rd d) :
    |convMollify κ ε (ofCont f) z - truncMollify κ ε (ofCont f) z| ≤
      M * (∫ u : Rd d, |convKernel κ u| *
        |1 - radBump (Real.sqrt ε / 2) (Real.sqrt ε) (ε • u)|) := by
  have hK : Integrable (convKernel κ) := integrable_convKernel hd hκ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let W : Rd d → ℝ := fun u =>
    radBump (Real.sqrt ε / 2) (Real.sqrt ε) (ε • u)
  have hWc : Continuous W :=
    (contDiff_radBump (by have hs := Real.sqrt_pos.2 hε; positivity) (by
      have hs := Real.sqrt_pos.2 hε
      linarith)).continuous.comp (by fun_prop)
  have hW (u : Rd d) : W u ∈ Icc (0 : ℝ) 1 :=
    l2c_radBump_mem_Icc _ _ _
  let F : Rd d → ℝ := fun u => convKernel κ u * f (z - ε • u)
  let G : Rd d → ℝ := fun u => convKernel κ u * W u * f (z - ε • u)
  let B : Rd d → ℝ := fun u => |convKernel κ u| * |1 - W u|
  have hFb : Integrable F := by
    apply Integrable.mono' (hK.abs.const_mul M)
    · exact (hK.aestronglyMeasurable.mul
        (f.continuous.comp (by fun_prop : Continuous
          (fun u : Rd d => z - ε • u))).aestronglyMeasurable)
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hM _) (abs_nonneg (convKernel κ u))
  have hGb : Integrable G := by
    apply Integrable.mono' (hK.abs.const_mul M)
    · exact ((hK.aestronglyMeasurable.mul hWc.aestronglyMeasurable).mul
        (f.continuous.comp (by fun_prop : Continuous
          (fun u : Rd d => z - ε • u))).aestronglyMeasurable)
    · filter_upwards with u
      have hWu := hW u
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hWu.1]
      have hprod : W u * |f (z - ε • u)| ≤ M :=
        (mul_le_mul_of_nonneg_left (hM _) hWu.1).trans
          (mul_le_of_le_one_left hM0 hWu.2)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hprod (abs_nonneg (convKernel κ u))
  have hBb : Integrable B := by
    apply Integrable.mono' hK.abs
    · exact ((convKernel_contDiff (by omega) hκ).continuous.abs.mul
        (continuous_const.sub hWc).abs).aestronglyMeasurable
    · filter_upwards with u
      have hu := hW u
      have hunit : |1 - W u| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [hu.2])]
        linarith [hu.1]
      have hB0 : 0 ≤ B u := by dsimp [B]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hB0]
      exact mul_le_of_le_one_right (abs_nonneg _) hunit
  have hBf : Integrable (fun u => M * B u) := hBb.const_mul M
  have hpoint (u : Rd d) : ‖F u - G u‖ ≤ M * B u := by
    dsimp [F, G, B]
    have he : convKernel κ u * f (z - ε • u) -
        convKernel κ u * W u * f (z - ε • u) =
        convKernel κ u * (1 - W u) * f (z - ε • u) := by ring
    rw [he, abs_mul, abs_mul]
    have hu := mul_le_mul_of_nonneg_left (hM (z - ε • u)) (mul_nonneg
      (abs_nonneg (convKernel κ u)) (abs_nonneg (1 - W u)))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hu
  have hbound := norm_integral_le_of_norm_le hBf
    (Filter.Eventually.of_forall hpoint)
  rw [Real.norm_eq_abs, integral_const_mul] at hbound
  have heq : convMollify κ ε (ofCont f) z - truncMollify κ ε (ofCont f) z =
      ∫ u : Rd d, F u - G u := by
    rw [l2b_convMollify_ofCont hd hκ hε f M hM z,
      l6c_conv_ofCont_change_variables κ f hε z,
      l6c_truncMollify_ofCont hd κ hκ hε f z,
      l6c_weighted_conv_change_variables κ f
        (radBump (Real.sqrt ε / 2) (Real.sqrt ε)) hε z]
    change (∫ u : Rd d, F u) - ∫ u : Rd d, G u = _
    rw [integral_sub hFb hGb]
  rw [heq]
  exact hbound

/-- The truncated mollifications of any uniformly bounded, locally uniformly
convergent perturbation sequence have the same local uniform limit. -/
theorem l6c_tendstoUniformlyOn_truncMollify_seq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {fn : ℕ → C(Rd d, ℝ)} {f : C(Rd d, ℝ)} {M : ℝ}
    (hfnM : ∀ n z, |fn n z| ≤ M) (hfM : ∀ z, |f z| ≤ M)
    (hconv : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 R))
    {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n z => truncMollify κ (εs n) (ofCont (fn n)) z) ⇑f atTop
      (closedBall (0 : Rd d) R) := by
  have hfull := l6c_tendstoUniformlyOn_convMollify_seq hd κ hκ
    hεs hεt hfnM hfM hconv hR
  have herr := l6c_trunc_kernel_error_tendsto hd κ hκ hεs hεt
  rw [Metric.tendstoUniformlyOn_iff] at hfull ⊢
  intro η hη
  have he1 := hfull (η / 2) (by positivity)
  have he2 := herr.eventually (gt_mem_nhds (show (0 : ℝ) < η / (2 * (M + 1)) by
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
    positivity))
  filter_upwards [he1, he2] with n hn ht z hz
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hb := l6c_trunc_ofCont_error_bound hd κ hκ (hεs n) (fn n) M
    (hfnM n) z
  have hnz := hn z hz
  rw [Real.dist_eq] at hnz ⊢
  have htri : |f z - truncMollify κ (εs n) (ofCont (fn n)) z| ≤
      |f z - convMollify κ (εs n) (ofCont (fn n)) z| +
      |convMollify κ (εs n) (ofCont (fn n)) z -
        truncMollify κ (εs n) (ofCont (fn n)) z| := abs_sub_le _ _ _
  have hmass : 0 ≤ ∫ u : Rd d, |convKernel κ u| *
      |1 - radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n))
        (εs n • u)| := integral_nonneg fun _ => by positivity
  have hsmall : M * (∫ u : Rd d, |convKernel κ u| *
      |1 - radBump (Real.sqrt (εs n) / 2) (Real.sqrt (εs n))
        (εs n • u)|) < η / 2 := by
    have hprod := mul_lt_mul_of_pos_left ht (by linarith : 0 < M + 1)
    have hcancel : (M + 1) * (η / (2 * (M + 1))) = η / 2 := by
      field_simp
    rw [hcancel] at hprod
    nlinarith [mul_nonneg hM0 hmass]
  exact lt_of_le_of_lt htri (by linarith)

end HigherDimLQGMetric
