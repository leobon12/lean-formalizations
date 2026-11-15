/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessLog
import InteractingSLE.Spec.ZhanGT4.DualSeedMeas

/-!
# The original separated-source logarithm in the opposite view

Packet PROVE-ZHAN-GT4-A22. The source derivative in the fused normalizer
is an adapted time integral, with a bound depending only on the protected
source gap and time horizon. No derivative at a physical seed is used.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)

/-- The real logarithm of the separated-source derivative is its
variational integral, including the initial time. -/
theorem log_source_deriv_eq_integral {W : ℝ → ℝ} (hW : Continuous W)
    {p T : ℝ} {q : ℝ → ℂ} (hq : IsForwardSol W (p : ℂ) T q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Real.log (deriv (fwdMap W t) p).re =
      ∫ u in (0 : ℝ)..t, -2 / (fwdMap W u p).re ^ 2 := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hd : ∀ u ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt (fun y => Real.log (deriv (fwdMap W y) p).re)
        (-2 / (fwdMap W u p).re ^ 2) (Icc 0 T) u :=
    fun u hu => OwnData.hasDerivWithinAt_log_source_deriv hW hq (hsub hu)
  have hcont : ContinuousOn (fun u => Real.log (deriv (fwdMap W u) p).re) (Icc 0 t) :=
    fun u hu => ((hd u hu).mono hsub).continuousWithinAt
  have hqcont : ContinuousOn (fun u => (fwdMap W u p).re) (Icc 0 t) := by
    have hc := continuous_re.comp_continuousOn (hq.1.mono hsub)
    exact hc.congr fun u hu => congrArg Complex.re (fwdMap_eq_of_isForwardSol hW hq (hsub hu))
  have hn : ∀ u ∈ Icc (0 : ℝ) t, (fwdMap W u p).re ≠ 0 := fun u hu =>
    re_ne_zero_of_im_eq_zero ((fwdMap_eq_of_isForwardSol hW hq (hsub hu)).symm ▸ (hq.2 u (hsub hu)).1)
      (fwdMap_real_im hW hq (hsub hu))
  have hc : ContinuousOn (fun u => -2 / (fwdMap W u p).re ^ 2) (Icc 0 t) :=
    continuousOn_const.div (hqcont.pow 2) fun u hu => pow_ne_zero 2 (hn u hu)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont
    (fun u hu => ((hd u (Ioo_subset_Icc_self hu)).mono hsub).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
    (hc.intervalIntegrable_of_Icc ht.1)
  have hzero : (deriv (fwdMap W 0) p).re = 1 := by
    obtain ⟨δ, hδ, hl, hv⟩ := exists_aliveDisc_self hq (ht.1.trans ht.2)
    have hd0 := deriv_fwdMap_aliveDisc hW hq hδ hl hv ⟨le_rfl, ht.1.trans ht.2⟩
    simp only [hd0, QuantumZipper.logDerivFwd, intervalIntegral.integral_same, neg_zero,
      Complex.exp_zero, Complex.one_re]
  simpa only [hzero, Real.log_one, sub_zero] using he.symm

/-- A uniform protected source gap bounds the logarithmic derivative on
the entire horizon. The constant is independent of the driving path. -/
theorem abs_log_source_deriv_le {W : ℝ → ℝ} (hW : Continuous W)
    {p T c : ℝ} {q : ℝ → ℂ} (hq : IsForwardSol W (p : ℂ) T q) (hc : 0 < c)
    (hgap : ∀ u ∈ Icc (0 : ℝ) T, c ≤ |(fwdMap W u p).re|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    |Real.log (deriv (fwdMap W t) p).re| ≤ 2 * T / c ^ 2 := by
  rw [log_source_deriv_eq_integral hW hq ht, ← Real.norm_eq_abs]
  have hb : ∀ u ∈ Icc (0 : ℝ) t, ‖-2 / (fwdMap W u p).re ^ 2‖ ≤ 2 / c ^ 2 := by
    intro u hu
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_two, abs_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hc)
      (pow_le_pow_left₀ hc.le (hgap u ⟨hu.1, hu.2.trans ht.2⟩) 2)
  calc ‖∫ u in (0 : ℝ)..t, -2 / (fwdMap W u p).re ^ 2‖ ≤ (2 / c ^ 2) * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun u hu => hb u (uIoc_subset_uIcc hu |> (uIcc_of_le ht.1 ▸ ·)))
    _ ≤ (2 / c ^ 2) * T := by
      rw [sub_zero, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ = 2 * T / c ^ 2 := by ring

/-- Adapted source and driver values make the actual logarithmic source
derivative measurable on a protected event, via its integral formula. -/
theorem measurable_log_source_deriv {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω → ℝ → ℝ} {V : Ω → ℝ → ℝ} {G : Set Ω} {T : Ω → ℝ} {p t : ℝ}
    (hG : MeasurableSet G) (ht : 0 ≤ t)
    (hW : ∀ ω ∈ G, Continuous (W ω)) (hT : ∀ ω ∈ G, t ≤ T ω)
    (hq : ∀ ω ∈ G, ∃ q, IsForwardSol (W ω) (p : ℂ) (T ω) q)
    (hV : ∀ ω ∈ G, ∀ u ∈ Icc (0 : ℝ) t, V ω u = (fwdMap (W ω) u p).re + W ω u)
    (hWm : ∀ u ∈ Icc (0 : ℝ) t, Measurable (G.indicator fun ω => W ω u))
    (hVm : ∀ u ∈ Icc (0 : ℝ) t, Measurable (G.indicator fun ω => V ω u)) :
    Measurable (G.indicator fun ω => Real.log (deriv (fwdMap (W ω) t) p).re) := by
  have hm : ∀ u ∈ Icc (0 : ℝ) t,
      Measurable (G.indicator fun ω => -2 / (V ω u - W ω u) ^ 2) := by
    intro u hu
    convert ((measurable_const (a := (-2 : ℝ))).div (((hVm u hu).sub (hWm u hu)).pow_const 2)).indicator hG using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, Pi.div_apply, Pi.sub_apply]
    · simp only [indicator_of_notMem hω]
  have hi := Ito.measurable_intervalIntegral_of_continuousOn ht hm (fun ω => ?_)
  · convert hi using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      obtain ⟨q, hq'⟩ := hq ω hω
      rw [log_source_deriv_eq_integral (hW ω hω) hq' ⟨ht, hT ω hω⟩]
      exact intervalIntegral.integral_congr fun u hu => by rw [hV ω hω u (uIcc_of_le ht ▸ hu), add_sub_cancel_right]
    · simp only [indicator_of_notMem hω, intervalIntegral.integral_zero]
  · by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      obtain ⟨q, hq'⟩ := hq ω hω
      have hs : Icc (0 : ℝ) t ⊆ Icc 0 (T ω) := Icc_subset_Icc_right (hT ω hω)
      have hVc' : ContinuousOn (fun u => (fwdMap (W ω) u p).re + W ω u) (Icc 0 t) :=
        fun u hu => (((source_gmap_rates (hW ω hω) hq' (hs hu)).1).mono hs).continuousWithinAt
      have hcont := hVc'.sub (hW ω hω).continuousOn
      have hne : ∀ u ∈ Icc (0 : ℝ) t, (fwdMap (W ω) u p).re + W ω u - W ω u ≠ 0 := by
        intro u hu
        rw [add_sub_cancel_right]
        exact re_ne_zero_of_im_eq_zero
          ((fwdMap_eq_of_isForwardSol (hW ω hω) hq' (hs hu)).symm ▸ (hq'.2 u (hs hu)).1)
          (fwdMap_real_im (hW ω hω) hq' (hs hu))
      have hc : ContinuousOn (fun u => -2 / ((fwdMap (W ω) u p).re + W ω u - W ω u) ^ 2)
          (Icc 0 t) := continuousOn_const.div (hcont.pow 2) (fun u hu => pow_ne_zero 2 (hne u hu))
      apply hc.congr
      intro u hu
      change -2 / (V ω u - W ω u) ^ 2 = _
      rw [hV ω hω u hu]
    · simp only [indicator_of_notMem hω]
      exact continuousOn_const

end InteractingSLE.ZhanGT4
