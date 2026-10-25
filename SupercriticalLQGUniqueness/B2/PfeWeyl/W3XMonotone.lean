import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XUpperFamily

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private theorem weyl_mono_x {ξ : ℝ} (hξ : 0 ≤ ξ)
    {f g : C(ℂ, ℝ)} {D : LSCMetric} (hfg : ∀ z, f z ≤ g z)
    (p : ℂ × ℂ) :
    weylScale ξ f D p ≤ weylScale ξ g D p := by
  simp only [weylScale]
  refine iInf_mono fun P => iInf_mono fun L => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ => ?_
  exact setLIntegral_mono' measurableSet_Icc fun t _ =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg (P t)) hξ))

private theorem mollCont_mono_x {ε : ℝ} (hε : ε ≠ 0)
    {f g : C(ℂ, ℝ)} {M M' : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hM' : ∀ z, |g z| ≤ M')
    (hfg : ∀ z, f z ≤ g z) (z : ℂ) :
    LQGMetric.LFPP.mollCont ε hε f M hM z ≤
      LQGMetric.LFPP.mollCont ε hε g M' hM' z := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  change LQGMetric.heatMollify ε (LQGMetric.ofCont f) z ≤
    LQGMetric.heatMollify ε (LQGMetric.ofCont g) z
  rw [LQGMetric.heatMollify_ofCont f M hM ε hε z,
      LQGMetric.heatMollify_ofCont g M' hM' ε hε z]
  exact integral_mono
    (by simpa only [mul_comm] using
      LQGMetric.integrable_heatKernel_mul_of_bdd f M hM _ hs z)
    (by simpa only [mul_comm] using
      LQGMetric.integrable_heatKernel_mul_of_bdd g M' hM' _ hs z)
    fun w => mul_le_mul_of_nonneg_right (hfg w)
      (LQGMetric.heatKernel_nonneg _ hs.le z w)

 
theorem normalizedLFPPMetric_shift_mono_x {ξ : ℝ} (hξ : 0 ≤ ξ)
    (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) {ε : ℝ} (hε : ε ≠ 0)
    {f g : C(ℂ, ℝ)} {M M' : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hM' : ∀ z, |g z| ≤ M')
    (hfg : ∀ z, f z ≤ g z) (p : ℂ × ℂ) :
    normalizedLFPPMetric ξ a
      (φ + LQGMetric.LFPP.mollCont ε hε f M hM) p ≤
    normalizedLFPPMetric ξ a
      (φ + LQGMetric.LFPP.mollCont ε hε g M' hM') p := by
  rw [normalizedLFPPMetric_add_eq_weylScale, normalizedLFPPMetric_add_eq_weylScale]
  exact weyl_mono_x hξ (mollCont_mono_x hε hM hM' hfg) p

end SupercriticalLQGUniqueness.B2.PfeWeyl
