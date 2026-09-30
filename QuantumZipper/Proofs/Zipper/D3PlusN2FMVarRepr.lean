import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, node FM-REPR: the first mode as a pair of field evaluations

Task N2Z-FMVAR-F. `fmReprStmt_holds : FMReprStmt`.

Route (own elementary bookkeeping): the `k`-th part of `∫_0^{2π} g(w + τ e^{iθ}, s) e^{iθ} dθ`
is `∫_0^{2π} g(w + τ u_k e^{iφ}, s) cos φ dφ` (real part, resp. imaginary part after the shift
`θ = φ + π/2`, by `2π`-periodicity). Splitting `cos = cos⁺ − cos⁻` and shifting the `cos⁻` part by
`π` (`w + τ u e^{i(φ+π)} = w − τ u e^{iφ}`) gives the difference of the pairings of `g(·, s)` with
the arc measures `fmArc w (± τ u_k)`. The probabilistic step is the repository's stochastic Fubini
`WedgeTK.ae_integral_G_eq`, applied with the compact set `closedBall w τ ⊆ Hbar`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Real ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The function `φ ↦ g(w + v e^{iφ}, s)` on the circle. -/
def fmH (g : ℂ × ℝ → ℝ) (w v : ℂ) (s φ : ℝ) : ℝ :=
  g (w + v * Complex.exp ((φ : ℂ) * Complex.I), s)

theorem fmH_add (g : ℂ × ℝ → ℝ) (w v : ℂ) (s φ c : ℝ) :
    fmH g w v s (φ + c) = fmH g w (v * Complex.exp ((c : ℂ) * Complex.I)) s φ := by
  unfold fmH
  congr 3
  push_cast
  rw [add_mul, Complex.exp_add]; ring

theorem fmH_periodic (g : ℂ × ℝ → ℝ) (w v : ℂ) (s : ℝ) :
    Function.Periodic (fmH g w v s) (2 * π) := by
  intro φ
  rw [fmH_add]
  congr 1
  push_cast
  rw [Complex.exp_two_pi_mul_I, mul_one]

theorem im_nonneg_of_norm_le {w z : ℂ} {τ : ℝ} (hz : ‖z - w‖ ≤ τ) (hτ : τ ≤ w.im) :
    0 ≤ z.im := by
  have h1 := Complex.abs_im_le_norm (z - w)
  rw [Complex.sub_im] at h1
  have := (abs_le.1 h1).1
  linarith

theorem continuous_fmH {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) {w v : ℂ}
    {s : ℝ} (hv : ‖v‖ ≤ w.im) (hs : 0 < s) : Continuous (fmH g w v s) := by
  refine hg.comp_continuous (by fun_prop) fun φ => ⟨?_, hs⟩
  show 0 ≤ (w + v * Complex.exp ((φ : ℂ) * Complex.I)).im
  refine im_nonneg_of_norm_le (w := w) (τ := ‖v‖) ?_ hv
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Shifting a `2π`-periodic function does not change its integral over a period. -/
theorem integral_shift_fm (F : ℝ → ℝ) (hF : Function.Periodic F (2 * π)) (c : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), F (φ + c) = ∫ φ in (0 : ℝ)..(2 * π), F φ := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π) c]
  simpa using hF.intervalIntegral_add_eq c 0

/-- Step C: the `cos⁺`-pairing is the integral against the arc measure. -/
theorem integral_fmArc_eq {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) {w v : ℂ}
    {s : ℝ} (hv : ‖v‖ ≤ w.im) (hs : 0 < s) :
    ∫ z, g (z, s) ∂fmArc w v =
      ∫ φ in (0 : ℝ)..(2 * π), fmH g w v s φ * max (Real.cos φ) 0 := by
  have hae : ∀ᵐ z ∂fmArc w v, z ∈ Hbar := by
    unfold fmArc
    refine (ae_map_iff (measurable_fmArcMap w v).aemeasurable
      (measurableSet_le measurable_const Complex.measurable_im)).2 (ae_of_all _ fun φ => ?_)
    refine im_nonneg_of_norm_le (w := w) (τ := ‖v‖) ?_ hv
    rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsm : AEStronglyMeasurable (fun z => g (z, s)) (fmArc w v) := by
    have hc : ContinuousOn (fun z => g (z, s)) Hbar :=
      hg.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hu => ⟨hu, hs⟩
    have := hc.aestronglyMeasurable (μ := fmArc w v)
      (measurableSet_le measurable_const Complex.measurable_im)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  unfold fmArc
  rw [integral_map (measurable_fmArcMap w v).aemeasurable (by unfold fmArc at hsm; exact hsm)]
  unfold fmBase
  rw [integral_withDensity_eq_integral_toReal_smul
    (Real.continuous_cos.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul, fmH]
  ring

/-- Step A: the `k`-th part of the first mode is the `cos`-pairing in direction `u_k`. -/
theorem fmPart_fmInt_eq_cos {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) (k : Fin 2)
    {w : ℂ} {τ s : ℝ} (hτ : 0 < τ) (hτw : τ ≤ w.im) (hs : 0 < s) :
    fmPart k (fmInt g w τ s) =
      ∫ φ in (0 : ℝ)..(2 * π), fmH g w ((τ : ℂ) * fmDir k) s φ * Real.cos φ := by
  have h1 : Continuous (fmH g w (τ : ℂ) s) :=
    continuous_fmH hg (by rw [Complex.norm_real, Real.norm_of_nonneg hτ.le]; exact hτw) hs
  have hint : IntervalIntegrable (fun θ : ℝ => ((fmH g w (τ : ℂ) s θ : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ => ((fmH g w (τ : ℂ) s θ : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)).intervalIntegrable _ _
  have hfm : fmInt g w τ s = ∫ θ in (0 : ℝ)..(2 * π), ((fmH g w (τ : ℂ) s θ : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I) := rfl
  fin_cases k
  · simp only [fmPart, fmDir, hfm]
    rw [show (Fin.mk 0 (by norm_num) : Fin 2) = 0 from rfl, if_pos rfl]
    have := intervalIntegral.intervalIntegral_re hint
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at this
    rw [if_pos rfl, mul_one]
    exact this.symm
  · simp only [fmPart, fmDir, hfm]
    rw [show (Fin.mk 1 (by norm_num) : Fin 2) = 1 from rfl, if_neg one_ne_zero,
      if_neg one_ne_zero]
    have := intervalIntegral.intervalIntegral_im hint
    simp only [RCLike.im_to_complex, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at this
    rw [← this, ← integral_shift_fm (fun φ => fmH g w (τ : ℂ) s φ * Real.sin φ)
      (fun φ => by simp only [fmH_periodic g w _ s φ, Real.sin_add_two_pi]) (π / 2)]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [fmH_add, Real.sin_add_pi_div_two]
    congr 2
    push_cast
    rw [Complex.exp_pi_div_two_mul_I]

/-- **Deterministic identity.** -/
theorem fmPart_fmInt_eq_arc {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) (k : Fin 2)
    {w : ℂ} {τ s : ℝ} (hτ : 0 < τ) (hτw : τ ≤ w.im) (hs : 0 < s) :
    fmPart k (fmInt g w τ s) =
      ∫ z, g (z, s) ∂fmArc w ((τ : ℂ) * fmDir k) -
        ∫ z, g (z, s) ∂fmArc w (-((τ : ℂ) * fmDir k)) := by
  set v : ℂ := (τ : ℂ) * fmDir k with hv
  have hnv : ‖v‖ = τ := by
    rw [hv, norm_mul, norm_fmDir, Complex.norm_real, Real.norm_of_nonneg hτ.le, mul_one]
  have hc := continuous_fmH hg (v := v) (hnv.le.trans hτw) hs
  rw [fmPart_fmInt_eq_cos hg k hτ hτw hs, integral_fmArc_eq hg (hnv.le.trans hτw) hs,
    integral_fmArc_eq hg (by rw [norm_neg]; exact hnv.le.trans hτw) hs]
  -- the `cos⁻` part, shifted by `π`
  have hneg : ∫ φ in (0 : ℝ)..(2 * π), fmH g w (-v) s φ * max (Real.cos φ) 0 =
      ∫ φ in (0 : ℝ)..(2 * π), fmH g w v s φ * max (-Real.cos φ) 0 := by
    have hper : Function.Periodic (fun φ => fmH g w v s φ * max (-Real.cos φ) 0) (2 * π) :=
      fun φ => by simp only [fmH_periodic g w v s φ, Real.cos_add_two_pi]
    rw [← integral_shift_fm _ hper π]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [fmH_add, Real.cos_add_pi, neg_neg, Complex.exp_pi_mul_I, mul_neg_one]
  have i1 : IntervalIntegrable (fun φ => fmH g w v s φ * max (Real.cos φ) 0) volume 0 (2 * π) :=
    (hc.mul (by fun_prop)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun φ => fmH g w v s φ * max (-Real.cos φ) 0) volume 0
      (2 * π) := (hc.mul (by fun_prop)).intervalIntegrable _ _
  rw [hneg, ← intervalIntegral.integral_sub i1 i2, ← hv]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [← mul_sub]
  congr 1
  rcases le_total 0 (Real.cos φ) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **Node FM-REPR holds** (stochastic Fubini `WedgeTK.ae_integral_G_eq` on both arcs). -/
theorem fmReprStmt_holds : FMReprStmt := by
  intro Ω _ P _ X hX G hG k w τ s hτ hτw hs
  have hK : closedBall w τ ⊆ Hbar := fun z hz =>
    im_nonneg_of_norm_le (by rwa [mem_closedBall, dist_eq_norm] at hz) hτw
  have harc : ∀ v : ℂ, ‖v‖ = τ → fmArc w v (closedBall w τ)ᶜ = 0 := by
    intro v hv
    have : ∀ᵐ z ∂fmArc w v, z ∈ closedBall w τ := by
      unfold fmArc
      refine (ae_map_iff (measurable_fmArcMap w v).aemeasurable measurableSet_closedBall).2
        (ae_of_all _ fun φ => ?_)
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, hv]
    exact ae_iff.1 this
  have hnv : ‖(τ : ℂ) * fmDir k‖ = τ := by
    rw [norm_mul, norm_fmDir, Complex.norm_real, Real.norm_of_nonneg hτ.le, mul_one]
  filter_upwards [WedgeTK.ae_integral_G_eq hX hG hs (fmArc w ((τ : ℂ) * fmDir k))
      (isCompact_closedBall w τ) hK (harc _ hnv),
    WedgeTK.ae_integral_G_eq hX hG hs (fmArc w (-((τ : ℂ) * fmDir k)))
      (isCompact_closedBall w τ) hK (harc _ (by rw [norm_neg, hnv]))] with ω h1 h2
  rw [fmPart_fmInt_eq_arc (hG.cont ω) k hτ hτw hs, h1, h2]
  rfl

end D3Plus
end QuantumZipper
