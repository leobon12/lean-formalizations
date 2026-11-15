/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.PolarDisk
import InteractingSLE.Spec.Sec6.FiniteExceptionDisk
import InteractingSLE.Spec.Sec6.TraceOneDim
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The disk trace estimate (PU1)

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
`#id-PU1`, p. 164):

  `‖Tr v‖²_{H^{1/2}} ≤ C (‖v‖²_{L²(𝔻)} + ∫_𝔻 |∇v|²)`, with `‖w‖²_{H^{1/2}} = ∑ (1 + |n|) |ŵ(n)|²`.

"It follows by taking angular Fourier coefficients `a_n(r)` of a smooth `v`." We prove it for a
`C¹` function `v` on the open disk, with the trace taken on the circle of radius `R ∈ [1/2, 1)`
(the form used: the cutoffs of Aux. lemma 29 are smooth only inside the disk).

## Angular coefficients
For `|s| < 1`, `a_n(s) = (2π)⁻¹ ∫₀^{2π} e^{−int} v(se^{it}) dt` (`angCoeff`); its derivative is the
coefficient of the radial derivative `Dv(se^{it})(e^{it})` (`angDerivCoeff`, by differentiation
under the integral), and `in a_n(s)` is the coefficient of the angular derivative
`Dv(se^{it})(i s e^{it})`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Interval

namespace InteractingSLE.Sec6

theorem norm_polarPt' (s t : ℝ) : ‖polarPt s t‖ = |s| := by
  simp [polarPt, Complex.norm_exp_ofReal_mul_I]

theorem polarPt_mem_ball' {s : ℝ} (hs : |s| < 1) (t : ℝ) : polarPt s t ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_polarPt']; exact hs

theorem hasDerivAt_polarPt_radius (s t : ℝ) :
    HasDerivAt (fun s : ℝ => polarPt s t) (exp (t * I)) s := by
  simpa [polarPt] using (hasDerivAt_id (s : ℂ)).comp_ofReal.mul_const (exp (t * I))

theorem hasDerivAt_polarPt_angle (s t : ℝ) :
    HasDerivAt (fun t : ℝ => polarPt s t) ((s : ℂ) * (I * exp (t * I))) t := by
  have h : HasDerivAt (fun w : ℂ => exp (w * I)) (exp ((t : ℂ) * I) * I) (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).cexp
  have := (h.comp_ofReal).const_mul (s : ℂ)
  simp only [polarPt]
  refine this.congr_deriv ?_
  ring

theorem polarPt_two_pi (s : ℝ) : polarPt s (2 * π) = polarPt s 0 := by
  simp only [polarPt]
  rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I]
  simp

section Angular

variable (v : ℂ → ℝ) (Dv : ℂ → ℂ →L[ℝ] ℝ)

/-- The angular Fourier coefficient `a_n(s)` of `v` on the circle of radius `s`. -/
def angCoeff (n : ℤ) (s : ℝ) : ℂ := circCoeff (fun t => (v (polarPt s t) : ℂ)) n

/-- The angular Fourier coefficient of the radial derivative. -/
def angDerivCoeff (n : ℤ) (s : ℝ) : ℂ :=
  circCoeff (fun t => ((Dv (polarPt s t)) (exp (t * I)) : ℂ)) n

variable {v Dv}

/-- A uniform bound for `Dv` on a neighbourhood of a circle inside the disk. -/
theorem exists_local_bound (hDv : ContinuousOn Dv (ball 0 1)) {s₀ : ℝ} (hs₀ : |s₀| < 1) :
    ∃ ε > 0, ∃ M : ℝ, (∀ s ∈ Metric.ball s₀ ε, |s| < 1) ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ t : ℝ, ‖Dv (polarPt s t)‖ ≤ M := by
  set ρ := (1 + |s₀|) / 2
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hDv.mono (closedBall_subset_ball hρ1))
  refine ⟨(1 - |s₀|) / 2, by linarith, M, ?_, ?_⟩
  · intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub s s₀
    linarith
  · intro s hs t
    rw [Metric.mem_ball, Real.dist_eq] at hs
    refine hM _ ?_
    rw [mem_closedBall_zero_iff, norm_polarPt']
    have := abs_sub_abs_le_abs_sub s s₀
    simp only [ρ]; linarith

theorem hasDerivAt_v_polar_radius (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z) {s : ℝ}
    (hs : |s| < 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => v (polarPt s t)) ((Dv (polarPt s t)) (exp (t * I))) s :=
  (hv _ (polarPt_mem_ball' hs t)).comp_hasDerivAt s (hasDerivAt_polarPt_radius s t)

theorem hasDerivAt_v_polar_angle (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z) {s : ℝ}
    (hs : |s| < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => v (polarPt s t)) ((Dv (polarPt s t)) ((s : ℂ) * (I * exp (t * I)))) t :=
  (hv _ (polarPt_mem_ball' hs t)).comp_hasDerivAt t (hasDerivAt_polarPt_angle s t)

theorem continuousOn_v (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z) :
    ContinuousOn v (ball 0 1) := fun z hz => (hv z hz).continuousAt.continuousWithinAt

theorem continuous_v_polar (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z) {s : ℝ}
    (hs : |s| < 1) : Continuous fun t : ℝ => v (polarPt s t) :=
  (continuousOn_v hv).comp_continuous (by unfold polarPt; fun_prop) (polarPt_mem_ball' hs)

theorem continuous_Dv_polar (hDv : ContinuousOn Dv (ball 0 1)) {s : ℝ} (hs : |s| < 1) (w : ℝ → ℂ)
    (hw : Continuous w) : Continuous fun t : ℝ => (Dv (polarPt s t)) (w t) :=
  (hDv.comp_continuous (by unfold polarPt; fun_prop) (polarPt_mem_ball' hs)).clm_apply hw

/-- **Differentiation under the integral**: `a_n' = (coefficient of the radial derivative)`. -/
theorem hasDerivAt_angCoeff (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) (n : ℤ) {s₀ : ℝ} (hs₀ : |s₀| < 1) :
    HasDerivAt (angCoeff v n) (angDerivCoeff Dv n s₀) s₀ := by
  obtain ⟨ε, hε, M, hball, hM⟩ := exists_local_bound hDv hs₀
  have hexp : ∀ t : ℝ, ‖exp (-((n : ℂ) * t * I))‖ = 1 := fun t => by
    rw [show -((n : ℂ) * t * I) = ((-(n : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := 0)
    (b := 2 * π) (μ := volume) (bound := fun _ => M)
    (F := fun s t => exp (-((n : ℂ) * t * I)) * (v (polarPt s t) : ℂ))
    (F' := fun s t => exp (-((n : ℂ) * t * I)) * ((Dv (polarPt s t)) (exp (t * I)) : ℂ))
    (x₀ := s₀) (s := Metric.ball s₀ ε) (Metric.ball_mem_nhds s₀ hε)
    (by
      filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I))).mul
        (Complex.continuous_ofReal.comp (continuous_v_polar hv (hball s hs)))).aestronglyMeasurable)
    (((by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I))).mul
        (Complex.continuous_ofReal.comp (continuous_v_polar hv hs₀))).intervalIntegrable _ _)
    (((by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I))).mul
        (Complex.continuous_ofReal.comp (continuous_Dv_polar hDv hs₀ _
          (by fun_prop)))).aestronglyMeasurable)
    (Eventually.of_forall fun t _ s hs => by
      rw [norm_mul, hexp, one_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |(Dv (polarPt s t)) (exp (t * I))| ≤ ‖Dv (polarPt s t)‖ * ‖exp (t * I)‖ :=
            (Dv (polarPt s t)).le_opNorm _
        _ ≤ M := by rw [Complex.norm_exp_ofReal_mul_I, mul_one]; exact hM s hs t)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ s hs =>
      ((hasDerivAt_v_polar_radius hv (hball s hs) t).ofReal_comp).const_mul _)
  have := key.2.const_mul (((2 * π)⁻¹ : ℝ) : ℂ)
  exact this

theorem continuousOn_angDerivCoeff (hDv : ContinuousOn Dv (ball 0 1)) (n : ℤ) :
    ContinuousOn (angDerivCoeff Dv n) (Ioo (-1) 1) := by
  intro s₀ hs₀
  have hs₀' : |s₀| < 1 := abs_lt.2 hs₀
  obtain ⟨ε, hε, M, hball, hM⟩ := exists_local_bound hDv hs₀'
  have hexp : ∀ t : ℝ, ‖exp (-((n : ℂ) * t * I))‖ = 1 := fun t => by
    rw [show -((n : ℂ) * t * I) = ((-(n : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
    exact ((by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I))).mul
      (Complex.continuous_ofReal.comp (continuous_Dv_polar hDv (hball s hs) _
        (by fun_prop)))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
    refine Eventually.of_forall fun t _ => ?_
    rw [norm_mul, hexp, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |(Dv (polarPt s t)) (exp (t * I))| ≤ ‖Dv (polarPt s t)‖ * ‖exp (t * I)‖ :=
          (Dv (polarPt s t)).le_opNorm _
      _ ≤ M := by rw [Complex.norm_exp_ofReal_mul_I, mul_one]; exact hM s hs t
  · refine Eventually.of_forall fun t _ => ?_
    refine ContinuousAt.mul continuousAt_const (Complex.continuous_ofReal.continuousAt.comp ?_)
    have hp : ContinuousAt (fun s : ℝ => polarPt s t) s₀ := by unfold polarPt; fun_prop
    have hc : ContinuousAt (fun s : ℝ => Dv (polarPt s t)) s₀ :=
      ContinuousAt.comp (g := Dv) (f := fun s : ℝ => polarPt s t)
        (hDv.continuousAt (isOpen_ball.mem_nhds (polarPt_mem_ball' hs₀' t))) hp
    exact hc.clm_apply continuousAt_const

/-- `a_n(0) = 0` for `n ≠ 0`. -/
theorem angCoeff_zero {n : ℤ} (hn : n ≠ 0) : angCoeff v n 0 = 0 := by
  have h := circCoeff_exp_neg 0 (-n)
  simp only [neg_neg, Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero] at h
  have hn' : ¬ (-n = 0) := by omega
  simp only [hn', ↓reduceIte] at h
  have hconst : (fun t : ℝ => (v (polarPt 0 t) : ℂ)) = fun _ => (v 0 : ℂ) := by
    funext t; simp [polarPt]
  rw [angCoeff, hconst]
  unfold circCoeff at h ⊢
  have : (fun t : ℝ => exp (-((n : ℂ) * t * I)) * (v 0 : ℂ)) =
      fun t : ℝ => (v 0 : ℂ) * (exp (-((n : ℂ) * t * I)) * 1) := by funext t; ring
  rw [this, intervalIntegral.integral_const_mul, mul_left_comm, h, mul_zero]

end Angular

/-! ## Parseval on each circle -/

section Parseval

variable {v : ℂ → ℝ} {Dv : ℂ → ℂ →L[ℝ] ℝ}

theorem hasSum_sq_angCoeff (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z) {s : ℝ}
    (hs : |s| < 1) :
    HasSum (fun n => ‖angCoeff v n s‖ ^ 2)
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, v (polarPt s t) ^ 2) := by
  have h := hasSum_sq_circCoeff (Complex.continuous_ofReal.comp (continuous_v_polar hv hs))
  simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

theorem hasSum_sq_angDerivCoeff (hDv : ContinuousOn Dv (ball 0 1)) {s : ℝ} (hs : |s| < 1) :
    HasSum (fun n => ‖angDerivCoeff Dv n s‖ ^ 2)
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ((Dv (polarPt s t)) (exp (t * I))) ^ 2) := by
  have h := hasSum_sq_circCoeff (Complex.continuous_ofReal.comp
    (continuous_Dv_polar hDv hs _ (by fun_prop : Continuous fun t : ℝ => exp (t * I))))
  simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

theorem hasSum_sq_mul_angCoeff (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) {s : ℝ} (hs : |s| < 1) :
    HasSum (fun n : ℤ => (n : ℝ) ^ 2 * ‖angCoeff v n s‖ ^ 2)
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        ((Dv (polarPt s t)) ((s : ℂ) * (I * exp (t * I)))) ^ 2) := by
  have hcont : Continuous fun t : ℝ => ((Dv (polarPt s t)) ((s : ℂ) * (I * exp (t * I))) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_Dv_polar hDv hs _ (by fun_prop))
  have hloop : IsC1Loop (fun t => (v (polarPt s t) : ℂ))
      (fun t => ((Dv (polarPt s t)) ((s : ℂ) * (I * exp (t * I))) : ℂ)) :=
    ⟨fun t => (hasDerivAt_v_polar_angle hv hs t).ofReal_comp, hcont, by
      simp only [polarPt_two_pi]⟩
  have h := hasSum_sq_circCoeff hcont
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  refine h.congr_fun fun n => ?_
  rw [circCoeff_deriv hloop.1 hloop.2.1 hloop.2.2 n, norm_mul, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_intCast, mul_pow, sq_abs]
  rfl

theorem sq_apply_le (L : ℂ →L[ℝ] ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) : (L w) ^ 2 ≤ ‖L‖ ^ 2 := by
  have h := L.le_opNorm w
  have h1 : |L w| ≤ ‖L‖ := by
    rw [← Real.norm_eq_abs]
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hw)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

end Parseval

/-! ## Polar conversion for continuous integrands -/

/-- For a continuous `2π`-periodic `h ≥ 0`, `∫⁻_{(−π, π)} h = ∫₀^{2π} h`. -/
theorem lintegral_Ioo_pi_eq {h : ℝ → ℝ} (hc : Continuous h) (hper : Function.Periodic h (2 * π))
    (h0 : ∀ t, 0 ≤ h t) :
    ∫⁻ t in Ioo (-π) π, ENNReal.ofReal (h t) = ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, h t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hc.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall h0), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have h2 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h2
  rw [h2]

/-- Polar coordinates for a function `G ≥ 0` continuous on the disk. -/
theorem lintegral_ball_eq_polar_of_continuousOn {G : ℂ → ℝ} (hG : ContinuousOn G (ball 0 1))
    (hG0 : ∀ z, 0 ≤ G z) :
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (G z) =
      ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ *
        ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, G (polarPt ρ t)) := by
  classical
  set H : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator fun z => ENNReal.ofReal (G z)
  have hHm : Measurable H := by
    have := ContinuousOn.measurable_piecewise (f := fun z => ENNReal.ofReal (G z))
      (g := fun _ => (0 : ℝ≥0∞)) (s := ball (0 : ℂ) 1)
      (ENNReal.continuous_ofReal.comp_continuousOn hG) continuousOn_const measurableSet_ball
    have hH : H = (ball (0 : ℂ) 1).piecewise (fun z => ENNReal.ofReal (G z)) fun _ => 0 := by
      funext z; simp only [H, Set.indicator, Set.piecewise]
    rw [hH]; exact this
  have h1 : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (G z) = ∫⁻ z in ball (0 : ℂ) 1, H z :=
    setLIntegral_congr_fun measurableSet_ball fun z hz => by simp [H, indicator_of_mem hz]
  rw [h1, lintegral_ball_eq_polar hHm]
  refine setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ => ?_
  have hρ' : |ρ| < 1 := by rw [abs_of_pos hρ.1]; exact hρ.2
  congr 1
  have h2 : ∫⁻ t in Ioo (-π) π, H (polarPt ρ t) =
      ∫⁻ t in Ioo (-π) π, ENNReal.ofReal (G (polarPt ρ t)) :=
    lintegral_congr fun t => by simp [H, indicator_of_mem (polarPt_mem_ball' hρ' t)]
  rw [h2]
  refine lintegral_Ioo_pi_eq (hG.comp_continuous (by unfold polarPt; fun_prop)
    (polarPt_mem_ball' hρ')) (fun t => ?_) (fun t => hG0 _)
  have hp : polarPt ρ (t + 2 * π) = polarPt ρ t := by
    simp only [polarPt]
    rw [show ((t + 2 * π : ℝ) : ℂ) * I = (t : ℂ) * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [hp]

/-! ## The trace estimate -/

section Trace

variable {v : ℂ → ℝ} {Dv : ℂ → ℂ →L[ℝ] ℝ}

theorem sq_apply_smul_le (L : ℂ →L[ℝ] ℝ) (s : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    (L ((s : ℂ) * w)) ^ 2 ≤ s ^ 2 * ‖L‖ ^ 2 := by
  have : L ((s : ℂ) * w) = s * L w := by
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  rw [this, mul_pow]
  exact mul_le_mul_of_nonneg_left (sq_apply_le L hw) (sq_nonneg s)

/-- The pointwise bound for the radial integrand. -/
theorem radial_sum_le (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (S : Finset ℤ) :
    ∑ n ∈ S, (s * ‖angDerivCoeff Dv n s‖ ^ 2 + |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s) ≤
      s * (π⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) := by
  have hs' : |s| < 1 := by rw [abs_of_pos hs.1]; exact hs.2
  have hcD : Continuous fun t : ℝ => ‖Dv (polarPt s t)‖ ^ 2 :=
    ((hDv.comp_continuous (by unfold polarPt; fun_prop) (polarPt_mem_ball' hs')).norm).pow 2
  have hX := hasSum_sq_angDerivCoeff hDv hs'
  have hY := hasSum_sq_mul_angCoeff hv hDv hs'
  have hXle : ∑ n ∈ S, ‖angDerivCoeff Dv n s‖ ^ 2 ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2 := by
    refine (sum_le_hasSum S (fun n _ => sq_nonneg _) hX).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.integral_mono_on (by positivity) ?_ (hcD.intervalIntegrable _ _)
      fun t _ => sq_apply_le _ (by rw [Complex.norm_exp_ofReal_mul_I])
    exact ((continuous_Dv_polar hDv hs' _ (by fun_prop)).pow 2).intervalIntegrable _ _
  have hYle : ∑ n ∈ S, (n : ℝ) ^ 2 * ‖angCoeff v n s‖ ^ 2 ≤
      (2 * π)⁻¹ * (s ^ 2 * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) := by
    refine (sum_le_hasSum S (fun n _ => by positivity) hY).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by positivity) ?_
      ((continuous_const.mul hcD).intervalIntegrable _ _) fun t _ => ?_
    · exact ((continuous_Dv_polar hDv hs' _ (by fun_prop)).pow 2).intervalIntegrable _ _
    · refine sq_apply_smul_le _ s ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hsplit : ∑ n ∈ S, (s * ‖angDerivCoeff Dv n s‖ ^ 2 + |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s)
      = s * ∑ n ∈ S, ‖angDerivCoeff Dv n s‖ ^ 2 +
        (∑ n ∈ S, (n : ℝ) ^ 2 * ‖angCoeff v n s‖ ^ 2) / s := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun n _ => by rw [sq_abs]
  rw [hsplit]
  have hs0 : 0 < s := hs.1
  calc s * ∑ n ∈ S, ‖angDerivCoeff Dv n s‖ ^ 2 + (∑ n ∈ S, (n : ℝ) ^ 2 * ‖angCoeff v n s‖ ^ 2) / s
      ≤ s * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) +
        (2 * π)⁻¹ * (s ^ 2 * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) / s := by
        gcongr
    _ = s * (π⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) := by
        field_simp; ring

end Trace

section Trace2

variable {v : ℂ → ℝ} {Dv : ℂ → ℂ →L[ℝ] ℝ}

/-- The homogeneous part of (PU1): `∑ |n| |a_n(R)|² ≤ π⁻¹ ∫_𝔻 |∇v|²`. -/
theorem homogeneous_trace_le (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (S : Finset ℤ) :
    ENNReal.ofReal (∑ n ∈ S, |(n : ℝ)| * ‖angCoeff v n R‖ ^ 2) ≤
      ENNReal.ofReal π⁻¹ * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2) := by
  have hsub : Ioo (0 : ℝ) R ⊆ Ioo 0 1 := Ioo_subset_Ioo_right hR1.le
  -- per coefficient
  have hper : ∀ n : ℤ, ENNReal.ofReal (|(n : ℝ)| * ‖angCoeff v n R‖ ^ 2) ≤
      ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal (s * ‖angDerivCoeff Dv n s‖ ^ 2 +
        |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    refine ofReal_mul_norm_sq_le_lintegral (g := angCoeff v n) (g' := angDerivCoeff Dv n)
      (fun s hs => hasDerivAt_angCoeff hv hDv n (by rw [abs_of_pos hs.1]; exact hs.2))
      ((continuousOn_angDerivCoeff hDv n).mono (Ioo_subset_Ioo_left (by norm_num)))
      ?_ (abs_nonneg _) hR0 hR1
    have h0 := (hasDerivAt_angCoeff hv hDv n (by norm_num : |(0 : ℝ)| < 1)).continuousAt.tendsto
    rw [angCoeff_zero hn] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  -- continuity of the integrands on `(0, R)`
  have hcont : ∀ n : ℤ, ContinuousOn (fun s => s * ‖angDerivCoeff Dv n s‖ ^ 2 +
      |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s) (Ioo 0 R) := by
    intro n
    have h1 : ContinuousOn (angCoeff v n) (Ioo 0 R) := fun s hs =>
      (hasDerivAt_angCoeff hv hDv n (by rw [abs_of_pos hs.1]; linarith [hs.2])).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (angDerivCoeff Dv n) (Ioo 0 R) :=
      (continuousOn_angDerivCoeff hDv n).mono fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (continuousOn_id.mul (h2.norm.pow 2)).add
      ((continuousOn_const.mul (h1.norm.pow 2)).div continuousOn_id fun s hs => hs.1.ne')
  calc ENNReal.ofReal (∑ n ∈ S, |(n : ℝ)| * ‖angCoeff v n R‖ ^ 2)
      = ∑ n ∈ S, ENNReal.ofReal (|(n : ℝ)| * ‖angCoeff v n R‖ ^ 2) :=
        ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity
    _ ≤ ∑ n ∈ S, ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal (s * ‖angDerivCoeff Dv n s‖ ^ 2 +
          |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s) := Finset.sum_le_sum fun n _ => hper n
    _ = ∫⁻ s in Ioo (0 : ℝ) R, ∑ n ∈ S, ENNReal.ofReal (s * ‖angDerivCoeff Dv n s‖ ^ 2 +
          |(n : ℝ)| ^ 2 * ‖angCoeff v n s‖ ^ 2 / s) := by
        rw [lintegral_finset_sum']
        intro n _
        exact (ENNReal.continuous_ofReal.comp_continuousOn (hcont n)).aemeasurable measurableSet_Ioo
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal s *
          (ENNReal.ofReal π⁻¹ * ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by have := hs.1; positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hs.1.le]
        exact ENNReal.ofReal_le_ofReal (radial_sum_le hv hDv (hsub hs) S)
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal s *
          (ENNReal.ofReal π⁻¹ * ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2)) :=
        lintegral_mono_set hsub
    _ = ENNReal.ofReal π⁻¹ * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2) := by
        rw [lintegral_ball_eq_polar_of_continuousOn (G := fun z => ‖Dv z‖ ^ 2)
          (hDv.norm.pow 2) (fun z => sq_nonneg _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        ring

end Trace2

section Trace3

variable {v : ℂ → ℝ} {Dv : ℂ → ℂ →L[ℝ] ℝ}

/-- An annular integral bounded by a disk integral, in polar coordinates. -/
theorem ofReal_integral_annulus_le {G : ℂ → ℝ} (hG : ContinuousOn G (ball 0 1)) (hG0 : ∀ z, 0 ≤ G z)
    {φ : ℝ → ℝ} {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hc : 0 ≤ c)
    (hφ : ContinuousOn φ (Icc a b)) (hφ0 : ∀ s ∈ Icc a b, 0 ≤ φ s)
    (hφle : ∀ s ∈ Icc a b, φ s ≤ s * (c * ∫ t in (0 : ℝ)..2 * π, G (polarPt s t))) :
    ENNReal.ofReal (∫ s in a..b, φ s) ≤
      ENNReal.ofReal c * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (G z) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
    ((hφ.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hφ0 s (Ioc_subset_Icc_self hs)),
    lintegral_ball_eq_polar_of_continuousOn hG hG0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsub : Ioc a b ⊆ Ioo (0 : ℝ) 1 := fun s hs => ⟨lt_trans ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  calc ∫⁻ s in Ioc a b, ENNReal.ofReal (φ s)
      ≤ ∫⁻ s in Ioc a b, ENNReal.ofReal c * (ENNReal.ofReal s *
          ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, G (polarPt s t))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        have hs0 : 0 < s := lt_trans ha hs.1
        rw [← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_mul hc]
        refine ENNReal.ofReal_le_ofReal ((hφle s (Ioc_subset_Icc_self hs)).trans_eq ?_)
        ring
    _ ≤ _ := lintegral_mono_set hsub

/-- The zero coefficient: `|a_0(R)|² ≤ (16/π) ∫_𝔻 v² + (1/π) ∫_𝔻 |∇v|²` for `1/2 ≤ R < 1`. -/
theorem zero_coeff_trace_le (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) {R : ℝ} (hR : 1 / 2 ≤ R) (hR1 : R < 1) :
    ENNReal.ofReal (‖angCoeff v 0 R‖ ^ 2) ≤
      ENNReal.ofReal (16 / π) * (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (v z ^ 2)) +
      ENNReal.ofReal (1 / π) * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hsubI : ∀ s ∈ Icc (R / 2) R, |s| < 1 := fun s hs => by
    rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.2]
  have hd : ∀ s ∈ Icc (R / 2) R, HasDerivAt (angCoeff v 0) (angDerivCoeff Dv 0 s) s :=
    fun s hs => hasDerivAt_angCoeff hv hDv 0 (hsubI s hs)
  have hdc : ContinuousOn (angDerivCoeff Dv 0) (Icc (R / 2) R) :=
    (continuousOn_angDerivCoeff hDv 0).mono fun s hs => abs_lt.1 (hsubI s hs)
  have hac : ContinuousOn (angCoeff v 0) (Icc (R / 2) R) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have h1d := norm_sq_le_trace_one_dim (by linarith : R / 2 < R) hd hdc
  rw [show R - R / 2 = R / 2 by ring] at h1d
  have hpi := Real.pi_pos
  -- the two interval integrals
  have hI1 : ENNReal.ofReal (∫ s in R / 2..R, ‖angCoeff v 0 s‖ ^ 2) ≤
      ENNReal.ofReal (2 / π) * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (v z ^ 2) := by
    refine ofReal_integral_annulus_le (G := fun z => v z ^ 2) ((continuousOn_v hv).pow 2)
      (fun z => sq_nonneg _) (by linarith) (by linarith) hR1 (by positivity) (hac.norm.pow 2)
      (fun s _ => sq_nonneg _) fun s hs => ?_
    have h := le_hasSum (hasSum_sq_angCoeff hv (hsubI s hs)) 0 (fun n _ => sq_nonneg _)
    have hint : 0 ≤ ∫ t in (0 : ℝ)..2 * π, v (polarPt s t) ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) fun t _ => sq_nonneg _
    have hs4 : 1 ≤ 4 * s := by linarith [hs.1]
    calc ‖angCoeff v 0 s‖ ^ 2 ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, v (polarPt s t) ^ 2 := h
      _ ≤ (2 * π)⁻¹ * (4 * s) * ∫ t in (0 : ℝ)..2 * π, v (polarPt s t) ^ 2 := by
          rw [mul_assoc]; gcongr; nlinarith
      _ = s * (2 / π * ∫ t in (0 : ℝ)..2 * π, v (polarPt s t) ^ 2) := by field_simp; ring
  have hI2 : ENNReal.ofReal (∫ s in R / 2..R, ‖angDerivCoeff Dv 0 s‖ ^ 2) ≤
      ENNReal.ofReal (2 / π) * ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2) := by
    refine ofReal_integral_annulus_le (G := fun z => ‖Dv z‖ ^ 2) (hDv.norm.pow 2)
      (fun z => sq_nonneg _) (by linarith) (by linarith) hR1 (by positivity) (hdc.norm.pow 2)
      (fun s _ => sq_nonneg _) fun s hs => ?_
    have hs' := hsubI s hs
    have h := le_hasSum (hasSum_sq_angDerivCoeff hDv hs') 0 (fun n _ => sq_nonneg _)
    have hcD : Continuous fun t : ℝ => ‖Dv (polarPt s t)‖ ^ 2 :=
      ((hDv.comp_continuous (by unfold polarPt; fun_prop) (polarPt_mem_ball' hs')).norm).pow 2
    have hle : ∫ t in (0 : ℝ)..2 * π, ((Dv (polarPt s t)) (exp (t * I))) ^ 2 ≤
        ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by positivity)
        (((continuous_Dv_polar hDv hs' _ (by fun_prop)).pow 2).intervalIntegrable _ _)
        (hcD.intervalIntegrable _ _) fun t _ =>
          sq_apply_le _ (by rw [Complex.norm_exp_ofReal_mul_I])
    have hint : 0 ≤ ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) fun t _ => sq_nonneg _
    have hs4 : 1 ≤ 4 * s := by linarith [hs.1]
    calc ‖angDerivCoeff Dv 0 s‖ ^ 2
        ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ((Dv (polarPt s t)) (exp (t * I))) ^ 2 := h
      _ ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2 := by gcongr
      _ ≤ (2 * π)⁻¹ * (4 * s) * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2 := by
          rw [mul_assoc]; gcongr; nlinarith
      _ = s * (2 / π * ∫ t in (0 : ℝ)..2 * π, ‖Dv (polarPt s t)‖ ^ 2) := by field_simp; ring
  -- combine
  have hX0 : 0 ≤ ∫ s in R / 2..R, ‖angCoeff v 0 s‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hY0 : 0 ≤ ∫ s in R / 2..R, ‖angDerivCoeff Dv 0 s‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  calc ENNReal.ofReal (‖angCoeff v 0 R‖ ^ 2)
      ≤ ENNReal.ofReal (2 / (R / 2) * (∫ s in R / 2..R, ‖angCoeff v 0 s‖ ^ 2) +
          R / 2 * ∫ s in R / 2..R, ‖angDerivCoeff Dv 0 s‖ ^ 2) := ENNReal.ofReal_le_ofReal h1d
    _ = ENNReal.ofReal (2 / (R / 2)) * ENNReal.ofReal (∫ s in R / 2..R, ‖angCoeff v 0 s‖ ^ 2) +
        ENNReal.ofReal (R / 2) * ENNReal.ofReal (∫ s in R / 2..R, ‖angDerivCoeff Dv 0 s‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (2 / (R / 2)) * (ENNReal.ofReal (2 / π) *
          ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (v z ^ 2)) +
        ENNReal.ofReal (R / 2) * (ENNReal.ofReal (2 / π) *
          ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2)) :=
        add_le_add (mul_le_mul' le_rfl hI1) (mul_le_mul' le_rfl hI2)
    _ ≤ _ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        · rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hpi]; nlinarith
        · rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hpi]; nlinarith

/-- **The disk trace estimate (PU1).** For `v` of class `C¹` on the unit disk and `1/2 ≤ R < 1`,
`∑ (1 + |n|) |a_n(R)|² ≤ 8 (∫_𝔻 v² + ∫_𝔻 |∇v|²)` (finite partial sums). -/
theorem trace_estimate (hv : ∀ z ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv z) z)
    (hDv : ContinuousOn Dv (ball 0 1)) {R : ℝ} (hR : 1 / 2 ≤ R) (hR1 : R < 1) (S : Finset ℤ) :
    ENNReal.ofReal (∑ n ∈ S, (1 + |(n : ℝ)|) * ‖angCoeff v n R‖ ^ 2) ≤
      8 * ((∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (v z ^ 2)) +
        ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2)) := by
  classical
  set A := ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (v z ^ 2)
  set B := ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖Dv z‖ ^ 2)
  have hR0 : 0 < R := by linarith
  have hpi := Real.two_le_pi
  -- pointwise comparison of the summands
  have hterm : ∀ n ∈ S, (1 + |(n : ℝ)|) * ‖angCoeff v n R‖ ^ 2 ≤
      (if n = 0 then ‖angCoeff v 0 R‖ ^ 2 else 0) + 2 * (|(n : ℝ)| * ‖angCoeff v n R‖ ^ 2) := by
    intro n _
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, ↓reduceIte, zero_add]
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      nlinarith [sq_nonneg ‖angCoeff v n R‖]
  have hsum : ∑ n ∈ S, (1 + |(n : ℝ)|) * ‖angCoeff v n R‖ ^ 2 ≤
      ‖angCoeff v 0 R‖ ^ 2 + 2 * ∑ n ∈ S, |(n : ℝ)| * ‖angCoeff v n R‖ ^ 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    gcongr
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp [sq_nonneg]
  have h0 := zero_coeff_trace_le hv hDv hR hR1
  have hh := homogeneous_trace_le hv hDv hR0 hR1 S
  calc ENNReal.ofReal (∑ n ∈ S, (1 + |(n : ℝ)|) * ‖angCoeff v n R‖ ^ 2)
      ≤ ENNReal.ofReal (‖angCoeff v 0 R‖ ^ 2) +
          2 * ENNReal.ofReal (∑ n ∈ S, |(n : ℝ)| * ‖angCoeff v n R‖ ^ 2) := by
        refine (ENNReal.ofReal_le_ofReal hsum).trans ?_
        rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ (ENNReal.ofReal (16 / π) * A + ENNReal.ofReal (1 / π) * B) +
          2 * (ENNReal.ofReal π⁻¹ * B) := add_le_add h0 (mul_le_mul' le_rfl hh)
    _ ≤ 8 * A + 8 * B := by
        have h16 : ENNReal.ofReal (16 / π) ≤ 8 := by
          rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp]
          exact ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ (by linarith)]; nlinarith)
        have h3 : ENNReal.ofReal (1 / π) + 2 * ENNReal.ofReal π⁻¹ ≤ 8 := by
          rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [one_div]
          have : π⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
          nlinarith
        calc (ENNReal.ofReal (16 / π) * A + ENNReal.ofReal (1 / π) * B) + 2 * (ENNReal.ofReal π⁻¹ * B)
            = ENNReal.ofReal (16 / π) * A + (ENNReal.ofReal (1 / π) + 2 * ENNReal.ofReal π⁻¹) * B := by
              ring
          _ ≤ 8 * A + 8 * B := add_le_add (mul_le_mul' h16 le_rfl) (mul_le_mul' h3 le_rfl)
    _ = 8 * (A + B) := by ring

end Trace3

end InteractingSLE.Sec6
