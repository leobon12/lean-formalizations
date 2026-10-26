import HigherDimLFPPAS.Gauss.Variance

/-!
# The increment bound P4.1′ (packet F2b)

For `|t - t'| ≤ 1` and all `x, x'`:
`E (H_t(x) - H_{t'}(x'))² ≤ C₃ (|t - t'| + e^{max(t,t')} ‖x - x'‖)` with `H_t(x) = h ∗ K_{e^{-t}}(x)`
(`exists_integral_sq_convMollify_sub_le_F2b`; planning audit MA3, Details P4.1′). Proof: the radial
formula writes the increment as `∫ w(u) (h_{e^{-t}u}(x) - h_{e^{-t'}u}(x')) du`, Minkowski's
inequality in `L²` (`integral_sq_integral_le_F2b`) and the sphere-average increment bound
`E (h_r(z) - h_s(w))² ≤ C (‖z - w‖ + |r - s|)/min(r, s)`; the weights `|w(u)|` and `|w(u)| u^{-1/2}`
are integrable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The elementary scale estimate: for `|t - t'| ≤ 1`, `u > 0`,
`(X + |e^{-t}u - e^{-t'}u|) / min(e^{-t}u, e^{-t'}u) ≤ 2|t - t'| + e^{max(t,t')} X / u`. -/
lemma scale_ratio_le_F2b {t t' u X : ℝ} (htt : |t - t'| ≤ 1) (hu : 0 < u) :
    (X + |Real.exp (-t) * u - Real.exp (-t') * u|) / min (Real.exp (-t) * u) (Real.exp (-t') * u)
      ≤ 2 * |t - t'| + Real.exp (max t t') * X / u := by
  -- reduce to `t ≤ t'` by symmetry
  wlog hle : t ≤ t' generalizing t t'
  · have h := this (t := t') (t' := t) (by rwa [abs_sub_comm]) (le_of_not_ge hle)
    rw [abs_sub_comm t' t, abs_sub_comm (Real.exp (-t') * u), min_comm, max_comm] at h
    exact h
  have hδ : 0 ≤ t' - t := by linarith
  have hδ1 : |t' - t| ≤ 1 := by rwa [abs_sub_comm]
  have hm : Real.exp (-t') ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have hmin : min (Real.exp (-t) * u) (Real.exp (-t') * u) = Real.exp (-t') * u :=
    min_eq_right (mul_le_mul_of_nonneg_right hm hu.le)
  have hsplit : Real.exp (-t) = Real.exp (-t') * Real.exp (t' - t) := by
    rw [← Real.exp_add]
    ring_nf
  have habs : |Real.exp (-t) * u - Real.exp (-t') * u| =
      Real.exp (-t') * u * (Real.exp (t' - t) - 1) := by
    rw [hsplit]
    have h1 : 1 ≤ Real.exp (t' - t) := Real.one_le_exp hδ
    rw [abs_of_nonneg (by nlinarith [Real.exp_pos (-t')])]
    ring
  have hexp : Real.exp (t' - t) - 1 ≤ 2 * |t - t'| := by
    have h := Real.abs_exp_sub_one_le hδ1
    rw [abs_sub_comm t' t] at h
    exact (le_abs_self _).trans h
  have hpos : 0 < Real.exp (-t') * u := mul_pos (Real.exp_pos _) hu
  have hinv : Real.exp (max t t') * Real.exp (-t') = 1 := by
    rw [max_eq_right hle, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hmin, habs, div_le_iff₀ hpos]
  have hkey : Real.exp (max t t') * X / u * (Real.exp (-t') * u) = X := by
    calc Real.exp (max t t') * X / u * (Real.exp (-t') * u)
        = (Real.exp (max t t') * Real.exp (-t')) * X * (u / u) := by ring
      _ = X := by rw [hinv, div_self hu.ne']; ring
  have h2 : Real.exp (-t') * u * (Real.exp (t' - t) - 1) ≤ 2 * |t - t'| * (Real.exp (-t') * u) := by
    rw [mul_comm (2 * |t - t'|)]
    exact mul_le_mul_of_nonneg_left hexp hpos.le
  nlinarith [hkey, h2]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- **P4.1′** (planning audit MA3, Details P4.1′): for `|t - t'| ≤ 1` and all `x, x'`,
`E (H_t(x) - H_{t'}(x'))² ≤ C₃ (|t - t'| + e^{max(t,t')} ‖x - x'‖)`, `H_t(x) = h ∗ K_{e^{-t}}(x)`. -/
theorem exists_integral_sq_convMollify_sub_le_F2b (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ t t' : ℝ, |t - t'| ≤ 1 → ∀ x x' : Rd d,
        ∫ ω, (convMollify κ (Real.exp (-t)) (h ω) x -
            convMollify κ (Real.exp (-t')) (h ω) x') ^ 2 ∂P ≤
          C₃ * (|t - t'| + Real.exp (max t t') * ‖x - x'‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphereAvg_sub_le_F2b hd
  set μp : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμp
  set k₀ : ℝ := ∫ u, |radWeightF2b κ u| ∂μp with hk₀
  set k₁ : ℝ := ∫ u, |radWeightF2b κ u| * u ^ (-(1 / 2 : ℝ)) ∂μp with hk₁
  have hk₀0 : 0 ≤ k₀ := integral_nonneg fun u => abs_nonneg _
  have hw0 : Integrable (fun u => |radWeightF2b κ u|) μp := integrableOn_abs_radWeightF2b hd hκ
  have hw1 : Integrable (fun u => |radWeightF2b κ u| * u ^ (-(1 / 2 : ℝ))) μp :=
    integrableOn_radWeightF2b_rpow hd hκ
  refine ⟨4 * C * k₀ ^ 2 + 2 * C * k₁ ^ 2, by positivity,
    fun {Ω} _ {P} _ {h} hh t t' htt x x' => ?_⟩
  set ε : ℝ := Real.exp (-t) with hεdef
  set ε' : ℝ := Real.exp (-t') with hε'def
  have hε : 0 < ε := Real.exp_pos _
  have hε' : 0 < ε' := Real.exp_pos _
  set Y := sphScaleF2b h ε x with hY
  set Y' := sphScaleF2b h ε' x' with hY'
  let Δ : Ω → ℝ → ℝ := fun ω u => Y ω u - Y' ω u
  have hwm := measurable_radWeightF2b hd hκ
  have hYm : Measurable fun q : Ω × ℝ => Y q.1 q.2 := measurable_sphScaleF2b hh ε x
  have hY'm : Measurable fun q : Ω × ℝ => Y' q.1 q.2 := measurable_sphScaleF2b hh ε' x'
  have hΔm : Measurable fun q : Ω × ℝ => Δ q.1 q.2 := hYm.sub hY'm
  have hΔ2 : ∀ᵐ u ∂μp, MemLp (fun ω => Δ ω u) 2 P := by
    filter_upwards [ae_memLp_sphScaleF2b hd hh hε x, ae_memLp_sphScaleF2b hd hh hε' x']
      with u h1 h2
    exact h1.sub h2
  -- the almost-sure radial representation of the increment
  have hae : (fun ω => (convMollify κ ε (h ω) x - convMollify κ ε' (h ω) x') ^ 2) =ᵐ[P]
      fun ω => (∫ u, radWeightF2b κ u * Δ ω u ∂μp) ^ 2 := by
    filter_upwards [ae_convMollify_eq_radial_F2b hd hκ hh hε x,
      ae_convMollify_eq_radial_F2b hd hκ hh hε' x',
      ae_integrable_mul_F2b hwm hYm (ae_memLp_sphScaleF2b hd hh hε x)
        (integrable_radWeight_l2Sec_F2b hd hκ hh hε x),
      ae_integrable_mul_F2b hwm hY'm (ae_memLp_sphScaleF2b hd hh hε' x')
        (integrable_radWeight_l2Sec_F2b hd hκ hh hε' x')] with ω h1 h2 hi1 hi2
    rw [h1, h2, ← integral_sub hi1 hi2]
    congr 2
    funext u
    simp only [Δ, mul_sub]
  rw [integral_congr_ae hae]
  -- the section norms of the increment process
  set a : ℝ := √(2 * C * |t - t'|) with ha
  set b : ℝ := √(C * Real.exp (max t t') * ‖x - x'‖) with hb
  have hsec : ∀ u : ℝ, 0 < u → l2SecF2b P Δ u ≤ a + b * u ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    have hinc := hC hh.1 (mul_pos hε hu) (mul_pos hε' hu) x x'
    have hratio := scale_ratio_le_F2b (X := ‖x - x'‖) htt hu
    have hle : ∫ ω, Δ ω u ^ 2 ∂P ≤ 2 * C * |t - t'| + C * Real.exp (max t t') * ‖x - x'‖ / u := by
      refine hinc.trans ?_
      rw [mul_div_assoc]
      calc C * ((‖x - x'‖ + |ε * u - ε' * u|) / min (ε * u) (ε' * u))
          ≤ C * (2 * |t - t'| + Real.exp (max t t') * ‖x - x'‖ / u) :=
            mul_le_mul_of_nonneg_left hratio hC0
        _ = 2 * C * |t - t'| + C * Real.exp (max t t') * ‖x - x'‖ / u := by ring
    have hA0 : 0 ≤ 2 * C * |t - t'| := by positivity
    have hB0 : 0 ≤ C * Real.exp (max t t') * ‖x - x'‖ / u := by positivity
    unfold l2SecF2b
    refine (Real.sqrt_le_sqrt hle).trans ((sqrt_add_le_F2b hA0 hB0).trans (le_of_eq ?_))
    rw [Real.sqrt_div' _ hu.le, div_eq_mul_inv, Real.sqrt_eq_rpow u, ← Real.rpow_neg hu.le]
  have hdom : Integrable (fun u => |radWeightF2b κ u| * (a + b * u ^ (-(1 / 2 : ℝ)))) μp := by
    refine ((hw0.const_mul a).add (hw1.const_mul b)).congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hΔint : Integrable (fun u => |radWeightF2b κ u| * l2SecF2b P Δ u) μp := by
    refine hdom.mono' ?_ ?_
    · exact (((continuous_radWeightF2b hd hκ).abs.measurable).mul
        (measurable_l2SecF2b hΔm)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (l2SecF2b_nonneg P Δ u)]
      exact mul_le_mul_of_nonneg_left (hsec u hu) (abs_nonneg _)
  have hmink := integral_sq_integral_le_F2b hwm hΔm hΔ2 hΔint
  refine hmink.trans ?_
  have hS : ∫ u, |radWeightF2b κ u| * l2SecF2b P Δ u ∂μp ≤ a * k₀ + b * k₁ := by
    have hval : ∫ u, |radWeightF2b κ u| * (a + b * u ^ (-(1 / 2 : ℝ))) ∂μp = a * k₀ + b * k₁ := by
      have he : (fun u => |radWeightF2b κ u| * (a + b * u ^ (-(1 / 2 : ℝ)))) =
          fun u => a * |radWeightF2b κ u| + b * (|radWeightF2b κ u| * u ^ (-(1 / 2 : ℝ))) := by
        funext u
        ring
      rw [he, integral_add (hw0.const_mul a) (hw1.const_mul b), integral_const_mul,
        integral_const_mul]
    rw [← hval]
    refine integral_mono_ae hΔint hdom ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    exact mul_le_mul_of_nonneg_left (hsec u hu) (abs_nonneg _)
  have hS0 : 0 ≤ ∫ u, |radWeightF2b κ u| * l2SecF2b P Δ u ∂μp :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (l2SecF2b_nonneg P Δ u)
  have ha2 : a ^ 2 = 2 * C * |t - t'| := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = C * Real.exp (max t t') * ‖x - x'‖ := Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ C * k₀ ^ 2 * (Real.exp (max t t') * ‖x - x'‖) := by positivity
  have hx1 : 0 ≤ C * k₁ ^ 2 * |t - t'| := by positivity
  calc (∫ u, |radWeightF2b κ u| * l2SecF2b P Δ u ∂μp) ^ 2
      ≤ (a * k₀ + b * k₁) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    _ ≤ 2 * (a ^ 2 * k₀ ^ 2) + 2 * (b ^ 2 * k₁ ^ 2) := by
        nlinarith [sq_nonneg (a * k₀ - b * k₁)]
    _ = 4 * C * k₀ ^ 2 * |t - t'| + 2 * C * k₁ ^ 2 * (Real.exp (max t t') * ‖x - x'‖) := by
        rw [ha2, hb2]
        ring
    _ ≤ (4 * C * k₀ ^ 2 + 2 * C * k₁ ^ 2) * (|t - t'| + Real.exp (max t t') * ‖x - x'‖) := by
        nlinarith [hx0, hx1]

end HigherDimLFPPAS.Gauss
