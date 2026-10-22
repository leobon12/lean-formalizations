import HigherDimLQGMetric.Sphere.Avg

/-!
# Logarithmic potentials of growth-bounded measures

Packet F3 (Phase A, block A1), target 3 (first part). MA0 Details (a) D-F3 ("the unit-sphere log
potential `F_{σ₁}` is bounded and continuous on compacts"); blueprint Lemma `lem:potential` (a).

For a finite measure `λ` on `ℝ^d` with a linear small-ball bound `λ(B̄(x, s)) ≤ A s` (all `x`,
`s > 0`) carried by `B̄(0, D)`:

* `logPotM λ x = ∫ log|x - y|⁻¹ dλ(y)` is well defined (`integrable_log_norm_sub_left`);
* `logPotM λ x ≤ A` (HigherDimLFPP's layer-cake bound `FieldAux.lintegral_log_inv_le`) and
  `logPotM λ x ≥ -λ(ℝ^d) log⁺(|x| + D)` (`logPotM_le`, `neg_mul_le_logPotM`);
* `logPotM λ` is continuous (`continuous_logPotM`).

Proof of continuity (own step; the blueprint's "layer-cake bound" made explicit): the truncations
`F_M(x) = ∫ -log max(|x - y|, e^{-M}) dλ(y)` are continuous (dominated convergence, the integrand is
continuous in `x` and bounded by `M + log(|x₀| + D + 2)` near `x₀`), and
`0 ≤ logPotM λ x - F_M(x) = ∫ (log|x - y|⁻¹ - M)⁺ dλ(y) ≤ A e^{-M}` uniformly in `x`
(`λ` has no atoms; shifted layer cake `lintegral_log_inv_sub_le`: the set where
`(log|x - y|⁻¹ - M)⁺ > t` lies in `B̄(x, e^{-M-t})`), so `F_M → logPotM λ` uniformly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The logarithmic potential `x ↦ ∫ log|x - y|⁻¹ dμ(y)` of a measure. -/
def logPotM (μ : Measure (Rd d)) (x : Rd d) : ℝ := ∫ y, -Real.log ‖x - y‖ ∂μ

/-- The mutual logarithmic energy `∫∫ log|x - y|⁻¹ dμ(x) dν(y)`. -/
def logEnergy (μ ν : Measure (Rd d)) : ℝ := ∫ p, -Real.log ‖p.1 - p.2‖ ∂(μ.prod ν)

/-- HigherDimLFPP's `logCov` in terms of mutual energies. -/
theorem logCov_eq_logEnergy (μ ν α β : Measure (Rd d)) :
    HigherDimLFPP.logCov μ ν α β =
      logEnergy μ α - logEnergy μ β - logEnergy ν α + logEnergy ν β := rfl

theorem logEnergy_comm (μ ν : Measure (Rd d)) [SFinite μ] [SFinite ν] :
    logEnergy μ ν = logEnergy ν μ := by
  unfold logEnergy
  rw [← integral_prod_swap]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

section Growth

variable {lam : Measure (Rd d)} [IsFiniteMeasure lam] {A D : ℝ}

/-- A measure with a linear small-ball bound has no atoms. -/
theorem measure_singleton_eq_zero_of_smallBall
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s) (x : Rd d) :
    lam {x} = 0 := by
  have hle : ∀ s > (0 : ℝ), lam.real {x} ≤ A * s := fun s hs =>
    (measureReal_mono (singleton_subset_iff.2 (mem_closedBall_self hs.le))).trans (hball x s hs)
  have h0 : lam.real {x} ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases le_or_gt A 0 with hA | hA
    · have := hle 1 one_pos; nlinarith
    · have := hle (ε / A) (div_pos hε hA)
      rw [mul_div_cancel₀ _ hA.ne'] at this
      linarith
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm h0 measureReal_nonneg)

theorem ae_ne_of_smallBall (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (x : Rd d) : ∀ᵐ y ∂lam, y ≠ x := by
  rw [ae_iff]
  simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
  exact measure_singleton_eq_zero_of_smallBall hball x

/-- `log|x - y|` is `λ`-integrable for every `x`. -/
theorem integrable_log_norm_sub_left (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hD : ∀ᵐ y ∂lam, ‖y‖ ≤ D) (x : Rd d) :
    Integrable (fun y => Real.log ‖x - y‖) lam := by
  have hm : Measurable fun y : Rd d => Real.log ‖x - y‖ :=
    (measurable_const.sub measurable_id).norm.log
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hbd : ∀ᵐ y ∂lam, ‖Real.log ‖x - y‖‖ₑ ≤
      ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) +
        ENNReal.ofReal (max 0 (Real.log (2 * ((‖x‖ + D) / 2)))) := by
    filter_upwards [hD] with y hy
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    refine ENNReal.ofReal_le_ofReal (HigherDimLFPP.FieldAux.abs_log_le (norm_nonneg _) ?_)
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * ((‖x‖ + D) / 2) := by linarith
  calc ∫⁻ y, ‖Real.log ‖x - y‖‖ₑ ∂lam
      ≤ ∫⁻ y, (ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) +
          ENNReal.ofReal (max 0 (Real.log (2 * ((‖x‖ + D) / 2))))) ∂lam := lintegral_mono_ae hbd
    _ = ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂lam +
          ENNReal.ofReal (max 0 (Real.log (2 * ((‖x‖ + D) / 2)))) * lam univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨(HigherDimLFPP.FieldAux.lintegral_log_inv_le hA hball x).trans_lt
          ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

/-- **Upper bound**: `logPotM λ x ≤ A`. -/
theorem logPotM_le (hA : 0 ≤ A) (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hD : ∀ᵐ y ∂lam, ‖y‖ ≤ D) (x : Rd d) : logPotM lam x ≤ A := by
  have hi := (integrable_log_norm_sub_left hA hball hD x).neg
  have hi' : Integrable (fun y => max 0 (-Real.log ‖x - y‖)) lam :=
    (integrable_const 0).sup hi
  have h1 : logPotM lam x ≤ ∫ y, max 0 (-Real.log ‖x - y‖) ∂lam :=
    integral_mono hi hi' fun y => le_max_right _ _
  have h2 : ENNReal.ofReal (∫ y, max 0 (-Real.log ‖x - y‖) ∂lam) ≤ ENNReal.ofReal A := by
    rw [ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun y => le_max_left _ _)]
    exact HigherDimLFPP.FieldAux.lintegral_log_inv_le hA hball x
  exact h1.trans ((ENNReal.ofReal_le_ofReal_iff hA).1 h2)

/-- **Lower bound**: `logPotM λ x ≥ -λ(ℝ^d) log⁺(|x| + D)`. -/
theorem neg_mul_le_logPotM (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hD : ∀ᵐ y ∂lam, ‖y‖ ≤ D) (x : Rd d) :
    -(lam.real univ * max 0 (Real.log (‖x‖ + D))) ≤ logPotM lam x := by
  have hi := (integrable_log_norm_sub_left hA hball hD x).neg
  have hle : ∀ᵐ y ∂lam, -max 0 (Real.log (‖x‖ + D)) ≤ -Real.log ‖x - y‖ := by
    filter_upwards [hD] with y hy
    rw [neg_le_neg_iff]
    rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]; exact le_max_left _ _
    · refine (Real.log_le_log hpos ?_).trans (le_max_right _ _)
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + D := by linarith
  have := integral_mono_ae (integrable_const _) hi hle
  rw [integral_const, smul_eq_mul, mul_neg] at this
  exact this

/-- The shifted layer cake: `∫ (log|x - y|⁻¹ - M)⁺ dλ(y) ≤ A e^{-M}`. -/
theorem lintegral_log_inv_sub_le (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s) (x : Rd d) (M : ℝ) :
    ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖ - M)) ∂lam ≤
      ENNReal.ofReal (A * Real.exp (-M)) := by
  have hm : Measurable fun y : Rd d => max 0 (-Real.log ‖x - y‖ - M) :=
    measurable_const.max (((measurable_const.sub measurable_id).norm.log.neg).sub measurable_const)
  rw [lintegral_eq_lintegral_meas_lt (f := fun y => max 0 (-Real.log ‖x - y‖ - M)) lam
    (Eventually.of_forall fun y => le_max_left _ _) hm.aemeasurable]
  have hsub : ∀ t > (0 : ℝ), {y : Rd d | t < max 0 (-Real.log ‖x - y‖ - M)} ⊆
      closedBall x (Real.exp (-M) * Real.exp (-t)) := by
    intro t ht y hy
    simp only [mem_ofPred_eq] at hy
    have hy' : t < -Real.log ‖x - y‖ - M := by
      rcases le_total 0 (-Real.log ‖x - y‖ - M) with h | h
      · rwa [max_eq_right h] at hy
      · rw [max_eq_left h] at hy
        exact absurd hy (not_lt.2 ht.le)
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev, ← Real.exp_add]
    rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : Real.log ‖x - y‖ < -M + -t := by linarith
      exact ((Real.log_lt_iff_lt_exp hpos).1 this).le
  calc ∫⁻ t in Ioi 0, lam {y | t < max 0 (-Real.log ‖x - y‖ - M)}
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (A * Real.exp (-M) * Real.exp (-t)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        calc lam {y | t < max 0 (-Real.log ‖x - y‖ - M)}
            ≤ lam (closedBall x (Real.exp (-M) * Real.exp (-t))) := measure_mono (hsub t ht)
          _ = ENNReal.ofReal (lam.real (closedBall x (Real.exp (-M) * Real.exp (-t)))) :=
              (ofReal_measureReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (A * Real.exp (-M) * Real.exp (-t)) := by
              rw [mul_assoc]
              exact ENNReal.ofReal_le_ofReal (hball x _ (by positivity))
    _ = ENNReal.ofReal (∫ t in Ioi 0, A * Real.exp (-M) * Real.exp (-t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_neg_Ioi 0).const_mul (A * Real.exp (-M)))]
        exact (ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun t _ => by positivity)
    _ = ENNReal.ofReal (A * Real.exp (-M)) := by
        rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- The truncated potential `F_M(x) = ∫ -log max(|x - y|, e^{-M}) dλ(y)`. -/
def logPotTrunc (lam : Measure (Rd d)) (M : ℝ) (x : Rd d) : ℝ :=
  ∫ y, -Real.log (max ‖x - y‖ (Real.exp (-M))) ∂lam

theorem continuous_logPotTrunc (hD : ∀ᵐ y ∂lam, ‖y‖ ≤ D) {M : ℝ} (hM : 0 ≤ M) :
    Continuous (logPotTrunc lam M) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hcont : ∀ y : Rd d, Continuous fun x : Rd d => -Real.log (max ‖x - y‖ (Real.exp (-M))) :=
    fun y => ((continuous_id.sub continuous_const).norm.max continuous_const).log
      (fun x => (lt_max_of_lt_right (Real.exp_pos _)).ne') |>.neg
  set K : ℝ := M + Real.log (‖x₀‖ + 1 + D + Real.exp (-M) + 1) with hK
  refine continuousAt_of_dominated (bound := fun _ => |K|) ?_ ?_ (integrable_const _)
    (ae_of_all _ fun y => (hcont y).continuousAt)
  · exact Eventually.of_forall fun x =>
      (((continuous_const.sub continuous_id).norm.max continuous_const).log
        (fun y => (lt_max_of_lt_right (Real.exp_pos _)).ne') |>.neg).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards [hD] with y hy
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hx
      calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ ≤ ‖x₀‖ + 1 := by linarith
    have hpos : 0 < max ‖x - y‖ (Real.exp (-M)) := lt_max_of_lt_right (Real.exp_pos _)
    have hlow : Real.exp (-M) ≤ max ‖x - y‖ (Real.exp (-M)) := le_max_right _ _
    have hup : max ‖x - y‖ (Real.exp (-M)) ≤ ‖x₀‖ + 1 + D + Real.exp (-M) + 1 := by
      have : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      have hD0 : 0 ≤ D := (norm_nonneg y).trans hy
      have := Real.exp_pos (-M)
      have := norm_nonneg x₀
      refine max_le (by linarith) (by linarith)
    have h1 : -M ≤ Real.log (max ‖x - y‖ (Real.exp (-M))) := by
      have := Real.log_le_log (Real.exp_pos (-M)) hlow
      rwa [Real.log_exp] at this
    have h2 : Real.log (max ‖x - y‖ (Real.exp (-M))) ≤
        Real.log (‖x₀‖ + 1 + D + Real.exp (-M) + 1) := Real.log_le_log hpos hup
    have h3 : 0 ≤ Real.log (‖x₀‖ + 1 + D + Real.exp (-M) + 1) := by
      refine Real.log_nonneg ?_
      have hD0 : 0 ≤ D := (norm_nonneg y).trans hy
      have := Real.exp_pos (-M)
      have := norm_nonneg x₀
      linarith
    rw [Real.norm_eq_abs, abs_neg]
    refine (abs_le.2 ⟨by linarith, by linarith⟩).trans (le_abs_self K)

/-- **Continuity of the log potential** of a growth-bounded, boundedly supported finite measure. -/
theorem continuous_logPotM (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hD : ∀ᵐ y ∂lam, ‖y‖ ≤ D) : Continuous (logPotM lam) := by
  have hU : TendstoUniformly (fun (M : ℕ) => logPotTrunc lam M) (logPotM lam) atTop := by
    rw [tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun M : ℕ => A * Real.exp (-(M : ℝ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul A
      rw [mul_zero] at this
      exact this
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with M hM x
    have hi : Integrable (fun y => -Real.log ‖x - y‖) lam :=
      (integrable_log_norm_sub_left hA hball hD x).neg
    have hcont : Continuous fun y : Rd d => -Real.log (max ‖x - y‖ (Real.exp (-(M : ℝ)))) :=
      ((continuous_const.sub continuous_id).norm.max continuous_const).log
        (fun y => (lt_max_of_lt_right (Real.exp_pos _)).ne') |>.neg
    have hiT : Integrable (fun y : Rd d => -Real.log (max ‖x - y‖ (Real.exp (-(M : ℝ))))) lam := by
      refine Integrable.mono' (g := fun y => |Real.log ‖x - y‖| + M)
        ((integrable_log_norm_sub_left hA hball hD x).abs.add (integrable_const _))
        hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_neg]
      have hpos : 0 < max ‖x - y‖ (Real.exp (-(M : ℝ))) := lt_max_of_lt_right (Real.exp_pos _)
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      rcases le_total ‖x - y‖ (Real.exp (-(M : ℝ))) with h | h
      · rw [max_eq_right h, Real.log_exp, abs_neg, abs_of_nonneg hM0]
        linarith [abs_nonneg (Real.log ‖x - y‖)]
      · rw [max_eq_left h]
        linarith
    have hpt : ∀ᵐ y ∂lam, -Real.log ‖x - y‖ - -Real.log (max ‖x - y‖ (Real.exp (-(M : ℝ)))) =
        max 0 (-Real.log ‖x - y‖ - M) := by
      filter_upwards [ae_ne_of_smallBall hball x] with y hy
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy))
      rcases le_total ‖x - y‖ (Real.exp (-(M : ℝ))) with h | h
      · rw [max_eq_right h, Real.log_exp]
        have : Real.log ‖x - y‖ ≤ -(M : ℝ) := by
          rw [← Real.log_exp (-(M : ℝ))]; exact Real.log_le_log hpos h
        rw [max_eq_right (by linarith)]
        ring
      · rw [max_eq_left h]
        have : -(M : ℝ) ≤ Real.log ‖x - y‖ := by
          rw [← Real.log_exp (-(M : ℝ))]; exact Real.log_le_log (Real.exp_pos _) h
        rw [max_eq_left (by linarith)]
        ring
    have hdiff : logPotM lam x - logPotTrunc lam M x = ∫ y, max 0 (-Real.log ‖x - y‖ - M) ∂lam := by
      rw [logPotM, logPotTrunc, ← integral_sub hi hiT]
      exact integral_congr_ae hpt
    have hnn : 0 ≤ ∫ y, max 0 (-Real.log ‖x - y‖ - M) ∂lam :=
      integral_nonneg fun y => le_max_left _ _
    have hle : ∫ y, max 0 (-Real.log ‖x - y‖ - M) ∂lam ≤ A * Real.exp (-(M : ℝ)) := by
      have hi' : Integrable (fun y => max 0 (-Real.log ‖x - y‖ - M)) lam := by
        refine (integrable_congr hpt).1 (hi.sub hiT)
      have h2 := lintegral_log_inv_sub_le hA hball x M
      rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun y => le_max_left _ _)] at h2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    rw [Real.dist_eq, hdiff, abs_of_nonneg hnn]
    exact hle.trans_lt hM
  exact hU.continuous (Frequently.of_forall fun M =>
    continuous_logPotTrunc hD (Nat.cast_nonneg M))

end Growth

end HigherDimLQGMetric
