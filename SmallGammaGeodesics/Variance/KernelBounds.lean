import GaussianLQG.Energy.LogPotential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Elementary kernel bounds for the four-kernel lemma (packet P-A4)

Source: `source/small-parameter-lqg-geodesics.pdf`, §3, proof of Lemma 3.1 (and (5.5)).
Mathematics: planning audit GA2, "Details for later use", D1 (Lemma FK). The three analytic inputs
of the four-kernel lemma, none of which mentions measures on `ℂ`:

* `fourKernel_pointwise`: the pointwise bound of the four-kernel combination
  `Φ = K(p,q) - K(p,v) - K(t,q) + K(t,v)`, `K(z,w) = -log|z-w|`, for `|p - t|, |q - v| ≤ r`:
  `Φ ≤ 1_{|t-v| ≤ 4r} 2 log 2 + (17/8) r²/(r² + |t-v|²) + log⁺(r/|p-q|) + log⁺(r/|t-v|)`.
  It follows from the **cross-ratio identity** `(p-v)(t-q) = (p-q)(t-v) + (p-t)(v-q)`, which gives
  `Φ ≤ log(1 + r²/(|p-q| |t-v|))`. This replaces GA2's mixed-Hessian argument in the far region
  and its kernel splitting in the near region (same estimates, no derivatives).
* `integral_far_kernel_le`: `∫₀¹ r²/(r² + (t-v)²) dv ≤ π r` (antiderivative `r arctan((v-t)/r)`).
* `lintegral_min_exp_le`: `∫₀^∞ min{K, B e^{-sa}} da ≤ (K/s)(1 + log⁺(B/K))` (layer cake of
  D1 (iii)).
* `lintegral_posLog_div_le_of_minBound`: the layer cake of D1 step 3 (iii) for a measure with
  `ν(B_u(z)) ≤ min{A u^s, c₁ u + K}`, `0 < u ≤ 1`:
  `∫ log⁺(r/|z-w|) dν(w) ≤ c₁ r + (K/s)(1 + log⁺ A + log⁺(1/K))` for `0 < r ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Real

namespace SmallGammaGeodesics

/-! ## Elementary logarithm inequalities -/

/-- `log(1 + x) ≤ log 2 + log⁺ x` for `x ≥ 0`. -/
theorem log_one_add_le_log_two_add_posLog {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ Real.log 2 + log⁺ x := by
  rcases le_or_gt x 1 with h1 | h1
  · have : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith [Real.posLog_nonneg (x := x)]
  · have hx0 : 0 < x := by linarith
    have h2 : Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h2
    have h3 : log⁺ x = Real.log x := Real.posLog_eq_log (by rw [abs_of_pos hx0]; exact h1.le)
    linarith

/-- `log⁺(A r^s / K) ≤ log⁺ A + log⁺(1/K)` for `0 ≤ r ≤ 1`, `0 ≤ s`. -/
theorem posLog_mul_rpow_div_le {A r s K : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) :
    log⁺ (A * r ^ s / K) ≤ log⁺ A + log⁺ (1 / K) := by
  have hrs0 : 0 ≤ r ^ s := Real.rpow_nonneg hr s
  have hrs1 : r ^ s ≤ 1 := Real.rpow_le_one hr hr1 hs
  have h0 : log⁺ (r ^ s) = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg hrs0]
    exact hrs1
  calc log⁺ (A * r ^ s / K) = log⁺ (A * r ^ s * (1 / K)) := by rw [mul_one_div]
    _ ≤ log⁺ (A * r ^ s) + log⁺ (1 / K) := Real.posLog_mul
    _ ≤ log⁺ A + log⁺ (r ^ s) + log⁺ (1 / K) := by gcongr; exact Real.posLog_mul
    _ = log⁺ A + log⁺ (1 / K) := by rw [h0, add_zero]

/-! ## The pointwise four-kernel bound -/

/-- The cross-ratio identity `(p - v)(t - q) = (p - q)(t - v) + (p - t)(v - q)`. -/
theorem cross_ratio_identity (p q t v : ℂ) :
    (p - v) * (t - q) = (p - q) * (t - v) + (p - t) * (v - q) := by
  ring

/-- `Φ ≤ log(1 + r²/(|p-q||t-v|))` where `Φ = K(p,q) - K(p,v) - K(t,q) + K(t,v)`,
`K(z,w) = -log|z-w|`, provided `|p - t| ≤ r`, `|q - v| ≤ r` and the four points are pairwise
distinct as needed. -/
theorem fourKernel_le_log_cross {p q t v : ℂ} {r : ℝ} (hpq : p ≠ q) (hpv : p ≠ v) (htq : t ≠ q)
    (htv : t ≠ v) (hpt : ‖p - t‖ ≤ r) (hqv : ‖q - v‖ ≤ r) :
    -Real.log ‖p - q‖ - -Real.log ‖p - v‖ - -Real.log ‖t - q‖ + -Real.log ‖t - v‖ ≤
      Real.log (1 + r ^ 2 / (‖p - q‖ * ‖t - v‖)) := by
  have ha : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
  have hb : 0 < ‖p - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hpv)
  have hc : 0 < ‖t - q‖ := norm_pos_iff.2 (sub_ne_zero.2 htq)
  have he : 0 < ‖t - v‖ := norm_pos_iff.2 (sub_ne_zero.2 htv)
  have hX : 0 < ‖p - q‖ * ‖t - v‖ := mul_pos ha he
  have hY : 0 < ‖p - v‖ * ‖t - q‖ := mul_pos hb hc
  -- `|p - v| |t - q| ≤ |p - q| |t - v| + r²`
  have hYX : ‖p - v‖ * ‖t - q‖ ≤ ‖p - q‖ * ‖t - v‖ + r ^ 2 := by
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hpt
    calc ‖p - v‖ * ‖t - q‖ = ‖(p - v) * (t - q)‖ := (norm_mul _ _).symm
      _ = ‖(p - q) * (t - v) + (p - t) * (v - q)‖ := by rw [cross_ratio_identity]
      _ ≤ ‖(p - q) * (t - v)‖ + ‖(p - t) * (v - q)‖ := norm_add_le _ _
      _ = ‖p - q‖ * ‖t - v‖ + ‖p - t‖ * ‖q - v‖ := by
          rw [norm_mul, norm_mul, norm_sub_rev v q]
      _ ≤ ‖p - q‖ * ‖t - v‖ + r * r := by
          gcongr
      _ = ‖p - q‖ * ‖t - v‖ + r ^ 2 := by ring
  have hlhs : -Real.log ‖p - q‖ - -Real.log ‖p - v‖ - -Real.log ‖t - q‖ + -Real.log ‖t - v‖ =
      Real.log (‖p - v‖ * ‖t - q‖) - Real.log (‖p - q‖ * ‖t - v‖) := by
    rw [Real.log_mul hb.ne' hc.ne', Real.log_mul ha.ne' he.ne']
    ring
  have hrhs : Real.log (1 + r ^ 2 / (‖p - q‖ * ‖t - v‖)) =
      Real.log (‖p - q‖ * ‖t - v‖ + r ^ 2) - Real.log (‖p - q‖ * ‖t - v‖) := by
    rw [← Real.log_div (by positivity) hX.ne']
    congr 1
    field_simp
  rw [hlhs, hrhs]
  have := Real.log_le_log hY hYX
  linarith

/-- **Pointwise four-kernel bound.** For `|p - t| ≤ r`, `|q - v| ≤ r` (`r > 0`) and pairwise
distinct points as needed, `Φ = K(p,q) - K(p,v) - K(t,q) + K(t,v)` with `K = -log|·-·|`
satisfies
`Φ ≤ 1_{|t-v| ≤ 4r} 2 log 2 + (17/8) r²/(r² + |t-v|²) + log⁺(r/|p-q|) + log⁺(r/|t-v|)`.

Far region `|t-v| > 4r`: `|p-q| ≥ |t-v|/2`, so
`Φ ≤ r²/(|p-q||t-v|) ≤ 2r²/|t-v|² ≤ (17/8)r²/(r²+|t-v|²)`.
Near region: `1 + r²/(ab) ≤ (1 + r/a)(1 + r/b)` and `log(1+x) ≤ log 2 + log⁺ x`. -/
theorem fourKernel_pointwise {p q t v : ℂ} {r : ℝ} (hr : 0 < r) (hpq : p ≠ q) (hpv : p ≠ v)
    (htq : t ≠ q) (htv : t ≠ v) (hpt : ‖p - t‖ ≤ r) (hqv : ‖q - v‖ ≤ r) :
    -Real.log ‖p - q‖ - -Real.log ‖p - v‖ - -Real.log ‖t - q‖ + -Real.log ‖t - v‖ ≤
      (if ‖t - v‖ ≤ 4 * r then 2 * Real.log 2 else 0) +
        17 / 8 * (r ^ 2 / (r ^ 2 + ‖t - v‖ ^ 2)) + log⁺ (r / ‖p - q‖) + log⁺ (r / ‖t - v‖) := by
  have ha : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
  have he : 0 < ‖t - v‖ := norm_pos_iff.2 (sub_ne_zero.2 htv)
  have hX : 0 < ‖p - q‖ * ‖t - v‖ := mul_pos ha he
  have hmain := fourKernel_le_log_cross hpq hpv htq htv hpt hqv
  have hP1 : 0 ≤ log⁺ (r / ‖p - q‖) := Real.posLog_nonneg
  have hP2 : 0 ≤ log⁺ (r / ‖t - v‖) := Real.posLog_nonneg
  have hF : 0 ≤ 17 / 8 * (r ^ 2 / (r ^ 2 + ‖t - v‖ ^ 2)) := by positivity
  split_ifs with hnear
  · -- near region
    have hprod : 1 + r ^ 2 / (‖p - q‖ * ‖t - v‖) ≤ (1 + r / ‖p - q‖) * (1 + r / ‖t - v‖) := by
      have e : (1 + r / ‖p - q‖) * (1 + r / ‖t - v‖) =
          1 + r ^ 2 / (‖p - q‖ * ‖t - v‖) + (r / ‖p - q‖ + r / ‖t - v‖) := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ r / ‖p - q‖ + r / ‖t - v‖ := by positivity
      linarith
    have hlog : Real.log (1 + r ^ 2 / (‖p - q‖ * ‖t - v‖)) ≤
        Real.log (1 + r / ‖p - q‖) + Real.log (1 + r / ‖t - v‖) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) hprod
    have h1 := log_one_add_le_log_two_add_posLog (x := r / ‖p - q‖) (by positivity)
    have h2 := log_one_add_le_log_two_add_posLog (x := r / ‖t - v‖) (by positivity)
    linarith
  · -- far region
    push Not at hnear
    have hpq_ge : ‖t - v‖ / 2 ≤ ‖p - q‖ := by
      have tri : ‖t - v‖ ≤ ‖p - t‖ + ‖p - q‖ + ‖q - v‖ := by
        calc ‖t - v‖ = ‖-(p - t) + (p - q) + (q - v)‖ := by ring_nf
          _ ≤ ‖-(p - t) + (p - q)‖ + ‖q - v‖ := norm_add_le _ _
          _ ≤ ‖-(p - t)‖ + ‖p - q‖ + ‖q - v‖ := by gcongr; exact norm_add_le _ _
          _ = ‖p - t‖ + ‖p - q‖ + ‖q - v‖ := by rw [norm_neg]
      linarith
    have hX2 : ‖t - v‖ ^ 2 / 2 ≤ ‖p - q‖ * ‖t - v‖ := by
      have := mul_le_mul_of_nonneg_right hpq_ge he.le
      nlinarith
    have hlog : Real.log (1 + r ^ 2 / (‖p - q‖ * ‖t - v‖)) ≤ r ^ 2 / (‖p - q‖ * ‖t - v‖) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + r ^ 2 / (‖p - q‖ * ‖t - v‖)) (by positivity)
      linarith
    have hfar1 : r ^ 2 / (‖p - q‖ * ‖t - v‖) ≤ 2 * r ^ 2 / ‖t - v‖ ^ 2 := by
      rw [div_le_div_iff₀ hX (by positivity)]
      nlinarith
    have hfar2 : 2 * r ^ 2 / ‖t - v‖ ^ 2 ≤ 17 / 8 * (r ^ 2 / (r ^ 2 + ‖t - v‖ ^ 2)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have h16 : 16 * r ^ 2 ≤ ‖t - v‖ ^ 2 := by nlinarith
      nlinarith
    linarith

/-! ## The far-field integral -/

/-- `∫₀¹ r²/(r² + (t-v)²) dv ≤ π r` for every `t ∈ ℝ` and `r > 0`. -/
theorem integral_far_kernel_le (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ v in Icc (0 : ℝ) 1, r ^ 2 / (r ^ 2 + (t - v) ^ 2) ≤ π * r := by
  have hcont : Continuous fun v : ℝ => r ^ 2 / (r ^ 2 + (t - v) ^ 2) :=
    Continuous.div continuous_const (by fun_prop) fun v => by positivity
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v => r * Real.arctan ((v - t) / r)) (r ^ 2 / (r ^ 2 + (t - v) ^ 2)) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => (v - t) / r) (1 / r) v :=
      ((hasDerivAt_id v).sub_const t).div_const r
    have h2 := ((Real.hasDerivAt_arctan ((v - t) / r)).comp v h1).const_mul r
    have hr0 : r ≠ 0 := hr.ne'
    have hden : r ^ 2 + (t - v) ^ 2 ≠ 0 := by positivity
    have e : r * (1 / (1 + ((v - t) / r) ^ 2) * (1 / r)) = r ^ 2 / (r ^ 2 + (t - v) ^ 2) := by
      rw [div_pow, eq_div_iff hden]
      field_simp
      ring
    rw [e] at h2
    exact h2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  have a1 := Real.arctan_lt_pi_div_two ((1 - t) / r)
  have a2 := Real.neg_pi_div_two_lt_arctan ((0 - t) / r)
  have : r * Real.arctan ((1 - t) / r) - r * Real.arctan ((0 - t) / r) =
      r * (Real.arctan ((1 - t) / r) - Real.arctan ((0 - t) / r)) := by ring
  rw [this]
  have hlt : Real.arctan ((1 - t) / r) - Real.arctan ((0 - t) / r) ≤ π := by linarith
  calc r * (Real.arctan ((1 - t) / r) - Real.arctan ((0 - t) / r)) ≤ r * π :=
        mul_le_mul_of_nonneg_left hlt hr.le
    _ = π * r := mul_comm r π

/-! ## Layer cake with a two-regime ball bound -/

/-- `∫_c^∞ B e^{-s a} da = (B/s) e^{-s c}` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_mul_exp_neg_Ioi {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (c : ℝ) :
    ∫⁻ a in Ioi c, ENNReal.ofReal (B * Real.exp (-s * a)) =
      ENNReal.ofReal (B / s * Real.exp (-s * c)) := by
  have hint : IntegrableOn (fun a => B * Real.exp (-s * a)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => by positivity),
    integral_const_mul, integral_exp_mul_Ioi (by linarith) c]
  congr 1
  field_simp

/-- `B e^{-log⁺(B/K)} ≤ K` for `B ≥ 0`, `K > 0`. -/
theorem mul_exp_neg_posLog_div_le {B K : ℝ} (hB : 0 ≤ B) (hK : 0 < K) :
    B * Real.exp (-log⁺ (B / K)) ≤ K := by
  rcases le_or_gt B K with h | h
  · have h0 : log⁺ (B / K) = 0 := by
      rw [Real.posLog_eq_zero_iff, abs_of_nonneg (div_nonneg hB hK.le)]
      exact (div_le_one hK).2 h
    rw [h0, neg_zero, Real.exp_zero, mul_one]
    exact h
  · have hBK : 1 ≤ B / K := (one_le_div hK).2 h.le
    have hB0 : 0 < B := hK.trans h
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact hBK), Real.exp_neg,
      Real.exp_log (div_pos hB0 hK), inv_div]
    field_simp
    exact le_refl _

/-- **Layer cake for `min{K, B e^{-s a}}`** (GA2 D1, step 3 (iii)):
`∫₀^∞ min{K, B e^{-s a}} da ≤ (K/s)(1 + log⁺(B/K))` for `K, B ≥ 0` and `s > 0`
(the right side is `0` when `K = 0`). -/
theorem lintegral_min_exp_le {K B s : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hs : 0 < s) :
    ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (min K (B * Real.exp (-s * a))) ≤
      ENNReal.ofReal (K / s * (1 + log⁺ (B / K))) := by
  rcases hK.eq_or_lt with hK0 | hKpos
  · -- `K = 0`: the integrand vanishes
    subst hK0
    have h0 : ∀ a : ℝ, ENNReal.ofReal (min 0 (B * Real.exp (-s * a))) = 0 := fun a => by
      rw [min_eq_left (by positivity), ENNReal.ofReal_zero]
    simp only [h0, lintegral_zero, zero_le]
  set a₀ := log⁺ (B / K) / s with ha₀
  have ha₀0 : 0 ≤ a₀ := div_nonneg Real.posLog_nonneg hs.le
  have hcover : Ioi (0 : ℝ) ⊆ Ioc 0 a₀ ∪ Ioi a₀ := by
    intro a ha
    rcases le_or_gt a a₀ with h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr h
  have htail : B / s * Real.exp (-s * a₀) ≤ K / s := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
    have : -s * a₀ = -log⁺ (B / K) := by rw [ha₀]; field_simp
    rw [this]
    exact mul_exp_neg_posLog_div_le hB hKpos
  calc ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (min K (B * Real.exp (-s * a)))
      ≤ ∫⁻ a in Ioc 0 a₀ ∪ Ioi a₀, ENNReal.ofReal (min K (B * Real.exp (-s * a))) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ a in Ioc 0 a₀, ENNReal.ofReal (min K (B * Real.exp (-s * a)))) +
          ∫⁻ a in Ioi a₀, ENNReal.ofReal (min K (B * Real.exp (-s * a))) :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ _ in Ioc 0 a₀, ENNReal.ofReal K) +
          ∫⁻ a in Ioi a₀, ENNReal.ofReal (B * Real.exp (-s * a)) := by
        gcongr with a a
        · exact min_le_left _ _
        · exact min_le_right _ _
    _ = ENNReal.ofReal (K * a₀) + ENNReal.ofReal (B / s * Real.exp (-s * a₀)) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, lintegral_ofReal_mul_exp_neg_Ioi hB hs,
          ← ENNReal.ofReal_mul hK]
    _ ≤ ENNReal.ofReal (K * a₀) + ENNReal.ofReal (K / s) := by
        gcongr
    _ = ENNReal.ofReal (K / s * (1 + log⁺ (B / K))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [ha₀]
        ring

/-- **Layer cake of GA2 D1 step 3 (iii).** If `ν(B_u(z)) ≤ min{A u^s, c₁ u + K}` for
`0 < u ≤ 1`, then for `0 < r ≤ 1`,
`∫ log⁺(r/|z-w|) dν(w) ≤ c₁ r + (K/s)(1 + log⁺ A + log⁺(1/K))`. -/
theorem lintegral_posLog_div_le_of_minBound (ν : Measure ℂ) [IsFiniteMeasure ν] (z : ℂ)
    {r A s c₁ K : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (hs : 0 < s) (hc₁ : 0 ≤ c₁)
    (hK : 0 ≤ K)
    (hb : ∀ u : ℝ, 0 < u → u ≤ 1 → (ν (ball z u)).toReal ≤ min (A * u ^ s) (c₁ * u + K)) :
    ∫⁻ w, ENNReal.ofReal (log⁺ (r / ‖z - w‖)) ∂ν ≤
      ENNReal.ofReal (c₁ * r) + ENNReal.ofReal (K / s * (1 + log⁺ A + log⁺ (1 / K))) := by
  have hrs : 0 ≤ A * r ^ s := mul_nonneg hA (Real.rpow_nonneg hr.le s)
  have hg : ∀ a : ℝ, 0 < a → ν (ball z (r * Real.exp (-a))) ≤
      ENNReal.ofReal (c₁ * r * Real.exp (-1 * a)) +
        ENNReal.ofReal (min K (A * r ^ s * Real.exp (-s * a))) := by
    intro a ha
    have hu : 0 < r * Real.exp (-a) := mul_pos hr (Real.exp_pos _)
    have hu1 : r * Real.exp (-a) ≤ 1 := by
      have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc r * Real.exp (-a) ≤ 1 * 1 := mul_le_mul hr1 he (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have hpow : A * (r * Real.exp (-a)) ^ s = A * r ^ s * Real.exp (-s * a) := by
      rw [Real.mul_rpow hr.le (Real.exp_pos _).le, ← Real.exp_mul,
        show -a * s = -s * a by ring, mul_assoc]
    have h1 := hb _ hu hu1
    rw [hpow] at h1
    have hsplit : min (A * r ^ s * Real.exp (-s * a)) (c₁ * (r * Real.exp (-a)) + K) ≤
        c₁ * r * Real.exp (-1 * a) + min K (A * r ^ s * Real.exp (-s * a)) := by
      have hc : 0 ≤ c₁ * r * Real.exp (-1 * a) := by positivity
      have e : c₁ * (r * Real.exp (-a)) = c₁ * r * Real.exp (-1 * a) := by
        rw [neg_one_mul, mul_assoc]
      rw [e]
      rcases le_total K (A * r ^ s * Real.exp (-s * a)) with hk | hk
      · rw [min_eq_left hk]
        exact min_le_right _ _
      · rw [min_eq_right hk]
        linarith [min_le_left (A * r ^ s * Real.exp (-s * a)) (c₁ * r * Real.exp (-1 * a) + K)]
    calc ν (ball z (r * Real.exp (-a))) = ENNReal.ofReal (ν (ball z (r * Real.exp (-a)))).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (c₁ * r * Real.exp (-1 * a) + min K (A * r ^ s * Real.exp (-s * a))) :=
          ENNReal.ofReal_le_ofReal (h1.trans hsplit)
      _ ≤ _ := ENNReal.ofReal_add_le
  refine (GaussianLQG.lintegral_posLog_div_le ν z hr hg).trans ?_
  have hmeas : Measurable fun a : ℝ => ENNReal.ofReal (c₁ * r * Real.exp (-1 * a)) := by
    fun_prop
  rw [lintegral_add_left hmeas,
    GaussianLQG.lintegral_ofReal_mul_exp_Ioi (by positivity) one_pos, div_one]
  gcongr
  refine (lintegral_min_exp_le hK hrs hs).trans (ENNReal.ofReal_le_ofReal ?_)
  have hl := posLog_mul_rpow_div_le (A := A) (K := K) hr.le hr1 hs.le
  have hKs : 0 ≤ K / s := div_nonneg hK hs.le
  have : 1 + log⁺ (A * r ^ s / K) ≤ 1 + log⁺ A + log⁺ (1 / K) := by linarith
  exact mul_le_mul_of_nonneg_left this hKs

end SmallGammaGeodesics
