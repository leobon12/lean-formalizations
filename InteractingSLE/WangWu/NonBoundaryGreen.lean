/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.GrowthVariance
import QuantumZipper.Proofs.GFF.K3.C5Kernel
import QuantumZipper.Proofs.Zipper.B5VHccZero

/-!
# Continuity of Green-dominated quadratic forms (Wang–Wu Corollary 4.23, covariance step)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.5, proof of Corollary 4.23
(text dump lines 1779–1815): "Their conditional covariances tend to `Q_{D∖A}(p, p)` by dominated convergence, using
`G_{D∖A} ≤ G_D` and the locally integrable logarithmic singularity."

For a kernel `G` on `ℍ × ℍ` with `0 ≤ G ≤ G_ℍ` off the diagonal (e.g. the retained Green kernel `retainedGreen` of
the full level-line coupling), the form `Q_G(f) = ∫∫ f(a) G(a, b) f(b)` is quantitatively continuous: if `φ` and
`f` are bounded by `B`, vanish off `ℍ ∩ B̄(0, R)` and agree off a set `U`, then
`|Q_G(φ) − Q_G(f)| ≤ 128 π R² B² |U|`. The proof bounds `G_ℍ(a, b) ≤ log(4R/|a − b|)` on `B̄(0, R)` and uses
`∫_{B(x, ρ)} log(ρ/|y − x|) dy ≤ 2πρ²` (`lintegral_ball_log_div_norm_sub_le`).

## Main results

* `greenForm G f = ∫ a, ∫ b, f a * G a b * f b`;
* `greenH_le_log_div`, `logKer`, `lintegral_logKer_le`: the logarithmic domination;
* `integrable_greenForm_inner`, `integrable_greenForm_outer`: the double integral is a genuine iterated integral;
* **`abs_greenForm_sub_le`**: the continuity estimate.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory Function
open scoped ENNReal Real

namespace InteractingSLE.WangWu

open QuantumZipper (greenH H)

/-- The Green quadratic form `Q_G(f) = ∫∫ f(a) G(a, b) f(b) da db` (for `G = retainedGreen w t` this is
`retainedGreenEnergy w t f`). -/
def greenForm (G : ℂ → ℂ → ℝ) (f : ℂ → ℝ) : ℝ := ∫ a, ∫ b, f a * G a b * f b

/-- On `B̄(0, R) ∩ ℍ`, `G_ℍ(a, b) ≤ log(4R/|a − b|)`. -/
lemma greenH_le_log_div {R : ℝ} {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (haR : ‖a‖ ≤ R) (hbR : ‖b‖ ≤ R) : greenH a b ≤ Real.log (4 * R / ‖a - b‖) := by
  have hd : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hc : 0 < ‖a - (starRingEnd ℂ) b‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    have h1 : (0 : ℝ) < a.im := ha
    have h2 : (0 : ℝ) < b.im := hb
    linarith
  have hcb : ‖a - (starRingEnd ℂ) b‖ ≤ 4 * R := by
    calc ‖a - (starRingEnd ℂ) b‖ ≤ ‖a‖ + ‖(starRingEnd ℂ) b‖ := norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ := by rw [Complex.norm_conj]
      _ ≤ 4 * R := by linarith [norm_nonneg a, norm_nonneg b]
  unfold greenH
  rw [Real.log_div (by linarith) hd.ne']
  linarith [Real.log_le_log hc hcb]

/-- The dominating kernel `1_{B̄(0,R)}(a) 1_{B̄(0,R)}(b) log(4R/|a − b|)`. -/
def logKer (R : ℝ) (a b : ℂ) : ℝ :=
  (closedBall (0 : ℂ) R).indicator 1 a * (closedBall (0 : ℂ) R).indicator 1 b *
    Real.log (4 * R / ‖a - b‖)

lemma logKer_comm (R : ℝ) (a b : ℂ) : logKer R a b = logKer R b a := by
  rw [logKer, logKer, norm_sub_rev, mul_comm ((closedBall (0 : ℂ) R).indicator 1 a)]

lemma logKer_nonneg {R : ℝ} (hR : 0 < R) (a b : ℂ) : 0 ≤ logKer R a b := by
  unfold logKer
  by_cases ha : a ∈ closedBall (0 : ℂ) R
  · by_cases hb : b ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem ha, indicator_of_mem hb]
      simp only [Pi.one_apply, one_mul]
      rcases eq_or_ne a b with rfl | hab
      · simp
      have hd : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
      have hd2 : ‖a - b‖ ≤ 2 * R := by
        have h1 : ‖a‖ ≤ R := by simpa using ha
        have h2 : ‖b‖ ≤ R := by simpa using hb
        linarith [norm_sub_le a b]
      exact Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
    · rw [indicator_of_notMem hb]; simp
  · rw [indicator_of_notMem ha]; simp

lemma measurable_logKer (R : ℝ) : Measurable fun p : ℂ × ℂ => logKer R p.1 p.2 := by
  have hi : Measurable ((closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ)) :=
    measurable_one.indicator measurableSet_closedBall
  exact ((hi.comp measurable_fst).mul (hi.comp measurable_snd)).mul
    (Real.measurable_log.comp (measurable_const.div (measurable_fst.sub measurable_snd).norm))

/-- `∫ log(4R/|a − b|) db` over `B̄(0, R)` is at most `32πR²`, uniformly in `a`. -/
lemma lintegral_logKer_le {R : ℝ} (hR : 0 < R) (a : ℂ) :
    ∫⁻ b, ENNReal.ofReal (logKer R a b) ≤ ENNReal.ofReal (32 * π * R ^ 2) := by
  by_cases ha : a ∈ closedBall (0 : ℂ) R
  swap
  · simp [logKer, indicator_of_notMem ha]
  have hsub : closedBall (0 : ℂ) R ⊆ ball a (4 * R) := by
    intro b hb
    rw [mem_closedBall, dist_zero_right] at hb
    have : ‖a‖ ≤ R := by simpa using ha
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le b a]
  have hpt : ∀ b, ENNReal.ofReal (logKer R a b) ≤
      (ball a (4 * R)).indicator (fun b => ENNReal.ofReal (Real.log (4 * R / ‖b - a‖))) b := by
    intro b
    by_cases hb : b ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem (hsub hb), logKer, indicator_of_mem ha, indicator_of_mem hb]
      simp only [Pi.one_apply, one_mul]
      rw [norm_sub_rev]
    · simp [logKer, indicator_of_notMem hb]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator measurableSet_ball]
  refine (lintegral_ball_log_div_norm_sub_le a (by positivity)).trans (le_of_eq ?_)
  congr 1; ring

/-- The pointwise domination: for `f, g` bounded by `B` and vanishing off `ℍ ∩ B̄(0, R)`,
`|f(a) G(a, b) g(b)| ≤ B² logKer R a b` for `a ≠ b`. -/
lemma abs_mul_mul_le_logKer {G : ℂ → ℂ → ℝ}
    (hG : ∀ a b, a ∈ H → b ∈ H → a ≠ b → 0 ≤ G a b ∧ G a b ≤ greenH a b) {R B : ℝ} (hR : 0 < R)
    {f g : ℂ → ℝ} (hf : ∀ z, |f z| ≤ B) (hg : ∀ z, |g z| ≤ B)
    (hfH : ∀ z, z ∉ H ∩ closedBall 0 R → f z = 0) (hgH : ∀ z, z ∉ H ∩ closedBall 0 R → g z = 0)
    {a b : ℂ} (hab : a ≠ b) : |f a * G a b * g b| ≤ B ^ 2 * logKer R a b := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  by_cases ha : a ∈ H ∩ closedBall 0 R
  swap
  · rw [hfH a ha]; simp only [zero_mul, abs_zero]; exact mul_nonneg (sq_nonneg _) (logKer_nonneg hR _ _)
  by_cases hb : b ∈ H ∩ closedBall 0 R
  swap
  · rw [hgH b hb]; simp only [mul_zero, abs_zero]; exact mul_nonneg (sq_nonneg _) (logKer_nonneg hR _ _)
  obtain ⟨hG0, hG1⟩ := hG a b ha.1 hb.1 hab
  have haR : ‖a‖ ≤ R := by simpa using ha.2
  have hbR : ‖b‖ ≤ R := by simpa using hb.2
  have hlog := greenH_le_log_div ha.1 hb.1 hab haR hbR
  rw [logKer, indicator_of_mem ha.2, indicator_of_mem hb.2]
  simp only [Pi.one_apply, one_mul]
  rw [abs_mul, abs_mul, abs_of_nonneg hG0, sq]
  calc |f a| * G a b * |g b| = |f a| * |g b| * G a b := by ring
    _ ≤ B * B * Real.log (4 * R / ‖a - b‖) :=
        mul_le_mul (mul_le_mul (hf a) (hg b) (abs_nonneg _) hB) (hG1.trans hlog) hG0
          (mul_nonneg hB hB)

lemma integrable_logKer {R : ℝ} (hR : 0 < R) (a : ℂ) : Integrable (logKer R a) := by
  refine ⟨((measurable_logKer R).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (logKer_nonneg hR a))]
  exact (lintegral_logKer_le hR a).trans_lt ENNReal.ofReal_lt_top

lemma ae_ne_point (a : ℂ) : ∀ᵐ b ∂(volume : Measure ℂ), b ≠ a := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]

section Forms

variable {G : ℂ → ℂ → ℝ} (hGm : Measurable (uncurry G))
  (hG : ∀ a b, a ∈ H → b ∈ H → a ≠ b → 0 ≤ G a b ∧ G a b ≤ greenH a b) {R B : ℝ} (hR : 0 < R)
  {f g : ℂ → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hf : ∀ z, |f z| ≤ B) (hg : ∀ z, |g z| ≤ B)
  (hfH : ∀ z, z ∉ H ∩ closedBall 0 R → f z = 0) (hgH : ∀ z, z ∉ H ∩ closedBall 0 R → g z = 0)
include hGm hG hR hfm hgm hf hg hfH hgH

omit hG hR hf hg hfH hgH in
lemma measurable_greenForm_integrand :
    Measurable fun p : ℂ × ℂ => f p.1 * G p.1 p.2 * g p.2 :=
  ((hfm.comp measurable_fst).mul hGm).mul (hgm.comp measurable_snd)

/-- The inner integrand of the Green form is integrable. -/
lemma integrable_greenForm_inner (a : ℂ) : Integrable fun b => f a * G a b * g b := by
  refine Integrable.mono' ((integrable_logKer hR a).const_mul (B ^ 2)) ?_ ?_
  · exact ((measurable_greenForm_integrand hGm hfm hgm).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_ne_point a] with b hb
    rw [Real.norm_eq_abs]
    exact abs_mul_mul_le_logKer hG hR hf hg hfH hgH (Ne.symm hb)

omit hGm hfm hgm in
lemma abs_integral_greenForm_inner_le (a : ℂ) :
    |∫ b, f a * G a b * g b| ≤
      (closedBall (0 : ℂ) R).indicator (fun _ => B ^ 2 * (32 * π * R ^ 2)) a := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf 0)
  by_cases ha : a ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem ha]
    have h1 : |∫ b, f a * G a b * g b| ≤ ∫ b, B ^ 2 * logKer R a b := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((integrable_logKer hR a).const_mul _) ?_
      filter_upwards [ae_ne_point a] with b hb
      rw [Real.norm_eq_abs]
      exact abs_mul_mul_le_logKer hG hR hf hg hfH hgH (Ne.symm hb)
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg B)
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (logKer_nonneg hR a))
      ((integrable_logKer hR a).aestronglyMeasurable)]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_logKer_le hR a)
  · rw [indicator_of_notMem ha, hfH a fun h => ha h.2]
    simp

/-- The outer integrand of the Green form is integrable. -/
lemma integrable_greenForm_outer : Integrable fun a => ∫ b, f a * G a b * g b := by
  refine Integrable.mono' ((integrableOn_const (s := closedBall (0 : ℂ) R) (μ := volume)
    (C := B ^ 2 * (32 * π * R ^ 2)) measure_closedBall_lt_top.ne).integrable_indicator
    measurableSet_closedBall) ?_ ?_
  · exact (StronglyMeasurable.integral_prod_right'
      (measurable_greenForm_integrand hGm hfm hgm).stronglyMeasurable
      ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]
      exact abs_integral_greenForm_inner_le hG hR hf hg hfH hgH a

end Forms

/-- `∫∫ c logKer(a, b) 1_U(a) ≤ c · 32πR² |U|` and the same with `1_U(b)` (symmetry of `logKer`). -/
lemma lintegral_lintegral_logKer_indicator_le {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : MeasurableSet U)
    (c : ℝ≥0∞) :
    (∫⁻ a, ∫⁻ b, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a) ≤
        c * ENNReal.ofReal (32 * π * R ^ 2) * volume U ∧
      (∫⁻ a, ∫⁻ b, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b) ≤
        c * ENNReal.ofReal (32 * π * R ^ 2) * volume U := by
  have hK : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (logKer R p.1 p.2) :=
    (measurable_logKer R).ennreal_ofReal
  have hI : Measurable (U.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hU
  have hKa : ∀ a, Measurable fun b => ENNReal.ofReal (logKer R a b) := fun a =>
    ((measurable_logKer R).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hKb : ∀ b, Measurable fun a => ENNReal.ofReal (logKer R a b) := fun b =>
    ((measurable_logKer R).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have key : ∀ a, (∫⁻ b, c * ENNReal.ofReal (logKer R a b)) ≤ c * ENNReal.ofReal (32 * π * R ^ 2) :=
    fun a => by
      rw [lintegral_const_mul _ (hKa a)]
      exact mul_le_mul_right (lintegral_logKer_le hR a) _
  have hU1 : ∫⁻ a, U.indicator (1 : ℂ → ℝ≥0∞) a = volume U := by
    rw [lintegral_indicator hU]; simp
  constructor
  · calc (∫⁻ a, ∫⁻ b, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a)
        = ∫⁻ a, (∫⁻ b, c * ENNReal.ofReal (logKer R a b)) * U.indicator 1 a := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_mul_const _ ((hKa a).const_mul c)]
      _ ≤ ∫⁻ a, c * ENNReal.ofReal (32 * π * R ^ 2) * U.indicator 1 a :=
          lintegral_mono fun a => mul_le_mul_left (key a) _
      _ = c * ENNReal.ofReal (32 * π * R ^ 2) * volume U := by
          rw [lintegral_const_mul _ hI, hU1]
  · have hF : AEMeasurable (uncurry fun a b => c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b)
        ((volume : Measure ℂ).prod volume) :=
      ((hK.const_mul c).mul (hI.comp measurable_snd)).aemeasurable
    rw [lintegral_lintegral_swap hF]
    calc (∫⁻ b, ∫⁻ a, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b)
        = ∫⁻ b, (∫⁻ a, c * ENNReal.ofReal (logKer R b a)) * U.indicator 1 b := by
          refine lintegral_congr fun b => ?_
          rw [lintegral_mul_const _ ((hKb b).const_mul c)]
          congr 1
          refine lintegral_congr fun a => ?_
          rw [logKer_comm R a b]
      _ ≤ ∫⁻ b, c * ENNReal.ofReal (32 * π * R ^ 2) * U.indicator 1 b :=
          lintegral_mono fun b => mul_le_mul_left (key b) _
      _ = c * ENNReal.ofReal (32 * π * R ^ 2) * volume U := by
          rw [lintegral_const_mul _ hI, hU1]

/-- **Continuity of a Green-dominated form** (proof of Corollary 4.23: "Their conditional covariances tend to
`Q_{D∖A}(p, p)` by dominated convergence, using `G_{D∖A} ≤ G_D` and the locally integrable logarithmic
singularity"). Let `0 ≤ G ≤ G_ℍ` off the diagonal of `ℍ × ℍ`, and let `φ, f` be measurable, bounded by `B`,
vanishing off `ℍ ∩ B̄(0, R)` and agreeing off `U`. Then `|Q_G(φ) − Q_G(f)| ≤ 256 π R² B² |U|`. -/
theorem abs_greenForm_sub_le {G : ℂ → ℂ → ℝ} (hGm : Measurable (uncurry G))
    (hG : ∀ a b, a ∈ H → b ∈ H → a ≠ b → 0 ≤ G a b ∧ G a b ≤ greenH a b) {R B : ℝ} (hR : 0 < R)
    {φ f : ℂ → ℝ} (hφm : Measurable φ) (hfm : Measurable f) (hφ : ∀ z, |φ z| ≤ B)
    (hf : ∀ z, |f z| ≤ B) (hφH : ∀ z, z ∉ H ∩ closedBall 0 R → φ z = 0)
    (hfH : ∀ z, z ∉ H ∩ closedBall 0 R → f z = 0) {U : Set ℂ} (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hdiff : ∀ z, z ∉ U → φ z = f z) :
    |greenForm G φ - greenForm G f| ≤ 256 * π * R ^ 2 * B ^ 2 * (volume U).toReal := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hφ 0)
  set β : ℂ → ℝ := fun z => φ z - f z with hβ
  have hβm : Measurable β := hφm.sub hfm
  have hβb : ∀ z, |β z| ≤ 2 * B := fun z => (abs_sub _ _).trans (by linarith [hφ z, hf z])
  have hβH : ∀ z, z ∉ H ∩ closedBall 0 R → β z = 0 := fun z hz => by
    simp only [hβ, hφH z hz, hfH z hz, sub_zero]
  have hβU : ∀ z, z ∉ U → β z = 0 := fun z hz => by simp only [hβ, hdiff z hz, sub_self]
  have hφ2 : ∀ z, |φ z| ≤ 2 * B := fun z => (hφ z).trans (by linarith)
  have hf2 : ∀ z, |f z| ≤ 2 * B := fun z => (hf z).trans (by linarith)
  -- the difference as one iterated integral
  have hdiffint : greenForm G φ - greenForm G f =
      ∫ a, ∫ b, (β a * G a b * φ b + f a * G a b * β b) := by
    rw [greenForm, greenForm, ← integral_sub
      (integrable_greenForm_outer hGm hG hR hφm hφm hφ hφ hφH hφH)
      (integrable_greenForm_outer hGm hG hR hfm hfm hf hf hfH hfH)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [← integral_sub (integrable_greenForm_inner hGm hG hR hφm hφm hφ hφ hφH hφH a)
      (integrable_greenForm_inner hGm hG hR hfm hfm hf hf hfH hfH a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [hβ]
    ring
  rw [hdiffint]
  set c : ℝ≥0∞ := ENNReal.ofReal (4 * B ^ 2) with hc
  -- the pointwise bound
  have hpt : ∀ a, ∀ᵐ b ∂(volume : Measure ℂ), ‖β a * G a b * φ b + f a * G a b * β b‖ₑ ≤
      c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a +
        c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b := by
    intro a
    filter_upwards [ae_ne_point a] with b hb
    have hk := logKer_nonneg hR a b
    have h1 := abs_mul_mul_le_logKer hG hR hβb hφ2 hβH hφH (Ne.symm hb)
    have h2 := abs_mul_mul_le_logKer hG hR hf2 hβb hfH hβH (Ne.symm hb)
    have e1 : ‖β a * G a b * φ b‖ₑ ≤ c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a := by
      by_cases ha : a ∈ U
      · rw [indicator_of_mem ha, Pi.one_apply, mul_one, hc, ← ENNReal.ofReal_mul (by positivity),
          Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
      · rw [hβU a ha]; simp
    have e2 : ‖f a * G a b * β b‖ₑ ≤ c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b := by
      by_cases hbU : b ∈ U
      · rw [indicator_of_mem hbU, Pi.one_apply, mul_one, hc, ← ENNReal.ofReal_mul (by positivity),
          Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
      · rw [hβU b hbU]; simp
    exact (enorm_add_le _ _).trans (add_le_add e1 e2)
  have hK : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (logKer R p.1 p.2) :=
    (measurable_logKer R).ennreal_ofReal
  have hI : Measurable (U.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hU
  have hKa : ∀ a, Measurable fun b => ENNReal.ofReal (logKer R a b) := fun a =>
    ((measurable_logKer R).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  obtain ⟨hb1, hb2⟩ := lintegral_lintegral_logKer_indicator_le hR hU c
  have htot : ‖∫ a, ∫ b, (β a * G a b * φ b + f a * G a b * β b)‖ₑ ≤
      2 * (c * ENNReal.ofReal (32 * π * R ^ 2) * volume U) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ a, ‖∫ b, (β a * G a b * φ b + f a * G a b * β b)‖ₑ
        ≤ ∫⁻ a, ∫⁻ b, (c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a +
            c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b) :=
          lintegral_mono fun a => (enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono_ae (hpt a))
      _ = (∫⁻ a, ∫⁻ b, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 a) +
            ∫⁻ a, ∫⁻ b, c * ENNReal.ofReal (logKer R a b) * U.indicator 1 b := by
          rw [← lintegral_add_left]
          · refine lintegral_congr fun a => ?_
            rw [lintegral_add_left]
            exact ((hKa a).const_mul c).mul_const _
          · exact (((hK.const_mul c).mul (hI.comp measurable_fst)).lintegral_prod_right')
      _ ≤ _ := by rw [two_mul]; exact add_le_add hb1 hb2
  have hfin : 2 * (c * ENNReal.ofReal (32 * π * R ^ 2) * volume U) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.mul_ne_top ?_ hUf)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have habs : |∫ a, ∫ b, (β a * G a b * φ b + f a * G a b * β b)| =
      (‖∫ a, ∫ b, (β a * G a b * φ b + f a * G a b * β b)‖ₑ).toReal := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [habs]
  refine (ENNReal.toReal_mono hfin htot).trans (le_of_eq ?_)
  rw [hc, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

/-- **The retained Green kernel is dominated by `G_ℍ`** (the hypothesis `0 ≤ G ≤ G_ℍ` of `abs_greenForm_sub_le` and
of the Corollary 4.23 kernel identity, for QuantumZipper's `V_T`, i.e. `WangWu.retainedGreen`): time `0` is an
admissible time, where the kernel is `G_ℍ(a, b)` itself, and `V_T` is an infimum over admissible times. -/
theorem VT_nonneg_le_greenH {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) :
    0 ≤ QuantumZipper.K3.VT W T a b ∧ QuantumZipper.K3.VT W T a b ≤ greenH a b := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h0 : (0 : ℝ) ∈ QuantumZipper.K3.vtIdx W T a b := by
    refine ⟨le_rfl, hT, ?_, ?_⟩
    · rw [ENNReal.ofReal_zero]; exact QuantumZipper.swallowTime_pos hW ha
    · rw [ENNReal.ofReal_zero]; exact QuantumZipper.swallowTime_pos hW hb
  have hne : ∀ z ∈ H, z ≠ W 0 := fun z hz h => by
    rw [hW0] at h
    have : (0 : ℝ) < z.im := hz
    rw [h] at this
    simp at this
  have hle : QuantumZipper.K3.VTe W T a b ≤ ENNReal.ofReal (greenH a b) := by
    refine (iInf₂_le (0 : ℝ) h0).trans (le_of_eq ?_)
    rw [QuantumZipper.K3.vtKer, QuantumZipper.B5.fwdMap_zero_time W (hne a ha),
      QuantumZipper.B5.fwdMap_zero_time W (hne b hb), hW0, Complex.ofReal_zero, sub_zero, sub_zero]
  exact ENNReal.toReal_le_of_le_ofReal
    (QuantumZipper.greenH_nonneg (QuantumZipper.K3.H_subset_Hbar_K3 ha)
      (QuantumZipper.K3.H_subset_Hbar_K3 hb) hab) hle

end InteractingSLE.WangWu
