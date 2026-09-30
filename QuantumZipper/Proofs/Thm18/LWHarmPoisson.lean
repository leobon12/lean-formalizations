import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import QuantumZipper.Common.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): harmonic measure of a real open set in `ℍ`

Task LW-HARM (A), half-plane step. Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*,
Cambridge 2005, Ch. I §1, eq. (1.5), p. 4 (`literature/GarnettMarshall_HarmonicMeasure_2005.pdf`,
PDF p. 22): for `E ⊆ ℝ` measurable, `ω(x + iy, E, ℍ) = ∫_E y / ((t − x)² + y²) dt/π`, with the
properties (i)–(iii) of p. 2: `0 ≤ ω ≤ 1`, `ω → 1` at interior points of `E`, `ω → 0` at points
off `closure E`. Here `ω(w, O) = ∫_O cauchyPDFReal (Re w) (Im w)` (mathlib's Cauchy density is
exactly the Poisson kernel of `ℍ`).

* `lwHarm_eq_im`, `lwHarm_diffOn`: for bounded measurable `O`, `ω(·, O) = Im Φ_O / π` on `ℍ`
  with `Φ_O(w) = ∫_O (t − w)⁻¹ dt` holomorphic on `ℍ` (differentiation under the integral);
  hence `ω(·, O)` is harmonic (`lwHarm_harmonic`), GM p. 5 ("harmonic in its first variable").
* `lwHarm_tail_le`: the quantitative form of (ii)/(iii): if `|Re w − t₀| ≤ δ/2` and `S` misses
  `(t₀ − δ, t₀ + δ)`, then `ω(w, S) ≤ 8 Im w / δ` (own elementary comparison of kernels).
* `lwHarm_tendsto_one`, `lwHarm_tendsto_zero`, `lwHarm_small_far`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex ProbabilityTheory
open scoped Topology NNReal Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Harmonic measure of `O ⊆ ℝ` in `ℍ` seen from `w` (GM (1.5), p. 4). -/
def lwHarmOm (O : Set ℝ) (w : ℂ) : ℝ := ∫ t in O, cauchyPDFReal w.re w.im.toNNReal t

lemma lwHarm_toNNReal_ne {w : ℂ} (hw : 0 < w.im) : w.im.toNNReal ≠ 0 := by
  simpa using hw

lemma lwHarm_pdf_eq {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    cauchyPDFReal w.re w.im.toNNReal t = π⁻¹ * (w.im / ((t - w.re) ^ 2 + w.im ^ 2)) := by
  rw [cauchyPDFReal_def, Real.coe_toNNReal _ hw.le]
  ring

lemma lwHarm_pdf_nonneg0 (x : ℝ) (γ : ℝ≥0) (t : ℝ) : 0 ≤ cauchyPDFReal x γ t := by
  rw [cauchyPDFReal_def]; positivity

lemma lwHarm_pdf_nonneg (w : ℂ) (t : ℝ) : 0 ≤ cauchyPDFReal w.re w.im.toNNReal t := by
  rw [cauchyPDFReal_def]; positivity

lemma lwHarm_nonneg (O : Set ℝ) (w : ℂ) : 0 ≤ lwHarmOm O w :=
  integral_nonneg fun t => lwHarm_pdf_nonneg w t

lemma lwHarm_le_one (O : Set ℝ) {w : ℂ} (hw : 0 < w.im) : lwHarmOm O w ≤ 1 := by
  unfold lwHarmOm
  rw [← integral_cauchyPDFReal_eq_one w.re (lwHarm_toNNReal_ne hw)]
  exact setIntegral_le_integral (integrable_cauchyPDFReal _)
    (Eventually.of_forall fun t => lwHarm_pdf_nonneg w t)

lemma lwHarm_add_compl {O : Set ℝ} (hO : MeasurableSet O) {w : ℂ} (hw : 0 < w.im) :
    lwHarmOm O w + lwHarmOm Oᶜ w = 1 := by
  unfold lwHarmOm
  rw [integral_add_compl hO (integrable_cauchyPDFReal _),
    integral_cauchyPDFReal_eq_one w.re (lwHarm_toNNReal_ne hw)]

/-- Kernel comparison: `|Re w − t₀| ≤ δ/2`, `|t − t₀| ≥ δ` give
`P_w(t) ≤ 8 (Im w/δ) P_{t₀+iδ}(t)`. -/
lemma lwHarm_pdf_le {w : ℂ} (hw : 0 < w.im) {t₀ δ t : ℝ} (hδ : 0 < δ)
    (hx : |w.re - t₀| ≤ δ / 2) (ht : δ ≤ |t - t₀|) :
    cauchyPDFReal w.re w.im.toNNReal t ≤
      8 * (w.im / δ) * cauchyPDFReal t₀ δ.toNNReal t := by
  rw [cauchyPDFReal_def, cauchyPDFReal_def, Real.coe_toNNReal _ hw.le,
    Real.coe_toNNReal _ hδ.le]
  set u := t - t₀
  set v := w.re - t₀
  have htx : t - w.re = u - v := by simp [u, v]
  rw [htx]
  have h1 : |u| / 2 ≤ |u - v| := by
    have := abs_sub_abs_le_abs_sub u v
    linarith
  have h2 : (|u| / 2) ^ 2 ≤ (u - v) ^ 2 := by
    rw [← sq_abs (u - v)]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have h3 : δ ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ hδ.le ht 2
  have hu2 : (|u| / 2) ^ 2 = u ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
  have hA : 0 < (u - v) ^ 2 + w.im ^ 2 := by positivity
  have hB : 0 < u ^ 2 + δ ^ 2 := by positivity
  have key : u ^ 2 + δ ^ 2 ≤ 8 * ((u - v) ^ 2 + w.im ^ 2) := by nlinarith
  have hπ : 0 < π⁻¹ := inv_pos.2 Real.pi_pos
  rw [show 8 * (w.im / δ) * (π⁻¹ * δ * (u ^ 2 + δ ^ 2)⁻¹) =
      π⁻¹ * (8 * w.im) * (u ^ 2 + δ ^ 2)⁻¹ by field_simp]
  have : w.im * ((u - v) ^ 2 + w.im ^ 2)⁻¹ ≤ (8 * w.im) * (u ^ 2 + δ ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hA hB]
    nlinarith
  calc π⁻¹ * w.im * ((u - v) ^ 2 + w.im ^ 2)⁻¹
      = π⁻¹ * (w.im * ((u - v) ^ 2 + w.im ^ 2)⁻¹) := by ring
    _ ≤ π⁻¹ * ((8 * w.im) * (u ^ 2 + δ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left this hπ.le
    _ = _ := by ring

/-- **Tail bound** (quantitative GM (ii)/(iii), p. 2): `ω(w, S) ≤ 8 Im w / δ` when `S` misses
`(t₀ − δ, t₀ + δ)` and `|Re w − t₀| ≤ δ/2`. -/
theorem lwHarm_tail_le {S : Set ℝ} (hS : MeasurableSet S) {w : ℂ} (hw : 0 < w.im) {t₀ δ : ℝ}
    (hδ : 0 < δ) (hx : |w.re - t₀| ≤ δ / 2) (hSd : ∀ t ∈ S, δ ≤ |t - t₀|) :
    lwHarmOm S w ≤ 8 * w.im / δ := by
  unfold lwHarmOm
  calc ∫ t in S, cauchyPDFReal w.re w.im.toNNReal t
      ≤ ∫ t in S, 8 * (w.im / δ) * cauchyPDFReal t₀ δ.toNNReal t :=
        setIntegral_mono_on (integrable_cauchyPDFReal _).integrableOn
          ((integrable_cauchyPDFReal _).const_mul _).integrableOn hS
          fun t ht => lwHarm_pdf_le hw hδ hx (hSd t ht)
    _ ≤ ∫ t, 8 * (w.im / δ) * cauchyPDFReal t₀ δ.toNNReal t :=
        setIntegral_le_integral ((integrable_cauchyPDFReal _).const_mul _)
          (Eventually.of_forall fun t => mul_nonneg (by positivity) (lwHarm_pdf_nonneg0 t₀ δ.toNNReal t))
    _ = 8 * w.im / δ := by
        rw [integral_const_mul, integral_cauchyPDFReal_eq_one t₀ (by simpa using hδ)]
        ring

/-- `ω(·, O) → 1` at an interior point of `O` (GM (ii), p. 2). -/
theorem lwHarm_tendsto_one {O : Set ℝ} (hO : MeasurableSet O) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hsub : Ioo (t₀ - δ) (t₀ + δ) ⊆ O) :
    Tendsto (lwHarmOm O) (𝓝[H] (t₀ : ℂ)) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (δ / 2) (ε * δ / 8), by positivity, fun w hw hwd => ?_⟩
  have hw' : 0 < w.im := hw
  have hd : ‖w - t₀‖ < min (δ / 2) (ε * δ / 8) := by rwa [dist_eq_norm] at hwd
  have hre : |w.re - t₀| ≤ δ / 2 := by
    have := Complex.abs_re_le_norm (w - t₀)
    simp only [sub_re, ofReal_re] at this
    linarith [min_le_left (δ / 2) (ε * δ / 8)]
  have him : w.im < ε * δ / 8 := by
    have := Complex.abs_im_le_norm (w - t₀)
    simp only [sub_im, ofReal_im, sub_zero] at this
    linarith [min_le_right (δ / 2) (ε * δ / 8), le_abs_self w.im]
  have hc := lwHarm_tail_le hO.compl hw' hδ hre (fun t ht => by
    by_contra hlt
    push_neg at hlt
    exact ht (hsub ⟨by linarith [neg_abs_le (t - t₀)], by linarith [le_abs_self (t - t₀)]⟩))
  have hs := lwHarm_add_compl hO hw'
  have h1 := lwHarm_le_one O hw'
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  have : 8 * w.im / δ < ε := by rw [div_lt_iff₀ hδ]; linarith
  linarith

/-- `ω(·, O) → 0` at a point with a neighbourhood missing `O` (GM (iii), p. 2). -/
theorem lwHarm_tendsto_zero {O : Set ℝ} (hO : MeasurableSet O) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hdisj : ∀ t ∈ O, δ ≤ |t - t₀|) :
    Tendsto (lwHarmOm O) (𝓝[H] (t₀ : ℂ)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (δ / 2) (ε * δ / 8), by positivity, fun w hw hwd => ?_⟩
  have hw' : 0 < w.im := hw
  have hd : ‖w - t₀‖ < min (δ / 2) (ε * δ / 8) := by rwa [dist_eq_norm] at hwd
  have hre : |w.re - t₀| ≤ δ / 2 := by
    have := Complex.abs_re_le_norm (w - t₀)
    simp only [sub_re, ofReal_re] at this
    linarith [min_le_left (δ / 2) (ε * δ / 8)]
  have him : w.im < ε * δ / 8 := by
    have := Complex.abs_im_le_norm (w - t₀)
    simp only [sub_im, ofReal_im, sub_zero] at this
    linarith [min_le_right (δ / 2) (ε * δ / 8), le_abs_self w.im]
  have hc := lwHarm_tail_le hO hw' hδ hre hdisj
  have h0 := lwHarm_nonneg O w
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have : 8 * w.im / δ < ε := by rw [div_lt_iff₀ hδ]; linarith
  linarith

/-- `ω(·, O) → 0` at `∞` for bounded `O`: `ω(w, O) ≤ 16 R/(π ‖w‖)` if `O ⊆ [−R, R]`,
`‖w‖ ≥ 2R`. -/
theorem lwHarm_small_far {O : Set ℝ} {R : ℝ} (hR : 0 < R) (hOR : O ⊆ Icc (-R) R) {a : ℝ}
    (ha : 0 < a) : ∃ M : ℝ, ∀ w : ℂ, 0 < w.im → M < ‖w‖ → lwHarmOm O w < a := by
  refine ⟨max (2 * R) (8 * R / a), fun w hw hM => ?_⟩
  have hM1 : 2 * R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hM
  have hM2 : 8 * R / a < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hM
  have hwpos : 0 < ‖w‖ := by linarith
  have hnw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hyle : w.im ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_im_le_norm w)
  have hbd : ∀ t ∈ O, ‖cauchyPDFReal w.re w.im.toNNReal t‖ ≤ 4 / (π * ‖w‖) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (lwHarm_pdf_nonneg w t), lwHarm_pdf_eq hw]
    have htR : t ^ 2 ≤ R ^ 2 := by
      rcases hOR ht with ⟨h1, h2⟩; nlinarith
    have h4 : 4 * R ^ 2 < ‖w‖ ^ 2 := by nlinarith
    have hden : ‖w‖ ^ 2 / 4 ≤ (t - w.re) ^ 2 + w.im ^ 2 := by
      nlinarith [sq_nonneg (w.re - 2 * t)]
    have hden0 : 0 < ‖w‖ ^ 2 / 4 := by positivity
    have : w.im / ((t - w.re) ^ 2 + w.im ^ 2) ≤ 4 / ‖w‖ := by
      rw [div_le_div_iff₀ (by linarith) hwpos]
      nlinarith
    calc π⁻¹ * (w.im / ((t - w.re) ^ 2 + w.im ^ 2)) ≤ π⁻¹ * (4 / ‖w‖) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 Real.pi_pos).le
      _ = 4 / (π * ‖w‖) := by field_simp
  have hvol : volume O ≤ volume (Icc (-R) R) := measure_mono hOR
  have hvolR : volume.real O ≤ 2 * R := by
    have h := measureReal_mono (μ := volume) hOR (by simp)
    rw [Real.volume_real_Icc_of_le (by linarith)] at h
    linarith
  have hfin : volume O < ⊤ := hvol.trans_lt (by simp)
  have h := norm_setIntegral_le_of_norm_le_const hfin hbd
  unfold lwHarmOm
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => lwHarm_pdf_nonneg w t)] at h
  calc _ ≤ 4 / (π * ‖w‖) * volume.real O := h
    _ ≤ 4 / (π * ‖w‖) * (2 * R) := mul_le_mul_of_nonneg_left hvolR (by positivity)
    _ ≤ 8 * R / ‖w‖ := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hwpos]
        have : 1 ≤ π := by linarith [Real.two_le_pi]
        have := mul_nonneg (mul_nonneg hR.le hwpos.le) (sub_nonneg.2 this)
        nlinarith
    _ < a := by
        rw [div_lt_iff₀ hwpos]; rw [div_lt_iff₀ ha] at hM2; linarith

/-! ### Harmonicity through the Cauchy integral -/

/-- `Φ_O(w) = ∫_O (t − w)⁻¹ dt`. -/
def lwHarmPhi (O : Set ℝ) (w : ℂ) : ℂ := ∫ t in O, ((t : ℂ) - w)⁻¹

lemma lwHarm_inv_im {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    (((t : ℂ) - w)⁻¹).im = π * cauchyPDFReal w.re w.im.toNNReal t := by
  rw [lwHarm_pdf_eq hw, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul,
    Complex.inv_im, Complex.normSq_apply]
  simp only [sub_im, ofReal_im, sub_re, ofReal_re]
  congr 1 <;> ring

lemma lwHarm_meas_inv (w : ℂ) : Measurable fun t : ℝ => ((t : ℂ) - w)⁻¹ := by fun_prop

lemma lwHarm_norm_inv_le {w : ℂ} {c : ℝ} (hc : 0 < c) (hw : c ≤ w.im) (t : ℝ) :
    ‖((t : ℂ) - w)⁻¹‖ ≤ c⁻¹ := by
  have h : c ≤ ‖(t : ℂ) - w‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) - w)
    simp only [sub_im, ofReal_im, zero_sub, abs_neg] at this
    linarith [le_abs_self w.im]
  rw [norm_inv]
  exact inv_anti₀ hc h

lemma lwHarm_integrable_inv {O : Set ℝ} (hOf : volume O < ⊤) {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun t : ℝ => ((t : ℂ) - w)⁻¹) (volume.restrict O) := by
  have : IsFiniteMeasure (volume.restrict O) := ⟨by simpa using hOf⟩
  exact Integrable.of_bound (lwHarm_meas_inv w).aestronglyMeasurable (w.im⁻¹)
    (Eventually.of_forall fun t => lwHarm_norm_inv_le hw le_rfl t)

/-- `ω(w, O) = Im Φ_O(w)/π` on `ℍ` for `O` of finite measure. -/
theorem lwHarm_eq_im {O : Set ℝ} (hOf : volume O < ⊤) {w : ℂ} (hw : 0 < w.im) :
    lwHarmOm O w = (lwHarmPhi O w).im / π := by
  unfold lwHarmOm lwHarmPhi
  have h := integral_im (𝕜 := ℂ) (lwHarm_integrable_inv hOf hw)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  simp_rw [lwHarm_inv_im hw]
  rw [integral_const_mul]
  field_simp

/-- `Φ_O` is holomorphic on `ℍ` (differentiation under the integral sign). -/
theorem lwHarm_diffOn {O : Set ℝ} (hOf : volume O < ⊤) : DifferentiableOn ℂ (lwHarmPhi O) H := by
  intro w₀ hw₀
  have hy : 0 < w₀.im := hw₀
  have : IsFiniteMeasure (volume.restrict O) := ⟨by simpa using hOf⟩
  have hball : ∀ w ∈ ball w₀ (w₀.im / 2), w₀.im / 2 ≤ w.im := by
    intro w hw
    have h1 := Complex.abs_im_le_norm (w - w₀)
    rw [mem_ball, dist_eq_norm] at hw
    simp only [sub_im] at h1
    linarith [neg_abs_le (w.im - w₀.im)]
  have hy2 : 0 < w₀.im / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict O)
    (F := fun w (t : ℝ) => ((t : ℂ) - w)⁻¹)
    (F' := fun w (t : ℝ) => -(-1 : ℂ) / ((t : ℂ) - w) ^ 2)
    (bound := fun _ => (w₀.im / 2)⁻¹ ^ 2) (x₀ := w₀) (ball_mem_nhds w₀ hy2)
    (Eventually.of_forall fun w => (lwHarm_meas_inv w).aestronglyMeasurable)
    (lwHarm_integrable_inv hOf hy)
    (by fun_prop : Measurable fun t : ℝ => -(-1 : ℂ) / ((t : ℂ) - w₀) ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun t w hw => by
      rw [neg_neg, one_div, norm_inv, norm_pow, ← inv_pow, ← norm_inv]
      exact pow_le_pow_left₀ (norm_nonneg _) (lwHarm_norm_inv_le hy2 (hball w hw) t) 2)
    (integrable_const _)
    (Eventually.of_forall fun t w hw => by
      have hne : (t : ℂ) - w ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp only [sub_im, ofReal_im, zero_im] at this
        linarith [hball w hw]
      exact ((hasDerivAt_id' w).const_sub (t : ℂ)).inv hne)
  exact key.2.differentiableAt.differentiableWithinAt

end LWFar
end Thm18Asm
end QuantumZipper
