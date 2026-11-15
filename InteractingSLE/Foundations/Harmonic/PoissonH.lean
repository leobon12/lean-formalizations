import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import QuantumZipper.Proofs.Complex.BasicsCayley
import QuantumZipper.Proofs.Thm11.LyapunovAlgebra
import InteractingSLE.Foundations.Harmonic.StepData

/-!
# Poisson kernel, harmonic measure and Poisson integral of the upper half-plane

Packet GEO-POIS of the geometry foundation (`planning/INFRA-GEO.md` §3 "Harmonic analysis", §4).
Infrastructure (textbook results, [Gar] Garnett–Marshall, *Harmonic Measure*, Ch. I; [Law05]
Lawler, *Conformally Invariant Processes in the Plane*, Ch. 2), not a frozen source-facing file.

* `poissonKernelH z x = Im z / (π |z − x|²)`, `harmonicMeasureH z = P(z, ·) dx` on `ℝ = ∂ℍ`,
  `poissonIntegralH φ z = ∫ P(z, x) φ(x) dx` for `φ ∈ L^∞(ℝ)`.
* On `ℍ` the kernel is Mathlib's Cauchy density with location `Re z` and scale `Im z`
  (`poissonKernelH_eq_cauchyPDFReal`), whence `isProbabilityMeasure_harmonicMeasureH`.
* `x ↦ arg(z − x)/π` is a primitive of `P(z, ·)` (`hasDerivAt_arg_sub_div_pi`), whence
  `harmonicMeasureH_Ioo` and `harmonicMeasureH_Iio`.
* `abs_poissonIntegralH_le`: `|u φ| ≤ ‖φ‖_∞`.
* `harmonicOnNhd_poissonIntegralH`: on `ℍ`, `u φ = Im G / π + const` with
  `G z = ∫ φ(x) (1/(x − z) − 1/(x − i)) dx` holomorphic (differentiation under the integral).
* `tendsto_poissonIntegralH`: boundary values at continuity points of a representative
  (approximate identity, using the interval formula).
* `harmonicMeasureH_mobius`: invariance under real Möbius maps with `ad − bc > 0`
  (one-dimensional change of variables and `P(m z, m x) m'(x) = P(z, x)`).
* `StepData.harmonicExtH_eq_poissonIntegralH`: the explicit step-data extension of
  `Harmonic/StepData.lean` is the Poisson integral of its boundary function (via the uniqueness
  theorem `StepData.eqOn_harmonicExtH`).

Generic helper lemmas live in the namespace `InteractingSLE.PoissonH`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- The Poisson kernel of `ℍ`: `P(z, x) = Im z / (π |z − x|²)` (the density of harmonic measure
from `z` on `ℝ`). Meaningful for `z ∈ ℍ`; statements always assume `z ∈ H`. -/
def poissonKernelH (z : ℂ) (x : ℝ) : ℝ :=
  z.im / (π * ‖z - x‖ ^ 2)

/-- Harmonic measure of `ℍ` from `z`, as a measure on `ℝ = ∂ℍ` ([Law05] Ch. 2). -/
def harmonicMeasureH (z : ℂ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (poissonKernelH z x)

/-- The Poisson integral on `ℍ` of an essentially bounded boundary function. On this carrier
the integral is always absolutely convergent for `z ∈ ℍ`, so the Bochner integral is the
textbook Poisson integral (no junk value is reachable for `z ∈ H`). -/
def poissonIntegralH (φ : Lp ℝ ∞ (volume : Measure ℝ)) (z : ℂ) : ℝ :=
  ∫ x, poissonKernelH z x * φ x

lemma PoissonH.norm_sub_ofReal_sq (z : ℂ) (x : ℝ) : ‖z - x‖ ^ 2 = (x - z.re) ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  ring

lemma PoissonH.im_pos_of_mem_H {z : ℂ} (hz : z ∈ H) : 0 < z.im := hz

open PoissonH

lemma PoissonH.toNNReal_im_ne_zero {z : ℂ} (hz : z ∈ H) : z.im.toNNReal ≠ 0 := by
  simpa using im_pos_of_mem_H hz

/-- On `ℍ` the Poisson kernel is the Cauchy density with location `Re z` and scale `Im z`. -/
lemma poissonKernelH_eq_cauchyPDFReal {z : ℂ} (hz : z ∈ H) (x : ℝ) :
    poissonKernelH z x = ProbabilityTheory.cauchyPDFReal z.re z.im.toNNReal x := by
  rw [poissonKernelH, ProbabilityTheory.cauchyPDFReal_def, norm_sub_ofReal_sq,
    Real.coe_toNNReal _ (im_pos_of_mem_H hz).le, div_eq_mul_inv, mul_inv]
  ring

lemma poissonKernelH_eq_cauchyPDFReal' {z : ℂ} (hz : z ∈ H) :
    poissonKernelH z = ProbabilityTheory.cauchyPDFReal z.re z.im.toNNReal :=
  funext (poissonKernelH_eq_cauchyPDFReal hz)

lemma harmonicMeasureH_eq_cauchyMeasure {z : ℂ} (hz : z ∈ H) :
    harmonicMeasureH z = ProbabilityTheory.cauchyMeasure z.re z.im.toNNReal := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero _ (toNNReal_im_ne_zero hz), harmonicMeasureH,
    poissonKernelH_eq_cauchyPDFReal' hz]
  rfl

/-- Harmonic measure from a point of `ℍ` is a probability measure. -/
theorem isProbabilityMeasure_harmonicMeasureH {z : ℂ} (hz : z ∈ H) :
    IsProbabilityMeasure (harmonicMeasureH z) := by
  rw [harmonicMeasureH_eq_cauchyMeasure hz]; infer_instance

lemma poissonKernelH_pos {z : ℂ} (hz : z ∈ H) (x : ℝ) : 0 < poissonKernelH z x := by
  have h := im_pos_of_mem_H hz
  rw [poissonKernelH, norm_sub_ofReal_sq]; positivity

lemma integrable_poissonKernelH {z : ℂ} (hz : z ∈ H) : Integrable (poissonKernelH z) := by
  rw [poissonKernelH_eq_cauchyPDFReal' hz]; exact ProbabilityTheory.integrable_cauchyPDFReal _

lemma integral_poissonKernelH {z : ℂ} (hz : z ∈ H) : ∫ x, poissonKernelH z x = 1 := by
  rw [poissonKernelH_eq_cauchyPDFReal' hz]
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one _ (toNNReal_im_ne_zero hz)

lemma PoissonH.arg_sub_ofReal_eq {z : ℂ} (hz : z ∈ H) (x : ℝ) :
    arg (z - x) = π / 2 - Real.arctan ((z.re - x) / z.im) := by
  have h : 0 < (z - x).im := by simpa using im_pos_of_mem_H hz
  rw [QuantumZipper.Thm11Lyap.arg_eq_pi_div_two_sub_arctan h]
  simp

/-- `x ↦ arg(z − x)/π` is a primitive of the Poisson kernel (the Cauchy distribution function). -/
lemma hasDerivAt_arg_sub_div_pi {z : ℂ} (hz : z ∈ H) (x : ℝ) :
    HasDerivAt (fun t : ℝ => arg (z - t) / π) (poissonKernelH z x) x := by
  have hy := im_pos_of_mem_H hz
  have heq : (fun t : ℝ => arg (z - t) / π) =
      fun t : ℝ => (π / 2 - Real.arctan ((z.re - t) / z.im)) / π := by
    funext t; rw [arg_sub_ofReal_eq hz]
  rw [heq]
  have h1 : HasDerivAt (fun t : ℝ => (z.re - t) / z.im) (-1 / z.im) x := by
    simpa using ((hasDerivAt_id x).const_sub z.re).div_const z.im
  have h2 := (h1.arctan.const_sub (π / 2)).div_const π
  refine h2.congr_deriv ?_
  rw [poissonKernelH, norm_sub_ofReal_sq]
  have hpi := Real.pi_pos
  field_simp
  ring



lemma PoissonH.tendsto_arg_sub_atBot {z : ℂ} (hz : z ∈ H) :
    Tendsto (fun t : ℝ => arg (z - t) / π) atBot (𝓝 0) := by
  have hy := im_pos_of_mem_H hz
  simp_rw [arg_sub_ofReal_eq hz]
  have h1 : Tendsto (fun t : ℝ => (z.re - t) / z.im) atBot atTop := by
    have : Tendsto (fun t : ℝ => z.re - t) atBot atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop
    exact this.atTop_div_const hy
  have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  have h3 := (h2.const_sub (π / 2)).div_const π
  simpa using h3

lemma setIntegral_poissonKernelH_Ioo {z : ℂ} (hz : z ∈ H) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, poissonKernelH z x = arg (z - b) / π - arg (z - a) / π := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_arg_sub_div_pi hz x)
    ((integrable_poissonKernelH hz).intervalIntegrable)

theorem harmonicMeasureH_Ioo {z : ℂ} (hz : z ∈ H) {a b : ℝ} (hab : a ≤ b) :
    harmonicMeasureH z (Ioo a b) =
      ENNReal.ofReal ((arg (z - b) - arg (z - a)) / π) := by
  rw [harmonicMeasureH, withDensity_apply _ measurableSet_Ioo,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernelH hz).integrableOn
      (ae_of_all _ fun x => (poissonKernelH_pos hz x).le), setIntegral_poissonKernelH_Ioo hz hab,
    sub_div]

lemma setIntegral_poissonKernelH_Iio {z : ℂ} (hz : z ∈ H) (b : ℝ) :
    ∫ x in Iio b, poissonKernelH z x = arg (z - b) / π := by
  rw [← integral_Iic_eq_integral_Iio,
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arg_sub_div_pi hz x)
      (integrable_poissonKernelH hz).integrableOn (tendsto_arg_sub_atBot hz), sub_zero]

/-- Harmonic measure of a left half-line: `ω_ℍ(z, (−∞, b)) = arg(z − b)/π`. -/
theorem harmonicMeasureH_Iio {z : ℂ} (hz : z ∈ H) (b : ℝ) :
    harmonicMeasureH z (Iio b) = ENNReal.ofReal (arg (z - b) / π) := by
  rw [harmonicMeasureH, withDensity_apply _ measurableSet_Iio,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernelH hz).integrableOn
      (ae_of_all _ fun x => (poissonKernelH_pos hz x).le), setIntegral_poissonKernelH_Iio hz b]

lemma PoissonH.ae_norm_le_norm_Lp_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (φ : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ‖φ‖ := by
  have hfin : eLpNorm φ ∞ μ ≠ ∞ := (Lp.eLpNorm_lt_top φ).ne
  filter_upwards [ae_le_eLpNormEssSup (f := ⇑φ) (μ := μ)] with x hx
  rw [Lp.norm_def, ← eLpNorm_exponent_top] at *
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hx

lemma integrable_poissonKernelH_mul {z : ℂ} (hz : z ∈ H) (φ : Lp ℝ ∞ (volume : Measure ℝ)) :
    Integrable fun x => poissonKernelH z x * φ x :=
  (integrable_poissonKernelH hz).mul_bdd (Lp.aestronglyMeasurable φ) (ae_norm_le_norm_Lp_top φ)

/-- The Poisson integral is bounded by the `L^∞` norm of the boundary function. -/
theorem abs_poissonIntegralH_le (φ : Lp ℝ ∞ (volume : Measure ℝ)) {z : ℂ} (hz : z ∈ H) :
    |poissonIntegralH φ z| ≤ ‖φ‖ := by
  have h := norm_integral_le_of_norm_le ((integrable_poissonKernelH hz).mul_const ‖φ‖)
    (μ := volume) (f := fun x => poissonKernelH z x * φ x) ?_
  · rw [integral_mul_const, integral_poissonKernelH hz, one_mul] at h
    exact h
  filter_upwards [ae_norm_le_norm_Lp_top φ] with x hx
  rw [norm_mul, Real.norm_of_nonneg (poissonKernelH_pos hz x).le]
  exact mul_le_mul_of_nonneg_left hx (poissonKernelH_pos hz x).le

/-! ### Harmonicity: the Poisson integral is the imaginary part of a holomorphic function -/

/-- The holomorphic kernel `1/(x − z) − 1/(x − i)`; its imaginary part is `π (P(z,x) − P(i,x))`. -/
def PoissonH.cauchyKernelH (z : ℂ) (x : ℝ) : ℂ := 1 / ((x : ℂ) - z) - 1 / ((x : ℂ) - I)

lemma PoissonH.im_one_div_ofReal_sub (z : ℂ) (x : ℝ) :
    (1 / ((x : ℂ) - z)).im = π * poissonKernelH z x := by
  rw [poissonKernelH, one_div, inv_im, norm_sub_rev, ← Complex.normSq_eq_norm_sq]
  have hpi := Real.pi_ne_zero
  by_cases h : Complex.normSq ((x : ℂ) - z) = 0
  · simp [h]
  · simp only [sub_im, ofReal_im, zero_sub, neg_neg]
    field_simp



/-- `1 + x² ≤ K ‖x − w‖²`, uniformly for `w` in a compact part of `ℍ`. -/
lemma PoissonH.one_add_sq_le_mul_norm_sq {w : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hw : δ ≤ w.im) (hR : ‖w‖ ≤ R)
    (x : ℝ) : 1 + x ^ 2 ≤ (2 + (1 + 2 * R ^ 2) / δ ^ 2) * ‖(x : ℂ) - w‖ ^ 2 := by
  rw [norm_sub_rev, norm_sub_ofReal_sq]
  have hre : w.re ^ 2 ≤ R ^ 2 := by
    have h1 := Complex.abs_re_le_norm w
    have h2 : |w.re| ≤ R := h1.trans hR
    calc w.re ^ 2 = |w.re| ^ 2 := (sq_abs _).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have him : δ ^ 2 ≤ w.im ^ 2 := pow_le_pow_left₀ hδ.le hw 2
  have hK : 0 ≤ (1 + 2 * R ^ 2) / δ ^ 2 := by positivity
  have h3 : 1 + 2 * R ^ 2 ≤ (1 + 2 * R ^ 2) / δ ^ 2 * w.im ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left him (by positivity)
  have h4 : 0 ≤ (1 + 2 * R ^ 2) / δ ^ 2 * (x - w.re) ^ 2 := by positivity
  nlinarith [sq_nonneg (x - 2 * w.re), sq_nonneg (x - w.re), sq_nonneg w.im]

lemma PoissonH.ofReal_sub_ne_zero {z : ℂ} (hz : z ∈ H) (x : ℝ) : (x : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, ofReal_im, zero_sub, zero_im] at this
  linarith [im_pos_of_mem_H hz]

lemma PoissonH.I_mem_H : I ∈ H := by show (0 : ℝ) < I.im; simp

lemma PoissonH.measurable_cauchyKernelH (z : ℂ) : Measurable (cauchyKernelH z) := by
  unfold cauchyKernelH; fun_prop

lemma PoissonH.aestronglyMeasurable_ofReal_Lp (φ : Lp ℝ ∞ (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x => ((φ x : ℝ) : ℂ)) volume :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable φ)

lemma PoissonH.one_div_mul_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (a * b) ≤ 1 / a ^ 2 + 1 / b ^ 2 := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), mul_pos ha hb]

lemma PoissonH.norm_cauchyKernelH_le {z : ℂ} (hz : z ∈ H) (x : ℝ) :
    ‖cauchyKernelH z x‖ ≤ ‖z - I‖ * (2 + (1 + 2 * ‖z‖ ^ 2) / z.im ^ 2 + 1) * (1 + x ^ 2)⁻¹ := by
  have h1 := ofReal_sub_ne_zero hz x
  have h2 := ofReal_sub_ne_zero I_mem_H x
  have hk : cauchyKernelH z x = (z - I) / (((x : ℂ) - z) * ((x : ℂ) - I)) := by
    unfold cauchyKernelH; field_simp; ring
  have hxI : ‖(x : ℂ) - I‖ ^ 2 = 1 + x ^ 2 := by rw [norm_sub_rev, norm_sub_ofReal_sq]; simp; ring
  have ha : 0 < ‖(x : ℂ) - z‖ := norm_pos_iff.2 h1
  have hb : 0 < ‖(x : ℂ) - I‖ := norm_pos_iff.2 h2
  set K := 2 + (1 + 2 * ‖z‖ ^ 2) / z.im ^ 2
  have hKa := one_add_sq_le_mul_norm_sq (im_pos_of_mem_H hz) le_rfl le_rfl x
  rw [hk, norm_div, norm_mul, div_eq_mul_one_div, mul_assoc]
  gcongr
  have hx : 0 < 1 + x ^ 2 := by positivity
  refine (one_div_mul_le _ _ ha hb).trans ?_
  rw [hxI, add_mul, one_mul]
  gcongr
  · rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, ← div_eq_mul_inv,
      le_div_iff₀ hx, one_mul, mul_comm]
    exact hKa
  · exact le_of_eq (one_div _)

lemma PoissonH.integrable_ofReal_mul_cauchyKernelH (φ : Lp ℝ ∞ (volume : Measure ℝ)) {z : ℂ} (hz : z ∈ H) :
    Integrable fun x => ((φ x : ℝ) : ℂ) * cauchyKernelH z x := by
  refine Integrable.bdd_mul (c := ‖φ‖) ?_ (aestronglyMeasurable_ofReal_Lp φ) ?_
  · exact Integrable.mono' (integrable_inv_one_add_sq.const_mul
      (‖z - I‖ * (2 + (1 + 2 * ‖z‖ ^ 2) / z.im ^ 2 + 1)))
      (measurable_cauchyKernelH z).aestronglyMeasurable
      (ae_of_all _ fun x => norm_cauchyKernelH_le hz x)
  · filter_upwards [ae_norm_le_norm_Lp_top φ] with x hx
    simpa using hx

/-- Holomorphy of the Cauchy-type integral `∫ φ(x) (1/(x − z) − 1/(x − i)) dx` on `ℍ`. -/
lemma PoissonH.hasDerivAt_integral_cauchyKernelH (φ : Lp ℝ ∞ (volume : Measure ℝ)) {z₀ : ℂ} (hz₀ : z₀ ∈ H) :
    HasDerivAt (fun z => ∫ x, ((φ x : ℝ) : ℂ) * cauchyKernelH z x)
      (∫ x, ((φ x : ℝ) : ℂ) * (1 / ((x : ℂ) - z₀) ^ 2)) z₀ := by
  have hy := im_pos_of_mem_H hz₀
  set ε := z₀.im / 2 with hε
  have hεpos : 0 < ε := by positivity
  set R := ‖z₀‖ + ε
  set K := 2 + (1 + 2 * R ^ 2) / ε ^ 2
  have hball : ∀ z ∈ ball z₀ ε, ε ≤ z.im ∧ ‖z‖ ≤ R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
    rw [sub_im] at h1
    refine ⟨?_, ?_⟩
    · have := (abs_le.1 h1).1; linarith
    · have := norm_le_norm_add_norm_sub' z z₀
      have h2 : ‖z - z₀‖ ≤ ε := hz.le
      calc ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
            have := norm_sub_norm_le z z₀; linarith
        _ ≤ R := by linarith
  have hballH : ∀ z ∈ ball z₀ ε, z ∈ H := fun z hz =>
    show 0 < z.im from lt_of_lt_of_le hεpos (hball z hz).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z x => ((φ x : ℝ) : ℂ) * cauchyKernelH z x)
    (F' := fun z x => ((φ x : ℝ) : ℂ) * (1 / ((x : ℂ) - z) ^ 2))
    (bound := fun x => ‖φ‖ * (K * (1 + x ^ 2)⁻¹)) (ball_mem_nhds z₀ hεpos)
    (Eventually.of_forall fun z =>
      (aestronglyMeasurable_ofReal_Lp φ).mul (measurable_cauchyKernelH z).aestronglyMeasurable)
    (integrable_ofReal_mul_cauchyKernelH φ hz₀)
    ((aestronglyMeasurable_ofReal_Lp φ).mul (by fun_prop : Measurable fun x : ℝ =>
      1 / ((x : ℂ) - z₀) ^ 2).aestronglyMeasurable) ?_
    ((integrable_inv_one_add_sq.const_mul K).const_mul ‖φ‖) ?_
  · exact key.2
  · filter_upwards [ae_norm_le_norm_Lp_top φ] with x hx z hz
    obtain ⟨h1, h2⟩ := hball z hz
    rw [norm_mul, Complex.norm_real]
    gcongr
    have hne := ofReal_sub_ne_zero (hballH z hz) x
    have hpos : 0 < ‖(x : ℂ) - z‖ ^ 2 := by positivity
    have hb := one_add_sq_le_mul_norm_sq hεpos h1 h2 x
    rw [norm_div, norm_one, norm_pow, div_le_iff₀ hpos, mul_assoc, ← div_eq_inv_mul,
      ← mul_div_assoc, le_div_iff₀ (by positivity), one_mul]
    exact hb
  · refine ae_of_all _ fun x z hz => ?_
    have hne := ofReal_sub_ne_zero (hballH z hz) x
    have h1 : HasDerivAt (fun w : ℂ => (x : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (x : ℂ)
    have h2 := ((h1.inv hne).sub_const (1 / ((x : ℂ) - I))).const_mul ((φ x : ℝ) : ℂ)
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · exact Eventually.of_forall fun w => by simp [cauchyKernelH]

/-- On `ℍ`, the Poisson integral is `Im G / π` plus a constant, `G` the Cauchy-type integral. -/
lemma PoissonH.poissonIntegralH_eq_im (φ : Lp ℝ ∞ (volume : Measure ℝ)) {z : ℂ} (hz : z ∈ H) :
    poissonIntegralH φ z =
      (∫ x, ((φ x : ℝ) : ℂ) * cauchyKernelH z x).im / π + poissonIntegralH φ I := by
  have him := integral_im (integrable_ofReal_mul_cauchyKernelH φ hz)
  simp only [RCLike.im_to_complex] at him
  rw [← him]
  have hpt : ∀ x : ℝ, (((φ x : ℝ) : ℂ) * cauchyKernelH z x).im =
      π * (poissonKernelH z x * φ x) - π * (poissonKernelH I x * φ x) := by
    intro x
    rw [im_ofReal_mul, cauchyKernelH, sub_im, im_one_div_ofReal_sub, im_one_div_ofReal_sub]
    ring
  simp_rw [hpt]
  rw [integral_sub ((integrable_poissonKernelH_mul hz φ).const_mul π)
      ((integrable_poissonKernelH_mul I_mem_H φ).const_mul π), integral_const_mul,
    integral_const_mul]
  unfold poissonIntegralH
  have hpi := Real.pi_ne_zero
  field_simp
  ring

/-- The Poisson integral of an `L^∞` function is harmonic on `ℍ`. -/
theorem harmonicOnNhd_poissonIntegralH (φ : Lp ℝ ∞ (volume : Measure ℝ)) :
    InnerProductSpace.HarmonicOnNhd (poissonIntegralH φ) H := by
  intro z₀ hz₀
  set G : ℂ → ℂ := fun z => ∫ x, ((φ x : ℝ) : ℂ) * cauchyKernelH z x
  have hdiff : DifferentiableOn ℂ G H := fun z hz =>
    (hasDerivAt_integral_cauchyKernelH φ hz).differentiableAt.differentiableWithinAt
  have hana : AnalyticAt ℂ G z₀ := hdiff.analyticAt (QuantumZipper.isOpen_H.mem_nhds hz₀)
  have h1 : InnerProductSpace.HarmonicAt (fun z => (G z).im) z₀ := hana.harmonicAt_im
  have h2 : InnerProductSpace.HarmonicAt
      (fun z => (π⁻¹ : ℝ) • (G z).im + poissonIntegralH φ I) z₀ :=
    (h1.const_smul).add (InnerProductSpace.harmonicAt_const _)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h2
  filter_upwards [QuantumZipper.isOpen_H.mem_nhds hz₀] with z hz
  rw [poissonIntegralH_eq_im φ hz, smul_eq_mul, div_eq_inv_mul]

/-! ### Boundary values -/

/-- Harmonic measure of a neighbourhood interval tends to `1` at an interior boundary point. -/
lemma PoissonH.tendsto_arg_sub_sub_arg_sub {a b x₀ : ℝ} (ha : a < x₀) (hb : x₀ < b) :
    Tendsto (fun z : ℂ => (arg (z - b) - arg (z - a)) / π) (𝓝[H] (x₀ : ℂ)) (𝓝 1) := by
  have h1 : Tendsto (fun z : ℂ => arg (z - b)) (𝓝[H] (x₀ : ℂ)) (𝓝 π) := by
    have hre : ((x₀ : ℂ) - b).re < 0 := by simp; linarith
    have him : ((x₀ : ℂ) - b).im = 0 := by simp
    refine (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_sub_right (b : ℂ)).tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      show 0 ≤ (z - b).im
      simpa using (im_pos_of_mem_H hz).le
  have h2 : Tendsto (fun z : ℂ => arg (z - a)) (𝓝[H] (x₀ : ℂ)) (𝓝 0) := by
    have hmem : ((x₀ : ℂ) - a) ∈ slitPlane := by
      rw [← ofReal_sub, ofReal_mem_slitPlane]; linarith
    have hc := (continuousAt_arg hmem).tendsto.comp
      (((continuous_sub_right (a : ℂ)).tendsto (x₀ : ℂ)).mono_left (nhdsWithin_le_nhds (s := H)))
    rwa [← ofReal_sub, arg_ofReal_of_nonneg (by linarith)] at hc
  have := (h1.sub h2).div_const π
  rwa [sub_zero, div_self Real.pi_ne_zero] at this

/-- The approximate-identity estimate behind the boundary limits. -/
lemma abs_poissonIntegralH_sub_le (φ : Lp ℝ ∞ (volume : Measure ℝ)) {z : ℂ} (hz : z ∈ H)
    {a b c ε M : ℝ} (hab : a ≤ b) (hε : 0 ≤ ε)
    (hin : ∀ᵐ t ∂volume, t ∈ Ioo a b → |φ t - c| ≤ ε) (hM : ∀ᵐ t ∂volume, |φ t - c| ≤ M) :
    |poissonIntegralH φ z - c| ≤ ε + M * (1 - (arg (z - b) - arg (z - a)) / π) := by
  have hP := integrable_poissonKernelH hz
  have hdiff : poissonIntegralH φ z - c = ∫ x, poissonKernelH z x * (φ x - c) := by
    have h1 : (fun x => poissonKernelH z x * (φ x - c)) =
        fun x => poissonKernelH z x * φ x - poissonKernelH z x * c := by
      funext x; ring
    rw [h1, integral_sub (integrable_poissonKernelH_mul hz φ) (hP.mul_const c), integral_mul_const,
      integral_poissonKernelH hz, one_mul, poissonIntegralH]
  set s := Ioo a b
  have hg : Integrable fun x => poissonKernelH z x * ε + sᶜ.indicator (fun x => poissonKernelH z x * M) x :=
    (hP.mul_const ε).add ((hP.mul_const M).indicator measurableSet_Ioo.compl)
  have hle := norm_integral_le_of_norm_le hg (f := fun x => poissonKernelH z x * (φ x - c)) ?_
  · rw [Real.norm_eq_abs, ← hdiff] at hle
    refine hle.trans (le_of_eq ?_)
    rw [integral_add (hP.mul_const ε) ((hP.mul_const M).indicator measurableSet_Ioo.compl),
      integral_mul_const, integral_poissonKernelH hz, integral_indicator measurableSet_Ioo.compl,
      setIntegral_compl measurableSet_Ioo (hP.mul_const M), integral_mul_const,
      integral_mul_const, integral_poissonKernelH hz, setIntegral_poissonKernelH_Ioo hz hab]
    ring
  · filter_upwards [hin, hM] with t hin hM
    have hPt := (poissonKernelH_pos hz t).le
    rw [norm_mul, Real.norm_of_nonneg hPt, Real.norm_eq_abs]
    by_cases ht : t ∈ s
    · rw [indicator_of_notMem (by simpa using ht), add_zero]
      exact mul_le_mul_of_nonneg_left (hin ht) hPt
    · rw [indicator_of_mem (by simpa using ht)]
      have : 0 ≤ poissonKernelH z t * ε := mul_nonneg hPt hε
      nlinarith [mul_le_mul_of_nonneg_left hM hPt]

/-- Boundary values: at a point where a bounded measurable representative is continuous. -/
theorem tendsto_poissonIntegralH {φ : Lp ℝ ∞ (volume : Measure ℝ)} {f : ℝ → ℝ}
    (hf : ⇑φ =ᵐ[volume] f) {x : ℝ} (hx : ContinuousAt f x) :
    Tendsto (poissonIntegralH φ) (𝓝[H] (x : ℂ)) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hx (ε / 2) (by positivity)
  set M := ‖φ‖ + |f x| with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hM : ∀ᵐ t ∂volume, |φ t - f x| ≤ M := by
    filter_upwards [ae_norm_le_norm_Lp_top φ] with t ht
    rw [Real.norm_eq_abs] at ht
    exact (abs_sub _ _).trans (by linarith)
  have hin : ∀ᵐ t ∂volume, t ∈ Ioo (x - δ) (x + δ) → |φ t - f x| ≤ ε / 2 := by
    filter_upwards [hf] with t ht hmem
    rw [ht]
    have hd : dist t x < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hmem.1, hmem.2]
    exact (hfδ hd).le
  set η := ε / (2 * (M + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hlim := tendsto_arg_sub_sub_arg_sub (x₀ := x) (a := x - δ) (b := x + δ)
    (by linarith) (by linarith)
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (Metric.ball_mem_nhds 1 hη)] with z hz hω
  rw [Real.dist_eq]
  have hest := abs_poissonIntegralH_sub_le φ hz (by linarith : x - δ ≤ x + δ) (by positivity) hin hM
  rw [Real.dist_eq] at hω
  have h1 : M * (1 - (arg (z - ↑(x + δ)) - arg (z - ↑(x - δ))) / π) ≤ M * η := by
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have := (abs_lt.1 hω).1
    linarith
  have h2 : M * η < ε / 2 := by
    rw [hηdef, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-! ### Möbius invariance -/

section Mobius

variable {a b c d : ℝ}

/-- The pointwise transformation rule of the Poisson kernel under a real Möbius map `m`:
`P(m z, m x) · m'(x) = P(z, x)` with `m'(x) = (ad − bc)/(cx + d)²`. -/
lemma poissonKernelH_realMobius (h : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ H) {x : ℝ}
    (hx : c * x + d ≠ 0) :
    (a * d - b * c) / (c * x + d) ^ 2 *
        poissonKernelH (QuantumZipper.CA.realMobius a b c d z) ((a * x + b) / (c * x + d)) =
      poissonKernelH z x := by
  have hzd := QuantumZipper.CA.realMobius_denom_ne_zero h hz
  have hxc : ((c * x + d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  have hzx := ofReal_sub_ne_zero hz x
  have hsub : QuantumZipper.CA.realMobius a b c d z - (((a * x + b) / (c * x + d) : ℝ) : ℂ) =
      ((a * d - b * c : ℝ) : ℂ) * (z - x) / ((c * z + d) * ((c * x + d : ℝ) : ℂ)) := by
    rw [QuantumZipper.CA.realMobius]
    push_cast at hxc ⊢
    rw [div_sub_div _ _ hzd hxc]
    congr 1
    ring
  simp only [poissonKernelH]
  rw [hsub, QuantumZipper.CA.realMobius_im, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal]
  have h1 : 0 < Complex.normSq (c * z + d) := Complex.normSq_pos.2 hzd
  have h2 : 0 < Complex.normSq (z - x) := by
    rw [← neg_sub, Complex.normSq_neg]; exact Complex.normSq_pos.2 hzx
  have hpi := Real.pi_pos
  field_simp

lemma PoissonH.hasDerivAt_realMobius_real {x : ℝ} (hx : c * x + d ≠ 0) :
    HasDerivAt (fun t : ℝ => (a * t + b) / (c * t + d)) ((a * d - b * c) / (c * x + d) ^ 2) x := by
  have h1 : HasDerivAt (fun t : ℝ => a * t + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h2 : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  exact (h1.div h2 hx).congr_deriv (by ring)

lemma PoissonH.injOn_realMobius_real (h : 0 < a * d - b * c) :
    InjOn (fun t : ℝ => (a * t + b) / (c * t + d)) {t | c * t + d ≠ 0} := by
  intro x hx y hy hxy
  simp only [mem_ofPred_eq] at hx hy hxy
  rw [div_eq_div_iff hx hy] at hxy
  have : (a * d - b * c) * (x - y) = 0 := by linear_combination hxy
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · linarith

lemma PoissonH.subset_image_realMobius_real (h : 0 < a * d - b * c) :
    {y : ℝ | c * y ≠ a} ⊆ (fun t : ℝ => (a * t + b) / (c * t + d)) '' {t | c * t + d ≠ 0} := by
  intro y hy
  simp only [mem_ofPred_eq] at hy
  have hy' : a - c * y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  refine ⟨(d * y - b) / (a - c * y), ?_, ?_⟩
  · simp only [mem_ofPred_eq]
    rw [show c * ((d * y - b) / (a - c * y)) + d = (a * d - b * c) / (a - c * y) by
      field_simp; ring]
    exact div_ne_zero h.ne' hy'
  · have hden : c * ((d * y - b) / (a - c * y)) + d = (a * d - b * c) / (a - c * y) := by
      field_simp; ring
    simp only
    have hy'' : a - y * c ≠ 0 := by rwa [mul_comm]
    rw [hden, div_eq_iff (div_ne_zero h.ne' hy')]
    field_simp
    ring

lemma PoissonH.measure_setOf_mul_add_eq_zero (h : 0 < a * d - b * c) :
    (volume : Measure ℝ) {t | c * t + d = 0} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  simp only [mem_ofPred_eq] at hx hy
  by_cases hc : c = 0
  · subst hc; simp at hx; subst hx; simp at h
  · have : c * (x - y) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hc
    · linarith

lemma PoissonH.measure_setOf_mul_eq (h : 0 < a * d - b * c) :
    (volume : Measure ℝ) {y | c * y = a} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  simp only [mem_ofPred_eq] at hx hy
  by_cases hc : c = 0
  · subst hc; simp at hx; subst hx; simp at h
  · have : c * (x - y) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hc
    · linarith

/-- **Conformal invariance of harmonic measure under real Möbius maps** ([Gar] Ch. I): for
`m(z) = (az + b)/(cz + d)` with `ad − bc > 0`, the image of `ω_ℍ(z, ·)` under the boundary
action `x ↦ m(x)` is `ω_ℍ(m(z), ·)`. (At the pole `x = −d/c` the real formula takes Lean's junk
value; that single point is null for `ω_ℍ(z, ·)`, so the image measure is unaffected.) -/
theorem harmonicMeasureH_mobius (h : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ H) :
    (harmonicMeasureH z).map (fun x : ℝ => (a * x + b) / (c * x + d)) =
      harmonicMeasureH (QuantumZipper.CA.realMobius a b c d z) := by
  set m : ℝ → ℝ := fun x => (a * x + b) / (c * x + d) with hmdef
  have hm : Measurable m := by fun_prop
  set G : Set ℝ := {t | c * t + d ≠ 0} with hGdef
  have hGc : Gᶜ = {t : ℝ | c * t + d = 0} := by ext t; simp [hGdef]
  have hGm : MeasurableSet G := by
    have : MeasurableSet {t : ℝ | c * t + d = 0} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    rw [← compl_compl G, hGc]; exact this.compl
  ext E hE
  rw [Measure.map_apply hm hE]
  set s := m ⁻¹' E ∩ G with hsdef
  have hs : MeasurableSet s := (hm hE).inter hGm
  have hnull : harmonicMeasureH z Gᶜ = 0 := by
    rw [hGc]
    exact withDensity_absolutelyContinuous _ _ (measure_setOf_mul_add_eq_zero h)
  rw [← measure_inter_conull hnull, harmonicMeasureH, withDensity_apply _ hs]
  have hcongr : ∫⁻ x in s, ENNReal.ofReal (poissonKernelH z x) =
      ∫⁻ x in s, ENNReal.ofReal |(a * d - b * c) / (c * x + d) ^ 2| *
        ENNReal.ofReal (poissonKernelH (QuantumZipper.CA.realMobius a b c d z) (m x)) := by
    refine setLIntegral_congr_fun hs fun x hx => ?_
    have hx' : c * x + d ≠ 0 := hx.2
    have hpos : 0 < (a * d - b * c) / (c * x + d) ^ 2 := div_pos h (by positivity)
    rw [abs_of_pos hpos, ← ENNReal.ofReal_mul hpos.le, poissonKernelH_realMobius h hz hx']
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (f := m)
    (f' := fun x => (a * d - b * c) / (c * x + d) ^ 2) hs
    (fun x hx => (hasDerivAt_realMobius_real hx.2).hasDerivWithinAt)
    ((injOn_realMobius_real h).mono inter_subset_right)
    (fun y => ENNReal.ofReal (poissonKernelH (QuantumZipper.CA.realMobius a b c d z) y))
  rw [hcongr, ← hcv, ← withDensity_apply']
  change harmonicMeasureH _ (m '' s) = harmonicMeasureH _ E
  refine le_antisymm (measure_mono ?_) ?_
  · rintro y ⟨t, ht, rfl⟩; exact ht.1
  · have hN : harmonicMeasureH (QuantumZipper.CA.realMobius a b c d z) {y | c * y = a} = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_setOf_mul_eq h)
    calc harmonicMeasureH _ E ≤ harmonicMeasureH _ (m '' s ∪ {y | c * y = a}) := by
          refine measure_mono fun y hy => ?_
          by_cases hya : c * y = a
          · exact Or.inr hya
          · obtain ⟨t, ht, hty⟩ := subset_image_realMobius_real h hya
            refine Or.inl ⟨t, ⟨?_, ht⟩, hty⟩
            show m t ∈ E
            rw [show m t = y from hty]; exact hy
      _ ≤ harmonicMeasureH _ (m '' s) + harmonicMeasureH _ {y | c * y = a} := measure_union_le _ _
      _ = harmonicMeasureH _ (m '' s) := by rw [hN, add_zero]

end Mobius

/-! ### Bridge to the explicit step-data extension -/

namespace StepData

variable (s : StepData)

/-- The breakpoint count `#{j | x j ≤ t}` as a sum of indicators. -/
lemma measurable_card_filter_le :
    Measurable fun t : ℝ => (Finset.univ.filter fun j => s.x j ≤ t).card := by
  have h : (fun t : ℝ => (Finset.univ.filter fun j => s.x j ≤ t).card) =
      fun t => ∑ j : Fin s.n, if s.x j ≤ t then 1 else 0 := by
    funext t; rw [Finset.card_filter]
  rw [h]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma measurable_bdry : Measurable s.bdry := by
  set g : ℕ → ℝ := fun k => if hk : k < s.n + 1 then s.v ⟨k, hk⟩ else 0
  have h : s.bdry = g ∘ fun t : ℝ => (Finset.univ.filter fun j => s.x j ≤ t).card := by
    funext t
    simp only [Function.comp, g, bdry]
    split_ifs with hk
    · rfl
    · exact absurd (Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))) hk
  rw [h]
  exact measurable_from_nat.comp s.measurable_card_filter_le

lemma abs_bdry_le (t : ℝ) : |s.bdry t| ≤ ∑ k, |s.v k| :=
  Finset.single_le_sum (f := fun k => |s.v k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)

lemma memLp_bdry : MemLp s.bdry ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound s.measurable_bdry.aestronglyMeasurable _
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact s.abs_bdry_le t)

/-- The boundary function as an element of `L^∞(ℝ)`. -/
def bdryLp : Lp ℝ ∞ (volume : Measure ℝ) := s.memLp_bdry.toLp s.bdry

lemma coeFn_bdryLp : ⇑s.bdryLp =ᵐ[volume] s.bdry := s.memLp_bdry.coeFn_toLp

/-- Off the breakpoints the boundary function is locally constant. -/
lemma continuousAt_bdry {t : ℝ} (ht : ∀ j, s.x j ≠ t) : ContinuousAt s.bdry t := by
  have hev : ∀ᶠ t' in 𝓝 t, ∀ j, (s.x j ≤ t' ↔ s.x j ≤ t) := by
    refine Filter.eventually_all.2 fun j => ?_
    rcases lt_or_gt_of_ne (ht j) with hj | hj
    · filter_upwards [Ioi_mem_nhds hj] with t' ht'
      exact ⟨fun _ => hj.le, fun _ => (le_of_lt ht')⟩
    · filter_upwards [Iio_mem_nhds hj] with t' ht'
      exact ⟨fun h => absurd (h.trans_lt ht') (lt_irrefl _), fun h => absurd (h.trans_lt hj) (lt_irrefl _)⟩
  refine (continuousAt_const (y := s.bdry t)).congr ?_
  filter_upwards [hev] with t' ht'
  unfold bdry
  congr 2
  rw [Finset.filter_congr fun j _ => (ht' j).symm]

/-- **The explicit extension is the Poisson integral** of the boundary function: for any
`L^∞` representative `φ` of `s.bdry`, `s.harmonicExtH = poissonIntegralH φ` on `ℍ`. -/
theorem harmonicExtH_eq_poissonIntegralH {φ : Lp ℝ ∞ (volume : Measure ℝ)}
    (hφ : ⇑φ =ᵐ[volume] s.bdry) {z : ℂ} (hz : z ∈ H) :
    s.harmonicExtH z = poissonIntegralH φ z := by
  refine (s.eqOn_harmonicExtH (harmonicOnNhd_poissonIntegralH φ) ?_ ?_ hz).symm
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := ‖φ‖)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_poissonIntegralH_le φ hw
  · intro t ht
    exact tendsto_poissonIntegralH hφ (s.continuousAt_bdry ht)

/-- The bridge with the canonical `L^∞` representative `s.bdryLp`. -/
theorem harmonicExtH_eq_poissonIntegralH_bdryLp {z : ℂ} (hz : z ∈ H) :
    s.harmonicExtH z = poissonIntegralH s.bdryLp z :=
  s.harmonicExtH_eq_poissonIntegralH s.coeFn_bdryLp hz

end StepData

end InteractingSLE
