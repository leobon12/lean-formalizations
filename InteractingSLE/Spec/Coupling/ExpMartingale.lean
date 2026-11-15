import MathFin.Probability.Martingales.LevyExpMartingale
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Characteristic-function martingales of a martingale with a Lipschitz bracket

Packet PROVE-T11-L311 (Specification §3.3, `source/spec/p049-096.md#33-proof-of-theorem-11`, L550–L552; graph
node `SPEC.thm-1.1#charfn-martingale`): "Since `E_t(φ) ≥ 0`, the bracket increment is bounded by `E_0(φ)` … The
characteristic-function martingale `exp(iθ(𝔥_t, φ) − θ² E_t(φ)/2)` is bounded in modulus by one. Optional stopping
at these protected-domain stops is therefore valid." This file is the abstract (process-free) layer of that step.

Let `M` be a bounded martingale with continuous paths and `A` a bracket: `M² − A` is a martingale, `A₀ = 0`, and
`A` is nondecreasing and Lipschitz in time. Then

* `martingale_exp_of_bracket`: `exp(a M − a² A/2)` is a martingale for every real `a` (MathFin's
  `LevyExpMartingale.martingale_exp` for a slow clock, after rescaling time-independently by the Lipschitz
  constant);
* `integral_cexp_eq_of_forall_real`: identities `∫ exp(a Y + a² V/2) dμ = ∫ exp(a Y' + a² V'/2) dν` for every
  real `a` (bounded `Y, V, Y', V'`) continue to every complex `a` (both sides are entire);
* `setIntegral_cexp_eq_of_bracket`: hence the characteristic-function identity
  `∫_S exp(iθ M_t + θ² A_t/2) = ∫_S exp(iθ M_s + θ² A_s/2)` for `s ≤ t` and `S ∈ 𝓕_s`;
* `map_eq_gaussianReal_of_condExp`: the abstract core of Lemma 3.11 — a variable whose conditional characteristic
  function given `𝒢` is that of `N(m, v)` (`m, v` random), with `E[exp(iθ m − θ² v/2)] = exp(iθ m₀ − θ² v₀/2)`
  for every `θ`, has the law `N(m₀, v₀)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### The real exponential martingale -/

section ExpMart

variable [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ} {K c : ℝ}

/-- **Exponential martingale of a bounded continuous martingale with a Lipschitz bracket.** If `M` is a bounded
martingale with continuous paths, `M² − A` is a martingale, `A₀ = 0`, `A` is nondecreasing and
`A_q − A_p ≤ c (q − p)`, then `exp(a M − a² A/2)` is a martingale for every real `a`. -/
theorem martingale_exp_of_bracket (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t => M t ω)
    (hA0 : ∀ ω, A 0 ω = 0) (hAmono : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A p ω ≤ A q ω)
    (hAlip : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A q ω - A p ω ≤ c * ((q : ℝ) - p)) (a : ℝ) :
    Martingale (fun t ω => Real.exp (a * M t ω - a ^ 2 * A t ω / 2)) 𝓕 P := by
  set c' : ℝ := max c 1 with hc'
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r : ℝ := Real.sqrt c' with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hc'0
  have hrr : r ^ 2 = c' := Real.sq_sqrt hc'0.le
  have hslow : MathFin.LevyQuadraticSums.IsSlowClock (fun t ω => A t ω / c') :=
    { zero := fun ω => by simp [hA0 ω]
      sub_nonneg := fun p q hpq ω => by
        rw [← sub_div]; exact div_nonneg (sub_nonneg.2 (hAmono hpq ω)) hc'0.le
      sub_le := fun p q hpq ω => by
        rw [← sub_div, div_le_iff₀ hc'0]
        have hpq' : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.2 (by exact_mod_cast hpq)
        calc A q ω - A p ω ≤ c * ((q : ℝ) - p) := hAlip hpq ω
          _ ≤ c' * ((q : ℝ) - p) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpq'
          _ = ((q : ℝ) - p) * c' := by ring }
  have hM' : Martingale (fun t ω => r⁻¹ * M t ω) 𝓕 P := hM.smul r⁻¹
  have hM2' : Martingale (fun t ω => (r⁻¹ * M t ω) ^ 2 - A t ω / c') 𝓕 P := by
    have h := hM2.smul c'⁻¹
    convert h using 1
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, inv_pow, hrr]
    ring
  have hK' : ∀ t ω, |r⁻¹ * M t ω| ≤ r⁻¹ * K := fun t ω => by
    rw [abs_mul, abs_of_pos (inv_pos.2 hr0)]
    exact mul_le_mul_of_nonneg_left (hK t ω) (inv_pos.2 hr0).le
  have hcont' : ∀ ω, Continuous fun t => r⁻¹ * M t ω := fun ω => (hcont ω).const_mul _
  have h := MathFin.LevyExpMartingale.martingale_exp hslow hM' hM2' hK' hcont' (a * r)
  convert h using 1
  funext t ω
  congr 1
  field_simp
  rw [hrr]
  ring

end ExpMart

/-! ### Analytic continuation from real to complex exponents -/

section Continuation

/-- The pointwise derivative of `z ↦ exp(z y + z² v/2)`. -/
theorem hasDerivAt_cexp_quad (y v : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (z * y + z ^ 2 * v / 2))
      ((y + z * v) * Complex.exp (z * y + z ^ 2 * v / 2)) z := by
  have h1 : HasDerivAt (fun z : ℂ => z * y + z ^ 2 * v / 2) (y + z * v) z :=
    (((hasDerivAt_id' z).mul_const (y : ℂ)).add
      (((hasDerivAt_pow 2 z).mul_const (v : ℂ)).div_const 2)).congr_deriv (by push_cast; ring)
  exact h1.cexp.congr_deriv (by ring)

theorem norm_cexp_quad_le {y v K R : ℝ} (hy : |y| ≤ K) (hv : |v| ≤ K) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (z * y + z ^ 2 * v / 2)‖ ≤ Real.exp (R * K + R ^ 2 * K / 2) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hy
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
  calc ‖z * y + z ^ 2 * v / 2‖ ≤ ‖z * y‖ + ‖z ^ 2 * v / 2‖ := norm_add_le _ _
    _ = ‖z‖ * |y| + ‖z‖ ^ 2 * |v| / 2 := by
        rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_two]
    _ ≤ R * K + R ^ 2 * K / 2 := by
        have h0 : 0 ≤ ‖z‖ := norm_nonneg z
        have hR : 0 ≤ R := h0.trans hz
        gcongr

variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-- `z ↦ ∫ exp(z Y + z² V/2) dμ` is entire, for bounded measurable `Y, V` and a finite measure `μ`. -/
theorem differentiable_integral_cexp_quad {Y V : Ω → ℝ} (hY : Measurable Y) (hV : Measurable V)
    {K : ℝ} (hYb : ∀ ω, |Y ω| ≤ K) (hVb : ∀ ω, |V ω| ≤ K) :
    Differentiable ℂ (fun z : ℂ => ∫ ω, Complex.exp (z * Y ω + z ^ 2 * V ω / 2) ∂μ) := by
  intro z₀
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun ω => Complex.exp (z * Y ω + z ^ 2 * V ω / 2)) μ := fun z =>
    (by fun_prop : Measurable fun ω => Complex.exp (z * Y ω + z ^ 2 * V ω / 2)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun ω => ((Y ω : ℂ) + z₀ * V ω) * Complex.exp (z₀ * Y ω + z₀ ^ 2 * V ω / 2)) μ :=
    (by fun_prop : Measurable
      fun ω => ((Y ω : ℂ) + z₀ * V ω) * Complex.exp (z₀ * Y ω + z₀ ^ 2 * V ω / 2)).aestronglyMeasurable
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set C : ℝ := (|K| + R * |K|) * Real.exp (R * |K| + R ^ 2 * |K| / 2) with hC
  have hYb' : ∀ ω, |Y ω| ≤ |K| := fun ω => (hYb ω).trans (le_abs_self K)
  have hVb' : ∀ ω, |V ω| ≤ |K| := fun ω => (hVb ω).trans (le_abs_self K)
  have hball : ∀ z ∈ Metric.ball z₀ 1, ‖z‖ ≤ R := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := norm_le_insert' z z₀
    have h2 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
    linarith
  have hbound : ∀ ω, ∀ z ∈ Metric.ball z₀ 1,
      ‖((Y ω : ℂ) + z * V ω) * Complex.exp (z * Y ω + z ^ 2 * V ω / 2)‖ ≤ C := by
    intro ω z hz
    have hzR := hball z hz
    rw [norm_mul]
    refine mul_le_mul ?_ (norm_cexp_quad_le (hYb' ω) (hVb' ω) hzR) (norm_nonneg _)
      (by positivity)
    calc ‖(Y ω : ℂ) + z * V ω‖ ≤ ‖(Y ω : ℂ)‖ + ‖z * V ω‖ := norm_add_le _ _
      _ = |Y ω| + ‖z‖ * |V ω| := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |K| + R * |K| := add_le_add (hYb' ω)
          (mul_le_mul hzR (hVb' ω) (abs_nonneg _) hR0)
  have hint0 : Integrable (fun ω => Complex.exp (z₀ * Y ω + z₀ ^ 2 * V ω / 2)) μ :=
    Integrable.of_bound (hmeas z₀) (Real.exp (R * |K| + R ^ 2 * |K| / 2))
      (ae_of_all _ fun ω => norm_cexp_quad_le (hYb' ω) (hVb' ω) (by rw [hR]; linarith))
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z ω => Complex.exp (z * Y ω + z ^ 2 * V ω / 2))
    (F' := fun z ω => ((Y ω : ℂ) + z * V ω) * Complex.exp (z * Y ω + z ^ 2 * V ω / 2))
    (bound := fun _ => C) (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall hmeas) hint0
    hmeas' (ae_of_all _ hbound) (integrable_const C)
    (ae_of_all _ fun ω z _ => hasDerivAt_cexp_quad (Y ω) (V ω) z)
  exact h.differentiableAt

omit [IsFiniteMeasure μ] in
/-- `∫ exp(a Y + a² V/2) dμ` at a real `a` is the real integral. -/
theorem integral_cexp_quad_ofReal (Y V : Ω → ℝ) (a : ℝ) :
    ∫ ω, Complex.exp ((a : ℂ) * Y ω + (a : ℂ) ^ 2 * V ω / 2) ∂μ =
      ((∫ ω, Real.exp (a * Y ω + a ^ 2 * V ω / 2) ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext ω
  push_cast
  rfl

/-- **Analytic continuation.** If `∫ exp(a Y + a² V/2) dμ = ∫ exp(a Y' + a² V'/2) dν` for every real `a`
(bounded measurable `Y, V, Y', V'`, finite measures), the same holds for every complex `a`. -/
theorem integral_cexp_eq_of_forall_real {ν : Measure Ω} [IsFiniteMeasure ν] {Y V Y' V' : Ω → ℝ}
    (hY : Measurable Y) (hV : Measurable V) (hY' : Measurable Y') (hV' : Measurable V') {K : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ K) (hVb : ∀ ω, |V ω| ≤ K) (hY'b : ∀ ω, |Y' ω| ≤ K)
    (hV'b : ∀ ω, |V' ω| ≤ K)
    (h : ∀ a : ℝ, ∫ ω, Real.exp (a * Y ω + a ^ 2 * V ω / 2) ∂μ =
      ∫ ω, Real.exp (a * Y' ω + a ^ 2 * V' ω / 2) ∂ν) (z : ℂ) :
    ∫ ω, Complex.exp (z * Y ω + z ^ 2 * V ω / 2) ∂μ =
      ∫ ω, Complex.exp (z * Y' ω + z ^ 2 * V' ω / 2) ∂ν := by
  have hf := (differentiable_integral_cexp_quad (μ := μ) hY hV hYb hVb).differentiableOn.analyticOnNhd
    isOpen_univ
  have hg := (differentiable_integral_cexp_quad (μ := ν) hY' hV' hY'b hV'b).differentiableOn.analyticOnNhd
    isOpen_univ
  have ht : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_ofReal.tendsto (0 : ℝ))
      rw [Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact Complex.ofReal_ne_zero.2 ha
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), (∫ ω, Complex.exp (w * Y ω + w ^ 2 * V ω / 2) ∂μ) =
      ∫ ω, Complex.exp (w * Y' ω + w ^ 2 * V' ω / 2) ∂ν :=
    ht.frequently (Frequently.of_forall fun a => by
      rw [integral_cexp_quad_ofReal, integral_cexp_quad_ofReal, h a])
  exact congrFun (hf.eq_of_frequently_eq hg hfreq) z

end Continuation

/-! ### The characteristic-function martingale -/

section CharFun

variable [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ} {K c : ℝ}

/-- **Characteristic-function martingale.** Under the hypotheses of `martingale_exp_of_bracket`, for `s ≤ t`,
`S ∈ 𝓕_s` and real `θ`: `∫_S exp(iθ M_t + θ² A_t/2) = ∫_S exp(iθ M_s + θ² A_s/2)`. -/
theorem setIntegral_cexp_eq_of_bracket (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t => M t ω)
    (hA0 : ∀ ω, A 0 ω = 0) (hAmono : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A p ω ≤ A q ω)
    (hAlip : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A q ω - A p ω ≤ c * ((q : ℝ) - p))
    {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω} (hS : MeasurableSet[𝓕 s] S) (θ : ℝ) :
    ∫ ω in S, Complex.exp (Complex.I * θ * M t ω + θ ^ 2 * A t ω / 2) ∂P =
      ∫ ω in S, Complex.exp (Complex.I * θ * M s ω + θ ^ 2 * A s ω / 2) ∂P := by
  have hMm : ∀ r, Measurable (M r) := fun r => ((hM.stronglyAdapted r).mono (𝓕.le r)).measurable
  have hAm : ∀ r, Measurable (A r) := fun r => by
    have h1 := ((hM2.stronglyAdapted r).mono (𝓕.le r)).measurable
    have h2 := (hMm r).pow_const 2
    have : A r = fun ω => M r ω ^ 2 - (M r ω ^ 2 - A r ω) := by funext ω; ring
    rw [this]; exact h2.sub h1
  -- a uniform bound on `[0, t]`
  set K' : ℝ := max K (|c| * t) with hK'
  have hAb : ∀ r ≤ t, ∀ ω, |A r ω| ≤ K' := fun r hr ω => by
    have h0 : 0 ≤ A r ω := hA0 ω ▸ hAmono (zero_le (a := r)) ω
    have h1 : A r ω ≤ A t ω := hAmono hr ω
    have h2 := hAlip (zero_le (a := t)) ω
    rw [hA0 ω, sub_zero, NNReal.coe_zero, sub_zero] at h2
    rw [abs_of_nonneg h0]
    calc A r ω ≤ c * t := h1.trans h2
      _ ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) t.coe_nonneg
      _ ≤ K' := le_max_right _ _
  have hMb : ∀ r ω, |M r ω| ≤ K' := fun r ω => (hK r ω).trans (le_max_left _ _)
  have hnegA : ∀ r ≤ t, ∀ ω, |-A r ω| ≤ K' := fun r hr ω => by rw [abs_neg]; exact hAb r hr ω
  have hreal : ∀ a : ℝ, ∫ ω in S, Real.exp (a * M t ω + a ^ 2 * (-A t ω) / 2) ∂P =
      ∫ ω in S, Real.exp (a * M s ω + a ^ 2 * (-A s ω) / 2) ∂P := fun a => by
    have h := (martingale_exp_of_bracket hM hM2 hK hcont hA0 hAmono hAlip a).setIntegral_eq hst hS
    have e : ∀ r ω, a * M r ω + a ^ 2 * (-A r ω) / 2 = a * M r ω - a ^ 2 * A r ω / 2 :=
      fun r ω => by ring
    simp only [e]
    exact h.symm
  have hc := integral_cexp_eq_of_forall_real (μ := P.restrict S) (ν := P.restrict S) (hMm t)
    (hAm t).neg (hMm s) (hAm s).neg (hMb t) (hnegA t le_rfl) (hMb s) (hnegA s hst) hreal
    ((θ : ℂ) * Complex.I)
  have e : ∀ r ω, ((θ : ℂ) * Complex.I) * (M r ω : ℂ) + ((θ : ℂ) * Complex.I) ^ 2 *
      ((-A r ω : ℝ) : ℂ) / 2 = Complex.I * θ * M r ω + θ ^ 2 * A r ω / 2 := fun r ω => by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [Pi.neg_apply, e] at hc
  exact hc

end CharFun

/-! ### Identification of a Gaussian law from conditional characteristic functions -/

/-- **Abstract core of Lemma 3.11.** Let `Z` be a random variable whose conditional characteristic function given a
sub-σ-algebra `𝒢` is that of `N(m, v)` for random `m, v`, and suppose
`E[exp(iθ m − θ² v/2)] = exp(iθ m₀ − θ² v₀/2)` for every `θ`. Then `Z` has the law `N(m₀, v₀)`. -/
theorem map_eq_gaussianReal_of_condExp [IsProbabilityMeasure P] {𝒢 : MeasurableSpace Ω}
    (h𝒢 : 𝒢 ≤ mΩ) {Z m v : Ω → ℝ} (hZ : Measurable[mΩ] Z) {m₀ : ℝ} {v₀ : ℝ≥0}
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Z ω) | 𝒢] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * θ * m ω - θ ^ 2 * v ω / 2))
    (hmean : ∀ θ : ℝ, ∫ ω, Complex.exp (Complex.I * θ * m ω - θ ^ 2 * v ω / 2) ∂P =
      Complex.exp (Complex.I * θ * m₀ - θ ^ 2 * v₀ / 2)) :
    @Measure.map Ω ℝ mΩ _ Z P = gaussianReal m₀ v₀ := by
  refine Measure.ext_of_charFun (funext fun θ => ?_)
  rw [charFun_apply_real, charFun_gaussianReal, integral_map hZ.aemeasurable
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (θ * x * Complex.I)).aestronglyMeasurable]
  have e1 : ∀ ω, Complex.exp (θ * Z ω * Complex.I) = Complex.exp (Complex.I * θ * Z ω) :=
    fun ω => by ring_nf
  simp only [e1]
  rw [← integral_condExp h𝒢, integral_congr_ae (hcond θ), hmean θ]
  ring_nf

end Coupling

end InteractingSLE
