/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtDCov
import InteractingSLE.Spec.Sec7.LocalExtA3Gauss

/-!
# The conditional Cameron–Martin tilt of a two-step local-set model

Packet PROVE-LOCEXT-D, item 2 (step 5's locality, the Gaussian computation). Source: Aux. lemma 55, proof
(`source/spec/p241-288.md` L196–L206, p. 250); PROVE-LOCEXT-C's route (handoff, item 1(b)): conditionally on the
local-set σ-algebra the zero-boundary part `h₂` is tilted by `exp(−(h₂, v))`.

Setting: a random relatively closed set `A ⊆ ℍ` (`ℍ ∖ A` open for every `ω`), a σ-algebra `𝒢` for which the
covariances `Cov_{ℍ∖A}(φ, ψ)` are measurable, and `h₂` conditionally a zero-boundary GFF on `ℍ ∖ A` given `𝒢`
(`IsCondZeroBoundaryGFF`). Let `s_k` be energy-Cauchy test functions (`IsCovCauchy`).

* `condExp_cexp_add_eq`: the conditional joint characteristic function of `(h₂(φ), h₂(ψ))`;
* `ae_tendsto_srcLim`: `h₂(s_k) → Y = srcLim` almost surely (`E[(h₂(s_n) − h₂(s_m))²] ≤ 4 · 16^{−N}`);
* `condExp_cexp_srcLim_eq`: `(h₂(φ), Y)` is conditionally centred Gaussian with covariances
  `(Cov(φ, φ), Γ(φ), σ²)`, `Γ(φ) = lim_k Cov(φ, s_k)` (`covLim`), `σ² = lim_k Cov(s_k, s_k)` (`srcVar`);
* **`condExp_exp_neg_srcLim_mul_cexp`**: the complex tilt
  `E[e^{−Y} e^{i h₂(φ)} | 𝒢] = e^{σ²/2} · exp(−i Γ(φ) − Cov(φ, φ)/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets

theorem cfVal_zero_left (q : ℝ) : cfVal 0 q = ((Real.exp (-(1 / 2) * q) : ℝ) : ℂ) := by
  rw [cfVal, Complex.ofReal_zero, mul_zero, zero_sub, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-! ### The variance of the source along a domain -/

section SrcVar

variable {U : Set ℂ} {s : ℕ → TestOn upperHalfPlaneOpens}

theorem cauchySeq_zeroGFFTestCov_self (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) :
    CauchySeq fun k => zeroGFFTestCov U (s k) (s k) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have ht : Tendsto (fun N : ℕ => 2 * covBound s * (1 / 4 : ℝ) ^ N) atTop (𝓝 (2 * covBound s * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  rw [mul_zero] at ht
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun n hn => ?_⟩
  have e : zeroGFFTestCov U (s n) (s n) - zeroGFFTestCov U (s N) (s N) =
      zeroGFFTestCov U ⇑(s n - s N) (s n) + zeroGFFTestCov U (s N) ⇑(s n - s N) := by
    rw [zeroGFFTestCov_comm hU hUH (s n - s N) (s n), zeroGFFTestCov_sub_right hU hUH, zeroGFFTestCov_sub_right hU hUH,
      zeroGFFTestCov_comm hU hUH (s n) (s N)]
    ring
  rw [Real.dist_eq, e]
  refine lt_of_le_of_lt ((abs_add_le _ _).trans ?_) hN
  have hΔ := sqrt_zeroGFFTestCov_sub_le hU hUH hs hn le_rfl
  have hb : ∀ k, Real.sqrt (zeroGFFTestCov U (s k) (s k)) ≤ covBound s := sqrt_zeroGFFTestCov_le_covBound hU hUH hs
  have h1 := (abs_zeroGFFTestCov_le hU hUH (s n - s N) (s n)).trans
    (mul_le_mul hΔ (hb n) (Real.sqrt_nonneg _) (by positivity))
  have h2 := (abs_zeroGFFTestCov_le hU hUH (s N) (s n - s N)).trans
    (mul_le_mul (hb N) hΔ (Real.sqrt_nonneg _) covBound_pos.le)
  linarith

variable (U s) in
/-- `σ²_U = lim_k Cov_U(s_k, s_k)`: the conditional variance of the source pairing. -/
def srcVar : ℝ := limUnder atTop fun k => zeroGFFTestCov U (s k) (s k)

theorem tendsto_srcVar (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) :
    Tendsto (fun k => zeroGFFTestCov U (s k) (s k)) atTop (𝓝 (srcVar U s)) :=
  (cauchySeq_zeroGFFTestCov_self hU hUH hs).tendsto_limUnder

theorem srcVar_nonneg (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) : 0 ≤ srcVar U s :=
  ge_of_tendsto' (tendsto_srcVar hU hUH hs) fun _ => zeroGFFTestCov_self_nonneg hU hUH _

theorem srcVar_le (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) : srcVar U s ≤ covBound s ^ 2 := by
  refine le_of_tendsto' (tendsto_srcVar hU hUH hs) fun k => ?_
  rw [← Real.sq_sqrt (zeroGFFTestCov_self_nonneg hU hUH (s k))]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_zeroGFFTestCov_le_covBound hU hUH hs k) 2

end SrcVar

/-! ### Conditional characteristic functions of the zero-boundary part -/

section Model

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {A : Ω → Set ℂ} {h₂ : Ω → DistOn upperHalfPlaneOpens} {s : ℕ → TestOn upperHalfPlaneOpens}

/-- The conditional joint characteristic function of `(h₂(φ), h₂(ψ))`. -/
theorem condExp_cexp_add_eq (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (φ ψ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((a * h₂ ω φ + b * h₂ ω ψ : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cfVal 0 (a ^ 2 * zeroGFFTestCov (H \ A ω) φ φ + 2 * a * b * zeroGFFTestCov (H \ A ω) φ ψ +
        b ^ 2 * zeroGFFTestCov (H \ A ω) ψ ψ) := by
  have e : (fun ω => Complex.exp (Complex.I * ((a * h₂ ω φ + b * h₂ ω ψ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * (h₂ ω (a • φ + b • ψ) : ℂ)) := by
    funext ω
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [e]
  filter_upwards [hcond (a • φ + b • ψ)] with ω hω
  rw [hω, cfVal_zero_left]
  have hU := hA ω
  have hUH : H \ A ω ⊆ H := sdiff_subset
  congr 3
  simp only [zeroGFFTestCov_add_left hU hUH, zeroGFFTestCov_add_right hU hUH, zeroGFFTestCov_smul_left hU hUH,
    zeroGFFTestCov_smul_right hU hUH]
  rw [zeroGFFTestCov_comm hU hUH ψ φ]
  ring

/-- The conditional characteristic function of `t h₂(φ)`. -/
theorem condExp_cexp_mul_eq (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (φ : TestOn upperHalfPlaneOpens) (t : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((t * h₂ ω φ : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
  have h := condExp_cexp_add_eq hA hcond φ φ t 0
  simp only [zero_mul, add_zero, mul_zero, zero_pow two_ne_zero, cfVal_zero_left] at h
  exact h

theorem measurable_distOn_apply' {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (φ : TestOn upperHalfPlaneOpens) : Measurable fun ω => h ω φ :=
  (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hh)

/-- **The source pairings of the zero-boundary part converge almost surely.** -/
theorem ae_exists_tendsto_srcPairing [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (hh₂ : Measurable h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hs : IsCovCauchy s) : ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => h₂ ω (s k)) atTop (𝓝 l) := by
  set f : ℕ → Ω → ℝ := fun k ω => h₂ ω (s k) with hf
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_distOn_apply' hh₂ (s k)
  set B : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (3 * (1 / 4 : ℝ) ^ N) with hB
  have hBs : ∑' i, B i ≠ ∞ := by
    rw [hB, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3)]
    exact ENNReal.ofReal_ne_top
  refine Lp.ae_tendsto_of_cauchy_eLpNorm' (p := 2) (fun n => (hfm n).aestronglyMeasurable) one_le_two hBs ?_
  intro N n m hn hm
  set ψ : TestOn upperHalfPlaneOpens := s n - s m with hψ
  have hΔ : f n - f m = fun ω => h₂ ω ψ := by
    funext ω; simp only [hf, Pi.sub_apply, hψ, map_sub]
  rw [hΔ]
  have hV : ∀ ω, zeroGFFTestCov (H \ A ω) ψ ψ ≤ (1 / 16 : ℝ) ^ N := fun ω =>
    (zeroGFFTestCov_self_le_H (hA ω) sdiff_subset ψ).trans (hs N n m hn hm)
  have h2 := lintegral_sq_le_of_condCharFun h𝒢 (measurable_distOn_apply' hh₂ ψ) ((hcovm ψ ψ).mono h𝒢 le_rfl)
    (ae_of_all _ fun ω => zeroGFFTestCov_self_nonneg (hA ω) sdiff_subset ψ)
    (condExp_cexp_mul_eq hA hcond ψ) (by positivity : (0 : ℝ) < (1 / 16) ^ N) (ae_of_all _ hV)
  have e : ∀ ω, ‖h₂ ω ψ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (h₂ ω ψ ^ 2) := fun ω => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [eLpNorm', lintegral_congr fun ω => e ω]
  calc (∫⁻ ω, ENNReal.ofReal (h₂ ω ψ ^ 2) ∂P) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (4 * (1 / 16 : ℝ) ^ N) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_mul (by norm_num), sqrt_one_div_sixteen_pow,
          show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    _ < B N := by
        rw [hB]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
          have : (0 : ℝ) < (1 / 4) ^ N := by positivity
          linarith)

variable (s) in
/-- The almost sure limit `Y = lim_k h₂(s_k)` (`limUnder`). -/
def srcLim (h₂ : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : ℝ := limUnder atTop fun k => h₂ ω (s k)

theorem measurable_srcLim (hh₂ : Measurable h₂) : Measurable (srcLim s h₂) :=
  (StronglyMeasurable.limUnder fun k => (measurable_distOn_apply' hh₂ (s k)).stronglyMeasurable).measurable

theorem ae_tendsto_srcLim [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (hh₂ : Measurable h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hs : IsCovCauchy s) : ∀ᵐ ω ∂P, Tendsto (fun k => h₂ ω (s k)) atTop (𝓝 (srcLim s h₂ ω)) := by
  filter_upwards [ae_exists_tendsto_srcPairing h𝒢 hA hcond hh₂ hcovm hs] with ω ⟨l, hl⟩
  rw [srcLim, hl.limUnder_eq]
  exact hl

/-- **`(h₂(φ), Y)` is conditionally centred Gaussian** with covariances `(Cov(φ, φ), Γ(φ), σ²)`. -/
theorem condExp_cexp_srcLim_eq [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (hh₂ : Measurable h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hs : IsCovCauchy s) (φ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((a * h₂ ω φ + b * srcLim s h₂ ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cfVal 0 (a ^ 2 * zeroGFFTestCov (H \ A ω) φ φ + 2 * a * b * covLim (H \ A ω) s φ +
        b ^ 2 * srcVar (H \ A ω) s) := by
  refine ae_condExp_cexp_of_tendsto h𝒢 (Y := fun k ω => a * h₂ ω φ + b * h₂ ω (s k)) (a := fun _ _ => 0)
    (q := fun k ω => a ^ 2 * zeroGFFTestCov (H \ A ω) φ φ + 2 * a * b * zeroGFFTestCov (H \ A ω) φ (s k) +
      b ^ 2 * zeroGFFTestCov (H \ A ω) (s k) (s k))
    (fun k => ((measurable_distOn_apply' hh₂ φ).const_mul a |>.add
      ((measurable_distOn_apply' hh₂ (s k)).const_mul b)).aemeasurable)
    (fun k => condExp_cexp_add_eq hA hcond φ (s k) a b) ?_ (ae_of_all _ fun _ => tendsto_const_nhds)
    (ae_of_all _ fun ω => ?_)
  · filter_upwards [ae_tendsto_srcLim h𝒢 hA hcond hh₂ hcovm hs] with ω hω
    exact tendsto_const_nhds.add (hω.const_mul b)
  · exact (tendsto_const_nhds.add ((tendsto_covLim (hA ω) sdiff_subset hs φ).const_mul _)).add
      ((tendsto_srcVar (hA ω) sdiff_subset hs).const_mul _)

theorem measurable_srcVar
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ) :
    Measurable[𝒢] fun ω => srcVar (H \ A ω) s :=
  (@StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k => (hcovm (s k) (s k)).stronglyMeasurable).measurable

theorem measurable_covLim
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable[𝒢] fun ω => covLim (H \ A ω) s φ :=
  (@StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k => (hcovm φ (s k)).stronglyMeasurable).measurable

/-- `E[e^{−Y}] < ∞`: the conditional moment generating function of `Y`. -/
theorem integrable_exp_neg_srcLim [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (hh₂ : Measurable h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hs : IsCovCauchy s) : Integrable (fun ω => Real.exp (-srcLim s h₂ ω)) P := by
  have hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * srcLim s h₂ ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * srcVar (H \ A ω) s)) : ℝ) : ℂ) := fun t => by
    have h := condExp_cexp_srcLim_eq h𝒢 hA hcond hh₂ hcovm hs 0 0 t
    simp only [zero_mul, zero_add, zero_pow two_ne_zero, mul_zero, cfVal_zero_left] at h
    exact h
  have hW : Measurable[𝒢] fun _ : Ω => (1 : ℝ≥0∞) := @measurable_const ℝ≥0∞ Ω _ 𝒢 1
  have hm := lintegral_mul_exp_of_condCharFun (P := P) h𝒢 (measurable_srcLim hh₂)
    ((measurable_srcVar hcovm).mono h𝒢 le_rfl)
    (ae_of_all _ fun ω => srcVar_nonneg (hA ω) sdiff_subset hs) hc hW (-1)
  simp only [one_mul, neg_one_mul, neg_one_sq] at hm
  refine (lintegral_ofReal_ne_top_iff_integrable (measurable_srcLim hh₂).neg.exp.aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.exp_pos _).le)).1 ?_
  show ∫⁻ ω, ENNReal.ofReal (Real.exp (-srcLim s h₂ ω)) ∂P ≠ ∞
  rw [hm]
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := Real.exp (covBound s ^ 2 / 2))) ?_
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (srcVar (H \ A ω) s / 2)) ∂P
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (covBound s ^ 2 / 2)) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
          have := srcVar_le (hA ω) sdiff_subset hs
          linarith))
    _ = ENNReal.ofReal (Real.exp (covBound s ^ 2 / 2)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The conditional complex tilt** (the conditional Cameron–Martin shift of Aux. 55):
`E[e^{−Y} e^{i h₂(φ)} | 𝒢] = e^{σ²/2} · exp(−i Γ(φ) − Cov(φ, φ)/2)`. -/
theorem condExp_exp_neg_srcLim_mul_cexp [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) (hh₂ : Measurable h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hs : IsCovCauchy s) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => ((Real.exp (-srcLim s h₂ ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (h₂ ω φ : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (srcVar (H \ A ω) s / 2) : ℝ) : ℂ) *
        cfVal (-covLim (H \ A ω) s φ) (zeroGFFTestCov (H \ A ω) φ φ) := by
  have h := ae_condExp_tilt_of_joint (P := P) h𝒢 (measurable_distOn_apply' hh₂ φ) (measurable_srcLim hh₂)
    (integrable_exp_neg_srcLim h𝒢 hA hcond hh₂ hcovm hs) (D := univ) (μ₁ := fun _ => 0) (μ₂ := fun _ => 0)
    (s₁₁ := fun ω => zeroGFFTestCov (H \ A ω) φ φ) (s₁₂ := fun ω => covLim (H \ A ω) s φ)
    (s₂₂ := fun ω => srcVar (H \ A ω) s) fun a b => by
      filter_upwards [condExp_cexp_srcLim_eq h𝒢 hA hcond hh₂ hcovm hs φ a b] with ω hω _
      rw [hω, mul_zero, mul_zero, add_zero]
  filter_upwards [h] with ω hω
  rw [hω (mem_univ ω), neg_zero, zero_add, zero_sub]

end Model

end LocalExt

end InteractingSLE
