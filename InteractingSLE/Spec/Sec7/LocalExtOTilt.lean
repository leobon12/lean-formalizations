/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOCov

/-!
# The conditional Cameron–Martin tilt with a random source

Packet PROVE-LOCEXT-O, step (3). PROVE-LOCEXT-D's tilt (`LocalExtDTilt`, `IsLocalSet.withDensity_exp_neg`) uses a
deterministic source `s_k` and a deterministic shift `c`. At a restart the source is the source of the restart word,
which is a random variable measurable for the conditioning σ-algebra `𝒢` (it is read from the recorded history). This
file redoes the conditional computation with a `𝒢`-measurable random source `s ω k` (energy-Cauchy for every `ω`, with an
almost sure bound on its energy) and a `𝒢`-measurable random shift `c ω`:

* `condExp_cexp_add_eq_rand`, `ae_tendsto_srcLimR`, `condExp_cexp_srcLimR_eq`: given `𝒢`, `(h₂(φ), Y = lim_k h₂(s_k))`
  is centred Gaussian with the covariances `(Cov(φ, φ), Γ(φ), σ²)` of `ℍ ∖ A` at the random source;
* `condExp_exp_neg_srcLimR_mul_cexp`: the complex tilt `E[e^{−Y} e^{i h₂(φ)} | 𝒢] = e^{σ²/2} exp(−iΓ(φ) − Cov(φ, φ)/2)`;
* **`exists_condLocal_withDensity_tilt_rand`**: under `Q = e^{−Λ + b} · P` (`h(s_k) → Λ`, `b` `𝒢`-measurable), the field
  `h₁ + h₂ + c` decomposes again as a `𝒢`-measurable part harmonic off `A` (`h₁ + c − Γ`) plus a conditional zero-boundary
  GFF on `ℍ ∖ A` given `𝒢` (`h₂ + Γ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets

section Model

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h₂ : Ω → DistOn upperHalfPlaneOpens} {s : Ω → ℕ → TestOn upperHalfPlaneOpens}

theorem coe_add_smul_testOn (a b : ℝ) (φ ψ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    (a • φ + b • ψ) z = a * φ z + b * ψ z := rfl

/-- The conditional joint characteristic function of `(h₂(φ), h₂(ψ))` at random test functions. -/
theorem condExp_cexp_add_eq_rand (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω)) (hh₂ : Measurable h₂)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) {φ ψ : Ω → TestOn upperHalfPlaneOpens}
    (hφ : ∀ z, Measurable[𝒢] fun ω => φ ω z) (hψ : ∀ z, Measurable[𝒢] fun ω => ψ ω z) (a b : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((a * h₂ ω (φ ω) + b * h₂ ω (ψ ω) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cfVal 0 (a ^ 2 * zeroGFFTestCov (H \ A ω) (φ ω) (φ ω) +
        2 * a * b * zeroGFFTestCov (H \ A ω) (φ ω) (ψ ω) + b ^ 2 * zeroGFFTestCov (H \ A ω) (ψ ω) (ψ ω)) := by
  have e : (fun ω => Complex.exp (Complex.I * ((a * h₂ ω (φ ω) + b * h₂ ω (ψ ω) : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * (h₂ ω (a • φ ω + b • ψ ω) : ℂ)) := by
    funext ω
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [e]
  have hχ : ∀ z, Measurable[𝒢] fun ω => (a • φ ω + b • ψ ω) z := fun z => by
    simp only [coe_add_smul_testOn]
    exact ((hφ z).const_mul a).add ((hψ z).const_mul b)
  filter_upwards [IsCondZeroBoundaryGFF.condExp_cexp_random h𝒢 hA hh₂ hcond hχ] with ω hω
  rw [hω, cfVal_zero_left]
  have hU := hA ω
  have hUH : H \ A ω ⊆ H := sdiff_subset
  congr 3
  simp only [zeroGFFTestCov_add_left hU hUH, zeroGFFTestCov_add_right hU hUH, zeroGFFTestCov_smul_left hU hUH,
    zeroGFFTestCov_smul_right hU hUH]
  rw [zeroGFFTestCov_comm hU hUH (ψ ω) (φ ω)]
  ring

/-- The conditional characteristic function of `t h₂(ψ)` at a random test function. -/
theorem condExp_cexp_mul_eq_rand (h𝒢 : 𝒢 ≤ mΩ) (hA : ∀ ω, IsOpen (H \ A ω)) (hh₂ : Measurable h₂)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂) {ψ : Ω → TestOn upperHalfPlaneOpens}
    (hψ : ∀ z, Measurable[𝒢] fun ω => ψ ω z) (t : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((t * h₂ ω (ψ ω) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * zeroGFFTestCov (H \ A ω) (ψ ω) (ψ ω))) : ℝ) : ℂ) := by
  have h := condExp_cexp_add_eq_rand h𝒢 hA hh₂ hcond hψ hψ t 0
  simp only [zero_mul, add_zero, mul_zero, zero_pow two_ne_zero, cfVal_zero_left] at h
  exact h

/-- Pointwise measurability of a random test function for the ambient σ-algebra. -/
theorem measurable_apply_rand (h𝒢 : 𝒢 ≤ mΩ) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {ψ : Ω → TestOn upperHalfPlaneOpens} (hψ : ∀ z, Measurable[𝒢] fun ω => ψ ω z) :
    Measurable fun ω => h ω (ψ ω) :=
  RandomTest.measurable_apply_of_forall_measurable hh fun z => (hψ z).mono h𝒢 le_rfl

/-- **The source pairings of the zero-boundary part converge almost surely** (random source). -/
theorem ae_exists_tendsto_srcPairing_rand (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω)) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => h₂ ω (s ω k)) atTop (𝓝 l) := by
  have hA : ∀ ω, IsOpen (H \ A ω) := fun ω => (hAc ω).2
  set f : ℕ → Ω → ℝ := fun k ω => h₂ ω (s ω k) with hf
  have hfm : ∀ k, Measurable (f k) := fun k => measurable_apply_rand h𝒢 hh₂ (hsm k)
  set B : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (3 * (1 / 4 : ℝ) ^ N) with hB
  have hBs : ∑' i, B i ≠ ∞ := by
    rw [hB, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3)]
    exact ENNReal.ofReal_ne_top
  refine Lp.ae_tendsto_of_cauchy_eLpNorm' (p := 2) (fun n => (hfm n).aestronglyMeasurable) one_le_two hBs ?_
  intro N n m hn hm
  set ψ : Ω → TestOn upperHalfPlaneOpens := fun ω => s ω n - s ω m with hψ
  have hψm : ∀ z, Measurable[𝒢] fun ω => ψ ω z := fun z => by
    simp only [hψ]
    exact (hsm n z).sub (hsm m z)
  have hΔ : f n - f m = fun ω => h₂ ω (ψ ω) := by
    funext ω; simp only [hf, Pi.sub_apply, hψ, map_sub]
  rw [hΔ]
  have hV : ∀ ω, zeroGFFTestCov (H \ A ω) (ψ ω) (ψ ω) ≤ (1 / 16 : ℝ) ^ N := fun ω =>
    (zeroGFFTestCov_self_le_H (hA ω) sdiff_subset (ψ ω)).trans (hs ω N n m hn hm)
  have hVm : Measurable fun ω => zeroGFFTestCov (H \ A ω) (ψ ω) (ψ ω) :=
    (measurable_zeroGFFTestCov_compl_random hA𝒢 hAc hψm hψm).mono h𝒢 le_rfl
  have h2 := lintegral_sq_le_of_condCharFun h𝒢 (measurable_apply_rand h𝒢 hh₂ hψm) hVm
    (ae_of_all _ fun ω => zeroGFFTestCov_self_nonneg (hA ω) sdiff_subset (ψ ω))
    (condExp_cexp_mul_eq_rand h𝒢 hA hh₂ hcond hψm) (by positivity : (0 : ℝ) < (1 / 16) ^ N) (ae_of_all _ hV)
  have e : ∀ ω, ‖h₂ ω (ψ ω)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (h₂ ω (ψ ω) ^ 2) := fun ω => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [eLpNorm', lintegral_congr fun ω => e ω]
  calc (∫⁻ ω, ENNReal.ofReal (h₂ ω (ψ ω) ^ 2) ∂P) ^ (1 / (2 : ℝ))
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
/-- The almost sure limit `Y = lim_k h₂(s_k)` of the random source pairings (`limUnder`). -/
def srcLimR (h₂ : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : ℝ := limUnder atTop fun k => h₂ ω (s ω k)

theorem measurable_srcLimR (h𝒢 : 𝒢 ≤ mΩ) (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) :
    Measurable (srcLimR s h₂) :=
  (StronglyMeasurable.limUnder fun k => (measurable_apply_rand h𝒢 hh₂ (hsm k)).stronglyMeasurable).measurable

theorem ae_tendsto_srcLimR (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h₂ ω (s ω k)) atTop (𝓝 (srcLimR s h₂ ω)) := by
  filter_upwards [ae_exists_tendsto_srcPairing_rand h𝒢 hA𝒢 hAc hcond hh₂ hsm hs] with ω ⟨l, hl⟩
  rw [srcLimR, hl.limUnder_eq]
  exact hl

omit mΩ in
theorem measurable_srcVar_rand {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) :
    Measurable[𝒢] fun ω => srcVar (H \ A ω) (s ω) :=
  (@StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k =>
    (measurable_zeroGFFTestCov_compl_random hA𝒢 hAc (hsm k) (hsm k)).stronglyMeasurable).measurable

omit mΩ in
theorem measurable_covLim_rand {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z)
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable[𝒢] fun ω => covLim (H \ A ω) (s ω) φ :=
  (@StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k =>
    (measurable_zeroGFFTestCov_compl_random hA𝒢 hAc (ψ₁ := fun _ => φ) (fun _ => measurable_const)
      (hsm k)).stronglyMeasurable).measurable

/-- **`(h₂(φ), Y)` is conditionally centred Gaussian** with covariances `(Cov(φ, φ), Γ(φ), σ²)` (random source). -/
theorem condExp_cexp_srcLimR_eq (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω))
    (φ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((a * h₂ ω φ + b * srcLimR s h₂ ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cfVal 0 (a ^ 2 * zeroGFFTestCov (H \ A ω) φ φ + 2 * a * b * covLim (H \ A ω) (s ω) φ +
        b ^ 2 * srcVar (H \ A ω) (s ω)) := by
  have hA : ∀ ω, IsOpen (H \ A ω) := fun ω => (hAc ω).2
  refine ae_condExp_cexp_of_tendsto h𝒢 (Y := fun k ω => a * h₂ ω φ + b * h₂ ω (s ω k)) (a := fun _ _ => 0)
    (q := fun k ω => a ^ 2 * zeroGFFTestCov (H \ A ω) φ φ + 2 * a * b * zeroGFFTestCov (H \ A ω) φ (s ω k) +
      b ^ 2 * zeroGFFTestCov (H \ A ω) (s ω k) (s ω k))
    (fun k => ((measurable_distOn_apply' hh₂ φ).const_mul a |>.add
      ((measurable_apply_rand h𝒢 hh₂ (hsm k)).const_mul b)).aemeasurable)
    (fun k => condExp_cexp_add_eq_rand h𝒢 hA hh₂ hcond (φ := fun _ => φ) (fun z => measurable_const) (hsm k) a b)
    ?_ (ae_of_all _ fun _ => tendsto_const_nhds) (ae_of_all _ fun ω => ?_)
  · filter_upwards [ae_tendsto_srcLimR h𝒢 hA𝒢 hAc hcond hh₂ hsm hs] with ω hω
    exact tendsto_const_nhds.add (hω.const_mul b)
  · exact (tendsto_const_nhds.add ((tendsto_covLim (hA ω) sdiff_subset (hs ω) φ).const_mul _)).add
      ((tendsto_srcVar (hA ω) sdiff_subset (hs ω)).const_mul _)

/-- `E[e^{−Y}] < ∞` under an almost sure bound on the source energies. -/
theorem integrable_exp_neg_srcLimR (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω))
    {C : ℝ} (hbd : ∀ᵐ ω ∂P, covBound (s ω) ≤ C) :
    Integrable (fun ω => Real.exp (-srcLimR s h₂ ω)) P := by
  have hA : ∀ ω, IsOpen (H \ A ω) := fun ω => (hAc ω).2
  have hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * srcLimR s h₂ ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * srcVar (H \ A ω) (s ω))) : ℝ) : ℂ) := fun t => by
    have h := condExp_cexp_srcLimR_eq h𝒢 hA𝒢 hAc hcond hh₂ hsm hs 0 0 t
    simp only [zero_mul, zero_add, zero_pow two_ne_zero, mul_zero, cfVal_zero_left] at h
    exact h
  have hW : Measurable[𝒢] fun _ : Ω => (1 : ℝ≥0∞) := @measurable_const ℝ≥0∞ Ω _ 𝒢 1
  have hm := lintegral_mul_exp_of_condCharFun (P := P) h𝒢 (measurable_srcLimR h𝒢 hh₂ hsm)
    ((measurable_srcVar_rand hA𝒢 hAc hsm).mono h𝒢 le_rfl)
    (ae_of_all _ fun ω => srcVar_nonneg (hA ω) sdiff_subset (hs ω)) hc hW (-1)
  simp only [one_mul, neg_one_mul, neg_one_sq] at hm
  refine (lintegral_ofReal_ne_top_iff_integrable (measurable_srcLimR h𝒢 hh₂ hsm).neg.exp.aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.exp_pos _).le)).1 ?_
  show ∫⁻ ω, ENNReal.ofReal (Real.exp (-srcLimR s h₂ ω)) ∂P ≠ ∞
  rw [hm]
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := Real.exp (C ^ 2 / 2))) ?_
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (srcVar (H \ A ω) (s ω) / 2)) ∂P
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (C ^ 2 / 2)) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbd] with ω hω
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 := srcVar_le (hA ω) sdiff_subset (hs ω)
        have h0 : 0 ≤ covBound (s ω) := (covBound_pos (s := s ω)).le
        have h2 : covBound (s ω) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ h0 hω 2
        linarith
    _ = ENNReal.ofReal (Real.exp (C ^ 2 / 2)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The conditional complex tilt** with a random source:
`E[e^{−Y} e^{i h₂(φ)} | 𝒢] = e^{σ²/2} · exp(−i Γ(φ) − Cov(φ, φ)/2)`. -/
theorem condExp_exp_neg_srcLimR_mul_cexp (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ} (hA𝒢 : Measurable[𝒢, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hh₂ : Measurable h₂) (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω))
    {C : ℝ} (hbd : ∀ᵐ ω ∂P, covBound (s ω) ≤ C) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => ((Real.exp (-srcLimR s h₂ ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (h₂ ω φ : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (srcVar (H \ A ω) (s ω) / 2) : ℝ) : ℂ) *
        cfVal (-covLim (H \ A ω) (s ω) φ) (zeroGFFTestCov (H \ A ω) φ φ) := by
  have h := ae_condExp_tilt_of_joint (P := P) h𝒢 (measurable_distOn_apply' hh₂ φ)
    (measurable_srcLimR h𝒢 hh₂ hsm) (integrable_exp_neg_srcLimR h𝒢 hA𝒢 hAc hcond hh₂ hsm hs hbd) (D := univ)
    (μ₁ := fun _ => 0) (μ₂ := fun _ => 0)
    (s₁₁ := fun ω => zeroGFFTestCov (H \ A ω) φ φ) (s₁₂ := fun ω => covLim (H \ A ω) (s ω) φ)
    (s₂₂ := fun ω => srcVar (H \ A ω) (s ω)) fun a b => by
      filter_upwards [condExp_cexp_srcLimR_eq h𝒢 hA𝒢 hAc hcond hh₂ hsm hs φ a b] with ω hω _
      rw [hω, mul_zero, mul_zero, add_zero]
  filter_upwards [h] with ω hω
  rw [hω (mem_univ ω), neg_zero, zero_add, zero_sub]

omit mΩ in
/-- A `𝒢`-measurable random distribution paired with a `𝒢`-measurable random test function is `𝒢`-measurable. -/
theorem measurable_apply_rand_of {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable[𝒢] h)
    {ψ : Ω → TestOn upperHalfPlaneOpens} (hψ : ∀ z, Measurable[𝒢] fun ω => ψ ω z) :
    Measurable[𝒢] fun ω => h ω (ψ ω) :=
  @RandomTest.measurable_apply_of_forall_measurable Ω 𝒢 _ h hh ψ hψ

/-- **The tilted conditional decomposition with a random source** (step 5's locality at a restart). Let `A` be a
`𝒢`-measurable random relatively closed subset of `ℍ`, `h₁` `𝒢`-measurable and harmonic off `A`, `h₂` conditionally a
zero-boundary GFF on `ℍ ∖ A` given `𝒢`, `s ω k` a `𝒢`-measurable energy-Cauchy random source (energies bounded almost
surely) with `(h₁ + h₂)(s_k) → Λ` almost surely, `Z = e^{−Λ + b}` a probability density with `b` `𝒢`-measurable, and
`c` a `𝒢`-measurable random distribution with the Dirichlet pairings of the source. Then under `Z · P` the field
`h₁ + h₂ + c` is a `𝒢`-measurable part harmonic off `A` plus a conditional zero-boundary GFF on `ℍ ∖ A` given `𝒢`. -/
theorem exists_condLocal_withDensity_tilt_rand (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ}
    (hA𝒢 : Measurable[𝒢, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h₁ : Ω → DistOn upperHalfPlaneOpens} (hh₁ : Measurable[𝒢] h₁)
    (hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω)) (hh₂ : Measurable h₂)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hsm : ∀ k z, Measurable[𝒢] fun ω => s ω k z) (hs : ∀ ω, IsCovCauchy (s ω)) {C : ℝ}
    (hbd : ∀ᵐ ω ∂P, covBound (s ω) ≤ C) {Λ : Ω → ℝ} (hΛ : Measurable Λ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun k => (h₁ ω + h₂ ω) (s ω k)) atTop (𝓝 (Λ ω)))
    {b : Ω → ℝ} (hb : Measurable[𝒢] b) (hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp (-Λ ω + b ω)) ∂P = 1)
    {c : Ω → DistOn upperHalfPlaneOpens} (hc : Measurable[𝒢] c)
    (hcpair : ∀ ω (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)),
      Tendsto (fun k => ∫ z, s ω k z * g.1 z) atTop (𝓝 (c ω (lapTest U g)))) :
    ∃ h₁' : Ω → DistOn upperHalfPlaneOpens, Measurable[𝒢] h₁' ∧
      (∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ ω + b ω))),
        IsHarmonicDistOn (h₁' ω) (H \ A ω)) ∧
      IsCondZeroBoundaryGFF (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ ω + b ω))) 𝒢
        (fun ω => H \ A ω) (fun ω => h₁ ω + h₂ ω + c ω - h₁' ω) := by
  have hD : ∀ ω, IsOpen (H \ A ω) := fun ω => (hAc ω).2
  set Γ : Ω → DistOn upperHalfPlaneOpens := fun ω => covLimDist (hD ω) sdiff_subset (hs ω) with hΓdef
  have hΓφ : ∀ φ ω, Γ ω φ = covLim (H \ A ω) (s ω) φ := fun φ ω => covLimDist_apply _ _ _ φ
  have hΓm : Measurable[𝒢] Γ := by
    refine (@measurable_distOn_iff upperHalfPlaneOpens Ω 𝒢 _).2 fun φ => ?_
    simp only [hΓφ]
    exact measurable_covLim_rand hA𝒢 hAc hsm φ
  have hh₁m : Measurable h₁ := hh₁.mono h𝒢 le_rfl
  set Z : Ω → ℝ := fun ω => Real.exp (-Λ ω + b ω) with hZdef
  have hZm : Measurable Z := (hΛ.neg.add (hb.mono h𝒢 le_rfl)).exp
  have hZi : Integrable Z P :=
    (lintegral_ofReal_ne_top_iff_integrable hZm.aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).1 (by
        show ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≠ ∞
        rw [hZ]; exact ENNReal.one_ne_top)
  have hQP : (P.withDensity fun ω => ENNReal.ofReal (Z ω)) ≪ P := withDensity_absolutelyContinuous _ _
  refine ⟨fun ω => h₁ ω + (c ω - Γ ω), ?_, ?_, ?_⟩
  · refine (@measurable_distOn_iff upperHalfPlaneOpens Ω 𝒢 _).2 fun φ => ?_
    simp only [add_apply, sub_apply]
    exact ((measurable_distOn_apply φ).comp hh₁).add
      (((measurable_distOn_apply φ).comp hc).sub ((measurable_distOn_apply φ).comp hΓm))
  · filter_upwards [hQP.ae_le hharm] with ω hω
    exact Coupling.IsHarmonicDistOn.add' (hD ω) hω
      (isHarmonicDistOn_sub_covLimDist (hD ω) sdiff_subset (hs ω) (hcpair ω))
  -- the residual is `h₂ + Γ`
  have e : (fun ω => h₁ ω + h₂ ω + c ω - (h₁ ω + (c ω - Γ ω))) = fun ω => h₂ ω + Γ ω := by
    funext ω; abel
  rw [e]
  -- `Λ = M₁ + Y`
  have hY := ae_tendsto_srcLimR h𝒢 hA𝒢 hAc hcond hh₂ hsm hs
  set Y : Ω → ℝ := srcLimR s h₂ with hYdef
  set M₁ : Ω → ℝ := fun ω => limUnder atTop fun k => h₁ ω (s ω k) with hM₁def
  have hM₁m : StronglyMeasurable[𝒢] M₁ :=
    @StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k =>
      (measurable_apply_rand_of hh₁ (hsm k)).stronglyMeasurable
  have hΛY : ∀ᵐ ω ∂P, Λ ω = M₁ ω + Y ω := by
    filter_upwards [hconv, hY] with ω h1 h2
    have h3 : Tendsto (fun k => h₁ ω (s ω k)) atTop (𝓝 (Λ ω - Y ω)) :=
      (h1.sub h2).congr fun k => by simp only [add_apply]; ring
    rw [show M₁ ω = Λ ω - Y ω from h3.limUnder_eq]
    ring
  -- `E[Z | 𝒢] = N`
  set N : Ω → ℝ := fun ω => Real.exp (-M₁ ω + b ω) * Real.exp (srcVar (H \ A ω) (s ω) / 2) with hNdef
  have hEm : StronglyMeasurable[𝒢] fun ω => Real.exp (-M₁ ω + b ω) :=
    ((hM₁m.measurable.neg.add hb).exp).stronglyMeasurable
  have hNm : StronglyMeasurable[𝒢] N :=
    (hEm.measurable.mul (((measurable_srcVar_rand hA𝒢 hAc hsm).div_const 2).exp)).stronglyMeasurable
  have hNpos : ∀ ω, 0 < N ω := fun ω => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hYi : Integrable (fun ω => Real.exp (-Y ω)) P :=
    integrable_exp_neg_srcLimR h𝒢 hA𝒢 hAc hcond hh₂ hsm hs hbd
  have hcY : P[fun ω => Real.exp (-Y ω) | 𝒢] =ᵐ[P] fun ω => Real.exp (srcVar (H \ A ω) (s ω) / 2) := by
    have ht0 := condExp_exp_neg_srcLimR_mul_cexp h𝒢 hA𝒢 hAc hcond hh₂ hsm hs hbd 0
    have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := 𝒢) hYi
    filter_upwards [ht0, hcomm] with ω e1 e2
    have e3 : (fun ω => ((Real.exp (-srcLimR s h₂ ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (h₂ ω 0 : ℂ))) =
        Complex.ofRealCLM ∘ fun ω => Real.exp (-Y ω) := by
      funext ω
      simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Function.comp_apply,
        Complex.ofRealCLM_apply, hYdef]
    rw [e3] at e1
    have e4 : ((P[fun ω => Real.exp (-Y ω) | 𝒢] ω : ℝ) : ℂ) =
        ((Real.exp (srcVar (H \ A ω) (s ω) / 2) : ℝ) : ℂ) := by
      have := e2.trans e1
      simp only [Function.comp_apply, Complex.ofRealCLM_apply] at this
      rw [this, covLim_zero (hD ω) sdiff_subset (hs ω),
        show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, GFF.zeroGFFTestCov_zero_zero, neg_zero]
      simp [cfVal]
    exact_mod_cast e4
  have hZeq : Z =ᵐ[P] (fun ω => Real.exp (-M₁ ω + b ω)) * fun ω => Real.exp (-Y ω) := by
    filter_upwards [hΛY] with ω hω
    simp only [hZdef, Pi.mul_apply, hω, ← Real.exp_add]
    congr 1; ring
  have hN : P[Z | 𝒢] =ᵐ[P] N := by
    have hfg : Integrable ((fun ω => Real.exp (-M₁ ω + b ω)) * fun ω => Real.exp (-Y ω)) P := hZi.congr hZeq
    filter_upwards [condExp_congr_ae hZeq, condExp_mul_of_stronglyMeasurable_left
      (f := fun ω => Real.exp (-M₁ ω + b ω)) (g := fun ω => Real.exp (-Y ω)) hEm hfg hYi, hcY] with ω e1 e2 e3
    rw [e1, e2, Pi.mul_apply, e3]
  -- Bayes and the tilt, test function by test function
  intro φ
  set Xφ : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((h₂ ω + Γ ω) φ : ℂ)) with hXφ
  have hΓφm : Measurable[𝒢] fun ω => covLim (H \ A ω) (s ω) φ := measurable_covLim_rand hA𝒢 hAc hsm φ
  have hXφm : AEStronglyMeasurable Xφ P := by
    have : Measurable fun ω => (h₂ ω + Γ ω) φ := by
      simp only [add_apply, hΓφ]
      exact ((measurable_distOn_apply φ).comp hh₂).add (hΓφm.mono h𝒢 le_rfl)
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp this))).aestronglyMeasurable
  have hXφb : ∀ ω, ‖Xφ ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul _).le
  have hbayes := condExp_withDensity_ae_eq h𝒢 hZm (fun ω => (Real.exp_pos _).le) hZi hNm hNpos hN hXφm hXφb
  set Fφ : Ω → ℂ := fun ω => ((Real.exp (-M₁ ω + b ω) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (covLim (H \ A ω) (s ω) φ : ℂ)) with hFφ
  set Gφ : Ω → ℂ := fun ω => ((Real.exp (-srcLimR s h₂ ω) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (h₂ ω φ : ℂ)) with hGφ
  have hZX : (fun ω => Z ω • Xφ ω) =ᵐ[P] fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Fφ ω) (Gφ ω) := by
    filter_upwards [hZeq] with ω hω
    rw [hω, Complex.real_smul, hXφ, hFφ, hGφ, ContinuousLinearMap.mul_apply']
    simp only [Pi.mul_apply, add_apply, hΓφ, Complex.ofReal_add, mul_add, Complex.exp_add,
      Complex.ofReal_mul, hYdef]
    ring
  have hFm : AEStronglyMeasurable[𝒢] Fφ P :=
    ((Complex.measurable_ofReal.comp hEm.measurable).mul
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hΓφm)))).aestronglyMeasurable
  have hGi : Integrable Gφ P := by
    refine hYi.mono' (((Complex.measurable_ofReal.comp
      (measurable_srcLimR h𝒢 hh₂ hsm).neg.exp).mul (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh₂))))).aestronglyMeasurable)
      (ae_of_all _ fun ω => le_of_eq ?_)
    rw [hGφ, norm_mul, norm_cexp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hFGi : Integrable (fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Fφ ω) (Gφ ω)) P := by
    refine hZi.mono' ((hFm.mono h𝒢).mul hGi.aestronglyMeasurable) ?_
    filter_upwards [hZX] with ω hω
    rw [ContinuousLinearMap.mul_apply'] at hω
    rw [ContinuousLinearMap.mul_apply', ← hω, norm_smul, norm_cexp_I_mul, mul_one, Real.norm_eq_abs]
    exact (abs_of_pos (Real.exp_pos _)).le
  have hpull := condExp_bilin_of_aestronglyMeasurable_left (m := 𝒢) (ContinuousLinearMap.mul ℝ ℂ) hFm hFGi hGi
  have htilt := condExp_exp_neg_srcLimR_mul_cexp h𝒢 hA𝒢 hAc hcond hh₂ hsm hs hbd φ
  filter_upwards [hbayes, hQP.ae_le (condExp_congr_ae hZX), hQP.ae_le hpull, hQP.ae_le htilt]
    with ω e1 e2 e3 e4
  rw [e1, e2, e3, ContinuousLinearMap.mul_apply', e4, hFφ, hNdef, cfVal, Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_exp]
  have h1 : Complex.exp ((-M₁ ω + b ω : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h2 : Complex.exp ((srcVar (H \ A ω) (s ω) / 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Model

end LocalExt

end InteractingSLE
