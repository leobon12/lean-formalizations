/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.DiskFourier
import InteractingSLE.Spec.Sec6.CircleCutoff

/-!
# Harmonic functions on the disk vanishing on the circle off a finite set

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 28, `source/spec/p145-192.md`,
`#aux-28-proof`, pp. 162–163). The disk step of Aux. lemma 28: a harmonic function `u` on the unit
disk with

  `sup_{|ζ| = r} |u(ζ)| ≤ C (1 − r)^{−α}`

which tends continuously to zero at every point of the unit circle outside a finite set `E`
vanishes identically. The source proves this for `0 < α < 1`; we prove it for `0 ≤ α < 1/2`,
which is all that Aux. lemma 28 uses (there the bound holds for every `α > 0`).

## Proof (the source's boundary-distribution argument)

Write `u(re^{it}) = ∑ c_n r^{|n|} e^{int}` (`InteractingSLE.Sec6.hasSum_diskCoeff`); then
`|c_n| = O(|n|^α)` (`norm_diskCoeff_le_of_growth`), so the coefficients define the boundary
distribution `T(ψ) = ∑ c_n ψ̂(−n)` (`bdryPair`) on `C¹` functions, continuous for the `H¹` norm
(`pairing_bound`, since `α < 1/2`), and `T(ψ) = lim_{r → 1} (2π)⁻¹ ∫ u(re^{it}) ψ(t) dt`
(`tendsto_pairing_bdryPair`).

1. *Support.* Uniform convergence to zero on compact subarcs outside `E` gives `T(ψ) = 0` when
   `ψ` vanishes near `E` (`bdryPair_eq_zero_of_vanish_near`).
2. *Order zero.* If `ψ` vanishes on `E` to first order (`‖ψ(t)‖ ≤ L ‖e^{it} − p‖`), then
   `ψ (1 − χ_δ) → 0` in `H¹` as `δ → 0`, so `T(ψ) = 0` (`bdryPair_eq_zero_of_lipschitz`).
   This replaces the source's "a distribution supported at finitely many points is a finite
   linear combination of point masses and their derivatives": the `H¹` continuity of `T`
   (order `< 1`) leaves only the point masses.
3. *Point masses.* With bumps `b_p` equal to `1` near `p ∈ E` and `0` near the rest of `E`,
   `e^{int} − ∑_p p^n b_p` vanishes to first order on `E`, whence `c_m = ∑_p β_p p^{−m}`
   with `β_p = T(b_p)` (`diskCoeff_eq_sum`).
4. *Growth.* Then `u = ∑_p β_p P(·, p)` (Poisson kernels), and `u(r p) ≥ |β_p| (1+r)/(1−r) − B`
   contradicts `|u| ≤ C (1 − r)^{−α}` unless `β_p = 0` (`InteractingSLE.Sec6.eqOn_zero_of_growth`).
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ComplexConjugate Interval

namespace InteractingSLE.Sec6

/-- A `C¹` loop on `[0, 2π]`: `ψ` has derivative `ψ'` everywhere, `ψ'` is continuous and
`ψ(2π) = ψ(0)`. -/
def IsC1Loop (ψ ψ' : ℝ → ℂ) : Prop :=
  (∀ t, HasDerivAt ψ (ψ' t) t) ∧ Continuous ψ' ∧ ψ (2 * π) = ψ 0

theorem IsC1Loop.continuous {ψ ψ' : ℝ → ℂ} (h : IsC1Loop ψ ψ') : Continuous ψ :=
  continuous_iff_continuousAt.2 fun t => (h.1 t).continuousAt

/-- The boundary distribution `T(ψ) = ∑ c_n ψ̂(−n)` of `Re F`. -/
def bdryPair (F : ℂ → ℂ) (ψ : ℝ → ℂ) : ℂ := ∑' n : ℤ, diskCoeff F n * circCoeff ψ (-n)

/-! ## The radial limit of the pairing -/

section Standing

variable {F : ℂ → ℂ} {u : ℂ → ℝ} {K α : ℝ}

/-- Summability of the boundary pairing on `C¹` loops. -/
theorem summable_bdryPair (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hc : ∀ n, ‖diskCoeff F n‖ ≤ K * (1 + |(n : ℝ)|) ^ α) {ψ ψ' : ℝ → ℂ} (hψ : IsC1Loop ψ ψ') :
    Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ (-n)‖ :=
  (pairing_bound hα0 hα hc hψ.1 hψ.2.1 hψ.2.2 one_pos).1

/-- **Abel limit.** `(2π)⁻¹ ∫₀^{2π} u(re^{it}) ψ(t) dt → T(ψ)` as `r → 1⁻`. -/
theorem tendsto_pairing_bdryPair (hF : DifferentiableOn ℂ F (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hc : ∀ n, ‖diskCoeff F n‖ ≤ K * (1 + |(n : ℝ)|) ^ α) {ψ ψ' : ℝ → ℂ} (hψ : IsC1Loop ψ ψ') :
    Tendsto (fun r : ℝ => ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t)
      (𝓝[<] 1) (𝓝 (bdryPair F ψ)) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have heq : (fun r : ℝ => ∑' n : ℤ, diskCoeff F n * (r : ℂ) ^ n.natAbs * circCoeff ψ (-n)) =ᶠ[𝓝[<] 1]
      fun r : ℝ => ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t := by
    filter_upwards [hev] with r hr
    exact (hasSum_pairing hF hu hψ.continuous hr.1.le hr.2).tsum_eq
  refine Tendsto.congr' heq ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖diskCoeff F n‖ *
    ‖circCoeff ψ (-n)‖) (summable_bdryPair hα0 hα hc hψ) (fun n => ?_) ?_
  · have h1 : Tendsto (fun r : ℝ => (r : ℂ) ^ n.natAbs) (𝓝[<] 1) (𝓝 1) := by
      have : Tendsto (fun r : ℝ => (r : ℂ) ^ n.natAbs) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) ^ n.natAbs)) :=
        ((Complex.continuous_ofReal.pow n.natAbs).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    have := ((h1.const_mul (diskCoeff F n)).mul_const (circCoeff ψ (-n)))
    simpa using this
  · filter_upwards [hev] with r hr n
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    have : r ^ n.natAbs ≤ 1 := pow_le_one₀ hr.1.le hr.2.le
    have h0 : 0 ≤ ‖diskCoeff F n‖ := norm_nonneg _
    have h0' : 0 ≤ ‖circCoeff ψ (-n)‖ := norm_nonneg _
    nlinarith [mul_nonneg h0 h0']

end Standing

/-! ## Step 1: the boundary distribution is supported on `E` -/

/-- The radial functions converge to zero uniformly on the compact set of angles at distance
`≥ δ` from `E`. -/
theorem tendstoUniformlyOn_polar_zero {u : ℂ → ℝ} {E : Finset ℂ}
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) :
    TendstoUniformlyOn (fun r t => u (polarPt r t)) (fun _ => 0) (𝓝[<] 1)
      {t ∈ Icc (0 : ℝ) (2 * π) | ∀ p ∈ E, δ ≤ ‖exp (t * I) - p‖} := by
  have hK : IsCompact {t ∈ Icc (0 : ℝ) (2 * π) | ∀ p ∈ E, δ ≤ ‖exp (t * I) - p‖} := by
    have hset : {t : ℝ | ∀ p ∈ E, δ ≤ ‖exp (t * I) - p‖} =
        ⋂ p ∈ E, {t : ℝ | δ ≤ ‖exp (t * I) - p‖} := by ext; simp
    show IsCompact (Icc (0 : ℝ) (2 * π) ∩ {t : ℝ | ∀ p ∈ E, δ ≤ ‖exp (t * I) - p‖})
    refine isCompact_Icc.inter_right ?_
    rw [hset]
    exact isClosed_biInter fun p _ =>
      isClosed_le continuous_const (by fun_prop)
  refine (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    (tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun x hx => ?_)
  refine Uniform.tendsto_nhds_right.1 ?_
  set q := exp (x * I)
  have hq1 : ‖q‖ = 1 := Complex.norm_exp_ofReal_mul_I x
  have hqE : q ∉ E := fun hqE => by
    have := hx.2 q hqE
    rw [sub_self, norm_zero] at this
    linarith
  have hlim : Tendsto (fun y : ℝ × ℝ => polarPt y.1 y.2) (𝓝[<] 1 ×ˢ 𝓝 x)
      (𝓝[ball (0 : ℂ) 1] q) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun y : ℝ × ℝ => polarPt y.1 y.2 := by unfold polarPt; fun_prop
      have := hc.tendsto ((1 : ℝ), x)
      simp only [polarPt, Complex.ofReal_one, one_mul] at this
      rw [nhds_prod_eq] at this
      exact this.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
    · have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      filter_upwards [hev.prod_inl _] with y hy
      exact polarPt_mem_ball hy.1.le hy.2 y.2
  exact ((hbd q hq1 hqE).comp hlim).mono_left (Filter.prod_mono le_rfl nhdsWithin_le_nhds)

/-- **Support of the boundary distribution** (proof of Aux. lemma 28: "On every compact subarc
outside `E` the convergence to zero is uniform, so `T` is supported on `E`"). -/
theorem bdryPair_eq_zero_of_vanish_near {F : ℂ → ℂ} {u : ℂ → ℝ} {K α : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z)
    (hα0 : 0 ≤ α) (hα : α < 1 / 2) (hc : ∀ n, ‖diskCoeff F n‖ ≤ K * (1 + |(n : ℝ)|) ^ α)
    {E : Finset ℂ} (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0))
    {ψ ψ' : ℝ → ℂ} (hψ : IsC1Loop ψ ψ') {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ t : ℝ, ∀ p ∈ E, ‖exp (t * I) - p‖ < δ → ψ t = 0) :
    bdryPair F ψ = 0 := by
  refine tendsto_nhds_unique (tendsto_pairing_bdryPair hF hu hα0 hα hc hψ) ?_
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) (2 * π))
    hψ.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, by positivity⟩)
  have hunif := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_polar_zero hbd hδ)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hunif (ε / (M + 1)) (by positivity)] with r hr
  rw [dist_zero_right]
  have hbound : ∀ t ∈ Ι (0 : ℝ) (2 * π), ‖(u (polarPt r t) : ℂ) * ψ t‖ ≤ ε / (M + 1) * M := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) (2 * π) := Ioc_subset_Icc_self (by
      rwa [uIoc_of_le (by positivity)] at ht)
    by_cases hfar : ∀ p ∈ E, δ ≤ ‖exp (t * I) - p‖
    · have h1 := hr t ⟨htI, hfar⟩
      rw [dist_zero_left, Real.norm_eq_abs] at h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1.le (hM t htI) (norm_nonneg _) (by positivity)
    · simp only [not_forall, not_le] at hfar
      obtain ⟨p, hp, hpt⟩ := hfar
      rw [hvan t p hp hpt, mul_zero, norm_zero]
      positivity
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hI
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (2 * π)⁻¹ * ‖∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t‖
      ≤ (2 * π)⁻¹ * (ε / (M + 1) * M * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ε * (M / (M + 1)) := by field_simp
    _ < ε := by
        have : M / (M + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
        nlinarith

/-! ## Step 2: the boundary distribution has order zero -/

theorem circCoeff_sub {ψ₁ ψ₂ : ℝ → ℂ} (h1 : Continuous ψ₁) (h2 : Continuous ψ₂) (n : ℤ) :
    circCoeff (fun t => ψ₁ t - ψ₂ t) n = circCoeff ψ₁ n - circCoeff ψ₂ n := by
  unfold circCoeff
  rw [← mul_sub, ← intervalIntegral.integral_sub]
  · congr 1; refine intervalIntegral.integral_congr fun t _ => ?_; simp only; ring
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I)) * ψ₁ t).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-((n : ℂ) * t * I)) * ψ₂ t).intervalIntegrable _ _

theorem bdryPair_sub {F : ℂ → ℂ} {ψ₁ ψ₂ : ℝ → ℂ} (h1 : Continuous ψ₁) (h2 : Continuous ψ₂)
    (hs1 : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ₁ (-n)‖)
    (hs2 : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ₂ (-n)‖) :
    bdryPair F (fun t => ψ₁ t - ψ₂ t) = bdryPair F ψ₁ - bdryPair F ψ₂ := by
  unfold bdryPair
  have hs1' : Summable fun n => diskCoeff F n * circCoeff ψ₁ (-n) :=
    Summable.of_norm (by simpa only [norm_mul] using hs1)
  have hs2' : Summable fun n => diskCoeff F n * circCoeff ψ₂ (-n) :=
    Summable.of_norm (by simpa only [norm_mul] using hs2)
  rw [← hs1'.tsum_sub hs2']
  congr 1; funext n
  rw [circCoeff_sub h1 h2, mul_sub]

theorem norm_bdryPair_le {F : ℂ → ℂ} {ψ : ℝ → ℂ}
    (hs : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ (-n)‖) :
    ‖bdryPair F ψ‖ ≤ ∑' n, ‖diskCoeff F n‖ * ‖circCoeff ψ (-n)‖ := by
  unfold bdryPair
  refine (norm_tsum_le_tsum_norm (by simpa only [norm_mul] using hs)).trans_eq ?_
  simp only [norm_mul]

/-- The angles `t` with `e^{it} ∈ E` form a null set. -/
theorem ae_exp_notMem (E : Finset ℂ) :
    ∀ᵐ t : ℝ, exp (t * I) ∉ E := by
  have hcount : {t : ℝ | exp (t * I) ∈ E}.Countable := by
    have hsub : {t : ℝ | exp (t * I) ∈ E} ⊆
        ⋃ p ∈ E, range (fun k : ℤ => Complex.arg p + 2 * π * k) := by
      intro t ht
      simp only [mem_iUnion, mem_range]
      refine ⟨_, ht, ?_⟩
      have hp : exp (Complex.arg (exp (t * I)) * I) = exp (t * I) := by
        have := Complex.norm_mul_exp_arg_mul_I (exp (t * I))
        rwa [Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul] at this
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 hp.symm
      refine ⟨k, ?_⟩
      have h := congrArg Complex.im hk
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.mul_re] at h
      linarith
    refine Countable.mono hsub ?_
    exact (Finset.countable_toSet E).biUnion fun p _ => countable_range _
  have := hcount.measure_zero volume
  rw [ae_iff]
  simpa using this

/-- Off `E`, every point of the circle is eventually at distance `> 2δ` from `E`. -/
theorem eventually_two_mul_lt_dist {E : Finset ℂ} {t : ℝ} (ht : exp (t * I) ∉ E) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p ∈ E, 2 * δ < ‖exp (t * I) - p‖ := by
  refine (Filter.eventually_all_finset E).2 fun p hp => ?_
  have hpos : 0 < ‖exp (t * I) - p‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => ht (h ▸ hp))
  have h2 : Tendsto (fun δ : ℝ => 2 * δ) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2
  exact (h2.eventually_lt_const hpos).filter_mono nhdsWithin_le_nhds

/-- **Order zero** (proof of Aux. lemma 28, the step "a distribution supported at finitely many
points is a finite linear combination of point masses and their derivatives", in the order-zero
form available here because the boundary distribution is `H¹`-continuous): `T(ψ) = 0` for every
`C¹` loop `ψ` vanishing to first order on `E`. -/
theorem bdryPair_eq_zero_of_lipschitz {F : ℂ → ℂ} {u : ℂ → ℝ} {K α : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z)
    (hα0 : 0 ≤ α) (hα : α < 1 / 2) (hc : ∀ n, ‖diskCoeff F n‖ ≤ K * (1 + |(n : ℝ)|) ^ α)
    {E : Finset ℂ} (hE : ∀ p ∈ E, ‖p‖ = 1)
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0))
    {ψ ψ' : ℝ → ℂ} (hψ : IsC1Loop ψ ψ') {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t : ℝ, ∀ p ∈ E, ‖ψ t‖ ≤ L * ‖exp (t * I) - p‖) :
    bdryPair F ψ = 0 := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_deriv_cutProfile
  have hK : 0 ≤ K := by
    have h0 := hc 0
    simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h0
    linarith [norm_nonneg (diskCoeff F 0)]
  -- the remainders `ψ (1 − χ_δ)` and their derivatives
  let ρ : ℝ → ℝ → ℂ := fun δ t => ψ t * ((1 - circCutoff E δ t : ℝ) : ℂ)
  let ρ' : ℝ → ℝ → ℂ := fun δ t => ψ' t * ((1 - circCutoff E δ t : ℝ) : ℂ) +
    ψ t * ((-circCutoffDeriv E δ t : ℝ) : ℂ)
  have hρ : ∀ δ, IsC1Loop (ρ δ) (ρ' δ) := by
    intro δ
    have hc1 := continuous_circCutoff E δ
    have hc2 := continuous_circCutoffDeriv E δ
    have hψc := hψ.continuous
    have hψ'c := hψ.2.1
    refine ⟨fun t => ?_, by simp only [ρ']; fun_prop, ?_⟩
    · have h1 : HasDerivAt (fun t => ((1 - circCutoff E δ t : ℝ) : ℂ))
          ((-circCutoffDeriv E δ t : ℝ) : ℂ) t := by
        have := ((hasDerivAt_circCutoff E δ t).const_sub 1).ofReal_comp
        simpa using this
      exact (hψ.1 t).mul h1
    · simp only [ρ, hψ.2.2, circCutoff_two_pi]
  -- `ψ − ρ_δ = ψ χ_δ` vanishes near `E`
  have hsplit : ∀ δ, 0 < δ → bdryPair F ψ = bdryPair F (ρ δ) := by
    intro δ hδ
    have hloop : IsC1Loop (fun t => ψ t - ρ δ t) (fun t => ψ' t - ρ' δ t) :=
      ⟨fun t => (hψ.1 t).sub ((hρ δ).1 t), hψ.2.1.sub (hρ δ).2.1, by
        simp only [hψ.2.2, (hρ δ).2.2]⟩
    have h0 : bdryPair F (fun t => ψ t - ρ δ t) = 0 := by
      refine bdryPair_eq_zero_of_vanish_near hF hu hα0 hα hc hbd hloop hδ ?_
      intro t p hp ht
      simp only [ρ, circCutoff_eq_zero hδ hp ht]
      push_cast; ring
    have := bdryPair_sub (F := F) hψ.continuous (hρ δ).continuous
      (summable_bdryPair hα0 hα hc hψ) (summable_bdryPair hα0 hα hc (hρ δ))
    rw [h0] at this
    exact (sub_eq_zero.1 this.symm)
  -- uniform bounds
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) (2 * π))
    hψ.continuous.continuousOn
  obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) (2 * π))
    hψ.2.1.continuousOn
  have hI : ∀ t ∈ Ι (0 : ℝ) (2 * π), t ∈ Icc (0 : ℝ) (2 * π) := fun t ht =>
    Ioc_subset_Icc_self (by rwa [uIoc_of_le (by positivity)] at ht)
  have hχ : ∀ δ t, |1 - circCutoff E δ t| ≤ 1 := fun δ t => by
    rw [abs_le]; constructor <;> linarith [circCutoff_nonneg E δ t, circCutoff_le_one E δ t]
  have hρb : ∀ δ t, t ∈ Icc (0 : ℝ) (2 * π) → ‖ρ δ t‖ ≤ M := fun δ t ht => by
    simp only [ρ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖ψ t‖ * |1 - circCutoff E δ t| ≤ M * 1 :=
          mul_le_mul (hM t ht) (hχ δ t) (abs_nonneg _) (le_trans (norm_nonneg _) (hM t ht))
      _ = M := mul_one M
  have hρ'b : ∀ δ, 0 < δ → ∀ t, t ∈ Icc (0 : ℝ) (2 * π) →
      ‖ρ' δ t‖ ≤ M' + E.card * (8 * D * L) := fun δ hδ t ht => by
    simp only [ρ']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖ψ' t‖ * |1 - circCutoff E δ t| ≤ M' * 1 :=
            mul_le_mul (hM' t ht) (hχ δ t) (abs_nonneg _) (le_trans (norm_nonneg _) (hM' t ht))
        _ = M' := mul_one M'
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
      exact mul_abs_circCutoffDeriv_le hE hδ hD0 hD hL (norm_nonneg _) (hlip t)
  -- pointwise limits off the null set
  have hfar : ∀ t : ℝ, exp (t * I) ∉ E → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ρ δ t = 0 ∧ ρ' δ t = 0 := by
    intro t ht
    filter_upwards [eventually_two_mul_lt_dist ht, self_mem_nhdsWithin] with δ hδ hδ0
    obtain ⟨h1, h2⟩ := circCutoff_eq_one hδ0 hδ
    simp [ρ, ρ', h1, h2]
  have hae := ae_exp_notMem E
  have hlim0 : Tendsto (fun δ => ∫ t in (0 : ℝ)..2 * π, exp (-(((0 : ℤ) : ℂ) * t * I)) * ρ δ t)
      (𝓝[>] 0) (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (a := 0) (b := 2 * π)
      (μ := volume) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ t => exp (-(((0 : ℤ) : ℂ) * t * I)) * ρ δ t) (f := fun _ => 0) (fun _ => M)
      (Eventually.of_forall fun δ =>
        ((by fun_prop : Continuous fun t : ℝ => exp (-(((0 : ℤ) : ℂ) * t * I))).mul
          (hρ δ).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun δ => Eventually.of_forall fun t ht => by
        simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
        exact hρb δ t (hI t ht))
      intervalIntegrable_const
      (by
        filter_upwards [hae] with t ht _
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hfar t ht] with δ hδ
        simp only [hδ.1, mul_zero])
    simpa using this
  have hlim1 : Tendsto (fun δ => ∫ t in (0 : ℝ)..2 * π, ‖ρ' δ t‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (a := 0) (b := 2 * π)
      (μ := volume) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ t => ‖ρ' δ t‖ ^ 2) (f := fun _ => 0) (fun _ => (M' + E.card * (8 * D * L)) ^ 2)
      (Eventually.of_forall fun δ => ((hρ δ).2.1.norm.pow 2).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        refine Eventually.of_forall fun t ht => ?_
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ'b δ hδ t (hI t ht)) 2)
      intervalIntegrable_const
      (by
        filter_upwards [hae] with t ht _
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hfar t ht] with δ hδ
        simp only [hδ.2, norm_zero]
        norm_num)
    simpa using this
  -- the estimate, and the limits `δ → 0`, then `ε → 0`
  set Z := ∑' n, sobWeight α n
  have hstep : ∀ ε, 0 < ε → ‖bdryPair F ψ‖ ≤ K / 2 * (ε * Z) := by
    intro ε hε
    have hbound : ∀ δ ∈ Ioi (0 : ℝ), ‖bdryPair F ψ‖ ≤ ‖diskCoeff F 0‖ * ‖circCoeff (ρ δ) 0‖ +
        K / 2 * (ε * Z + ε⁻¹ * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖ρ' δ t‖ ^ 2)) := by
      intro δ hδ
      rw [hsplit δ hδ]
      obtain ⟨hs, hle⟩ := pairing_bound hα0 hα hc (hρ δ).1 (hρ δ).2.1 (hρ δ).2.2 hε
      exact (norm_bdryPair_le hs).trans hle
    have hc0 : Tendsto (fun δ => circCoeff (ρ δ) 0) (𝓝[>] 0) (𝓝 0) := by
      have := hlim0.const_mul (((2 * π)⁻¹ : ℝ) : ℂ)
      simpa [circCoeff] using this
    have hT : Tendsto (fun δ => ‖diskCoeff F 0‖ * ‖circCoeff (ρ δ) 0‖ +
        K / 2 * (ε * Z + ε⁻¹ * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖ρ' δ t‖ ^ 2))) (𝓝[>] 0)
        (𝓝 (‖diskCoeff F 0‖ * ‖(0 : ℂ)‖ + K / 2 * (ε * Z + ε⁻¹ * ((2 * π)⁻¹ * 0)))) :=
      ((hc0.norm.const_mul _).add
        ((((hlim1.const_mul _).const_mul _).const_add _).const_mul _))
    have := ge_of_tendsto hT (eventually_nhdsWithin_of_forall hbound)
    simpa using this
  have hT : Tendsto (fun ε : ℝ => K / 2 * (ε * Z)) (𝓝[>] 0) (𝓝 (K / 2 * (0 * Z))) :=
    (((tendsto_id).mul_const Z).const_mul _).mono_left nhdsWithin_le_nhds
  have h0 := ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hstep ε hε)
  simp only [zero_mul, mul_zero] at h0
  exact norm_le_zero_iff.1 h0

/-! ## Step 3: point masses -/

/-- `‖z^n − w^n‖ ≤ |n| ‖z − w‖` on the unit circle. -/
theorem norm_zpow_sub_zpow_le {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (n : ℤ) :
    ‖z ^ n - w ^ n‖ ≤ |(n : ℝ)| * ‖z - w‖ := by
  have hnat : ∀ k : ℕ, ‖z ^ k - w ^ k‖ ≤ k * ‖z - w‖ := by
    intro k
    rw [← Commute.geom_sum₂_mul (Commute.all z w) k, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range k, ‖z ^ i * w ^ (k - 1 - i)‖ ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by rw [norm_mul, norm_pow, norm_pow, hz, hw]; simp
      _ = k := by simp
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using hnat k
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    have : (z ^ k)⁻¹ - (w ^ k)⁻¹ = (w ^ k - z ^ k) / (z ^ k * w ^ k) := by
      field_simp
    rw [this, norm_div, norm_mul, norm_pow, norm_pow, hz, hw, one_pow, one_mul, div_one,
      norm_sub_rev, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    exact hnat k

/-- The bump `b_p(t) = 1 − η(‖e^{it} − p‖²/δ²)`: `1` within `δ` of `p`, `0` beyond `2δ`. -/
def circBump (p : ℂ) (δ t : ℝ) : ℝ := 1 - cutProfile (sqDist p t / δ ^ 2)

/-- The derivative of `circBump p δ`. -/
def circBumpDeriv (p : ℂ) (δ t : ℝ) : ℝ :=
  -(deriv cutProfile (sqDist p t / δ ^ 2) * (sqDistDeriv p t / δ ^ 2))

theorem isC1Loop_circBump (p : ℂ) (δ : ℝ) :
    IsC1Loop (fun t => (circBump p δ t : ℂ)) (fun t => (circBumpDeriv p δ t : ℂ)) := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have h := (((hasDerivAt_cutProfile _).comp t ((hasDerivAt_sqDist p t).div_const (δ ^ 2))).const_sub
      1).ofReal_comp
    simpa [circBump, circBumpDeriv] using h
  · unfold circBumpDeriv
    have := continuous_deriv_cutProfile.comp ((continuous_sqDist p).div_const (δ ^ 2))
    have := continuous_sqDistDeriv p
    fun_prop
  · simp only [circBump, sqDist_two_pi]

theorem circBump_eq_one {p : ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : ‖exp (t * I) - p‖ ≤ δ) :
    circBump p δ t = 1 := by
  rw [circBump, cutProfile_eq_zero, sub_zero]
  rw [sqDist_eq, div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) ht 2

theorem circBump_eq_zero {p : ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ ‖exp (t * I) - p‖) :
    circBump p δ t = 0 := by
  rw [circBump, cutProfile_eq_one, sub_self]
  rw [sqDist_eq, le_div_iff₀ (by positivity)]
  nlinarith

theorem abs_circBump_le (p : ℂ) (δ t : ℝ) : |circBump p δ t| ≤ 1 := by
  rw [circBump, abs_le]
  constructor <;> linarith [cutProfile_nonneg (sqDist p t / δ ^ 2),
    cutProfile_le_one (sqDist p t / δ ^ 2)]

/-- A separation radius for a finite set. -/
theorem exists_sep_radius (E : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ E, ∀ q ∈ E, p ≠ q → 3 * δ ≤ ‖p - q‖ := by
  have h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p ∈ E, ∀ q ∈ E, p ≠ q → 3 * δ < ‖p - q‖ := by
    refine (Filter.eventually_all_finset E).2 fun p _ => (Filter.eventually_all_finset E).2
      fun q _ => ?_
    by_cases hpq : p = q
    · exact Eventually.of_forall fun _ h => absurd hpq h
    have hpos : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
    have h3 : Tendsto (fun δ : ℝ => 3 * δ) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 3
    exact ((h3.eventually_lt_const hpos).filter_mono nhdsWithin_le_nhds).mono fun δ hδ _ => hδ
  obtain ⟨δ, hδ, hδ0⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ0, fun p hp q hq hpq => (hδ p hp q hq hpq).le⟩

theorem hasDerivAt_exp_mul_I (n : ℤ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp ((n : ℂ) * t * I)) (((n : ℂ) * I) * exp ((n : ℂ) * t * I)) t := by
  have h : HasDerivAt (fun w : ℂ => (n : ℂ) * w * I) ((n : ℂ) * 1 * I) (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).const_mul (n : ℂ)).mul_const I
  have h2 := (h.cexp).comp_ofReal
  simp only [mul_one] at h2
  convert h2 using 1; ring

theorem circCoeff_sub_sum {e : ℝ → ℂ} (he : Continuous e) (E : Finset ℂ) (a : ℂ → ℂ)
    {b : ℂ → ℝ → ℂ} (hb : ∀ p, Continuous (b p)) (k : ℤ) :
    circCoeff (fun t => e t - ∑ p ∈ E, a p * b p t) k =
      circCoeff e k - ∑ p ∈ E, a p * circCoeff (b p) k := by
  have hint : ∀ f : ℝ → ℂ, Continuous f →
      IntervalIntegrable (fun t : ℝ => exp (-((k : ℂ) * t * I)) * f t) volume 0 (2 * π) :=
    fun f hf => (by fun_prop : Continuous fun t : ℝ => exp (-((k : ℂ) * t * I)) * f t).intervalIntegrable _ _
  unfold circCoeff
  have h1 : (fun t : ℝ => exp (-((k : ℂ) * t * I)) * (e t - ∑ p ∈ E, a p * b p t)) =
      fun t : ℝ => exp (-((k : ℂ) * t * I)) * e t -
        ∑ p ∈ E, a p * (exp (-((k : ℂ) * t * I)) * b p t) := by
    funext t; rw [mul_sub, Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun p _ => ?_; ring
  rw [h1, intervalIntegral.integral_sub (hint e he), intervalIntegral.integral_finsetSum]
  · rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul]; ring
  · exact fun p _ => (hint (b p) (hb p)).const_mul _
  · exact (continuous_finsetSum _ fun p _ => continuous_const.mul
      ((by fun_prop : Continuous fun t : ℝ => exp (-((k : ℂ) * t * I))).mul (hb p))).intervalIntegrable _ _

/-- **Point masses** (Step 3). There are constants `β_p` (the masses `T(b_p)`) with
`c_m = ∑_{p ∈ E} β_p p^{−m}` for every `m`. -/
theorem diskCoeff_eq_sum {F : ℂ → ℂ} {u : ℂ → ℝ} {K α : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z)
    (hα0 : 0 ≤ α) (hα : α < 1 / 2) (hc : ∀ n, ‖diskCoeff F n‖ ≤ K * (1 + |(n : ℝ)|) ^ α)
    {E : Finset ℂ} (hE : ∀ p ∈ E, ‖p‖ = 1)
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0)) :
    ∃ β : ℂ → ℂ, ∀ m : ℤ, diskCoeff F m = ∑ p ∈ E, β p * p ^ (-m) := by
  obtain ⟨δ, hδ, hsep⟩ := exists_sep_radius E
  refine ⟨fun p => bdryPair F (fun t => (circBump p δ t : ℂ)), fun m => ?_⟩
  set n := -m with hn
  let e : ℝ → ℂ := fun t => exp ((n : ℂ) * t * I)
  let ψ : ℝ → ℂ := fun t => e t - ∑ p ∈ E, p ^ n * (circBump p δ t : ℂ)
  let ψ' : ℝ → ℂ := fun t => ((n : ℂ) * I) * e t - ∑ p ∈ E, p ^ n * (circBumpDeriv p δ t : ℂ)
  have he : Continuous e := by simp only [e]; fun_prop
  have hb : ∀ p, Continuous fun t => (circBump p δ t : ℂ) := fun p =>
    (isC1Loop_circBump p δ).continuous
  have hψ : IsC1Loop ψ ψ' := by
    refine ⟨fun t => ?_, ?_, ?_⟩
    · exact (hasDerivAt_exp_mul_I n t).sub (HasDerivAt.fun_sum fun p _ =>
        ((isC1Loop_circBump p δ).1 t).const_mul (p ^ n))
    · have h1 : ∀ p, Continuous fun t => (circBumpDeriv p δ t : ℂ) := fun p =>
        (isC1Loop_circBump p δ).2.1
      exact (continuous_const.mul he).sub (continuous_finsetSum _ fun p _ =>
        continuous_const.mul (h1 p))
    · simp only [ψ, e, (isC1Loop_circBump _ δ).2.2]
      congr 1
      rw [show (n : ℂ) * ((2 * π : ℝ) : ℂ) * I = n * (2 * π * I) by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I]
      simp
  -- `ψ` vanishes to first order on `E`
  have hlip : ∀ t : ℝ, ∀ q ∈ E, ‖ψ t‖ ≤ max |(n : ℝ)| ((1 + E.card) / δ) * ‖exp (t * I) - q‖ := by
    intro t q hq
    have hz : ‖exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    have he' : e t = exp (t * I) ^ n := by
      simp only [e]; rw [← Complex.exp_int_mul]; congr 1; ring
    by_cases hnear : ∃ q₀ ∈ E, ‖exp (t * I) - q₀‖ < δ
    · obtain ⟨q₀, hq₀, hq₀t⟩ := hnear
      have hsum : ∑ p ∈ E, p ^ n * (circBump p δ t : ℂ) = q₀ ^ n := by
        rw [Finset.sum_eq_single q₀]
        · rw [circBump_eq_one hδ hq₀t.le]; simp
        · intro p hp hpq
          rw [circBump_eq_zero hδ]
          · simp
          · have := hsep p hp q₀ hq₀ hpq
            have h2 : ‖p - q₀‖ ≤ ‖exp (t * I) - p‖ + ‖exp (t * I) - q₀‖ := by
              calc ‖p - q₀‖ = ‖(exp (t * I) - q₀) - (exp (t * I) - p)‖ := by ring_nf
                _ ≤ ‖exp (t * I) - q₀‖ + ‖exp (t * I) - p‖ := norm_sub_le _ _
                _ = _ := add_comm _ _
            linarith
        · intro h; exact absurd hq₀ h
      have hψt : ‖ψ t‖ ≤ |(n : ℝ)| * ‖exp (t * I) - q₀‖ := by
        simp only [ψ]; rw [hsum, he']
        exact norm_zpow_sub_zpow_le hz (hE q₀ hq₀) n
      have hcmp : ‖exp (t * I) - q₀‖ ≤ ‖exp (t * I) - q‖ := by
        by_cases hqq : q = q₀
        · rw [hqq]
        · have := hsep q hq q₀ hq₀ hqq
          have h2 : ‖q - q₀‖ ≤ ‖exp (t * I) - q‖ + ‖exp (t * I) - q₀‖ := by
            calc ‖q - q₀‖ = ‖(exp (t * I) - q₀) - (exp (t * I) - q)‖ := by ring_nf
              _ ≤ ‖exp (t * I) - q₀‖ + ‖exp (t * I) - q‖ := norm_sub_le _ _
              _ = _ := add_comm _ _
          linarith
      calc ‖ψ t‖ ≤ |(n : ℝ)| * ‖exp (t * I) - q₀‖ := hψt
        _ ≤ |(n : ℝ)| * ‖exp (t * I) - q‖ := mul_le_mul_of_nonneg_left hcmp (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · simp only [not_exists, not_and, not_lt] at hnear
      have hfar := hnear q hq
      have hψt : ‖ψ t‖ ≤ 1 + E.card := by
        simp only [ψ]
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [he', norm_zpow, hz, one_zpow]
        · refine (norm_sum_le _ _).trans ?_
          calc ∑ p ∈ E, ‖p ^ n * (circBump p δ t : ℂ)‖ ≤ ∑ _p ∈ E, (1 : ℝ) :=
                Finset.sum_le_sum fun p hp => by
                  rw [norm_mul, norm_zpow, hE p hp, one_zpow, one_mul, Complex.norm_real,
                    Real.norm_eq_abs]
                  exact abs_circBump_le p δ t
            _ = E.card := by simp
      calc ‖ψ t‖ ≤ 1 + E.card := hψt
        _ = (1 + E.card) / δ * δ := by field_simp
        _ ≤ (1 + E.card) / δ * ‖exp (t * I) - q‖ :=
            mul_le_mul_of_nonneg_left hfar (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hzero := bdryPair_eq_zero_of_lipschitz hF hu hα0 hα hc hE hbd hψ
    (le_trans (abs_nonneg _) (le_max_left _ _)) hlip
  -- the three sums
  have hsumm : ∀ {φ φ' : ℝ → ℂ}, IsC1Loop φ φ' →
      HasSum (fun k => diskCoeff F k * circCoeff φ (-k)) (bdryPair F φ) := fun hφ =>
    (Summable.of_norm (by simpa only [norm_mul] using summable_bdryPair hα0 hα hc hφ)).hasSum
  have h0 := hsumm hψ
  rw [hzero] at h0
  have he_eq : e = fun t : ℝ => exp (-(((-n : ℤ) : ℂ) * t * I)) := by
    funext t; simp only [e]; push_cast; ring_nf
  have hE' : HasSum (fun k => diskCoeff F k * circCoeff e (-k)) (diskCoeff F (-n)) := by
    rw [he_eq]
    simp_rw [circCoeff_exp_neg]
    have := hasSum_ite_eq (-n) (diskCoeff F (-n))
    refine this.congr_fun fun k => ?_
    split_ifs with h1 <;> simp [h1]
  have hB : HasSum (fun k => ∑ p ∈ E, p ^ n *
      (diskCoeff F k * circCoeff (fun t => (circBump p δ t : ℂ)) (-k)))
      (∑ p ∈ E, p ^ n * bdryPair F (fun t => (circBump p δ t : ℂ))) :=
    hasSum_sum fun p _ => (hsumm (isC1Loop_circBump p δ)).mul_left (p ^ n)
  have hdiff := hE'.sub hB
  have hfun : (fun k => diskCoeff F k * circCoeff e (-k) - ∑ p ∈ E, p ^ n *
      (diskCoeff F k * circCoeff (fun t => (circBump p δ t : ℂ)) (-k))) =
      fun k => diskCoeff F k * circCoeff ψ (-k) := by
    funext k
    simp only [ψ]
    rw [circCoeff_sub_sum he E (fun p => p ^ n) hb, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfun] at hdiff
  have := hdiff.unique h0
  rw [hn, neg_neg] at this
  rw [sub_eq_zero] at this
  rw [this]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hn]; ring

/-! ## Step 4: the growth bound excludes point masses -/

/-- The Poisson series `∑_{m ∈ ℤ} r^{|m|} w^m = 1/(1 − rw) + r w⁻¹/(1 − r w⁻¹)` for `|w| = 1`. -/
theorem hasSum_poissonSeries {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    HasSum (fun m : ℤ => (r : ℂ) ^ m.natAbs * w ^ m)
      (1 / (1 - r * w) + r * w⁻¹ / (1 - r * w⁻¹)) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hn1 : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hn2 : ‖(r : ℂ) * w⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, hw, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]; exact hr1
  have hA : HasSum (fun k : ℕ => (r : ℂ) ^ ((k : ℤ).natAbs) * w ^ (k : ℤ)) (1 / (1 - r * w)) := by
    have := hasSum_geometric_of_norm_lt_one hn1
    rw [one_div]
    refine this.congr_fun fun k => ?_
    rw [Int.natAbs_natCast, zpow_natCast, mul_pow]
  have hB : HasSum (fun k : ℕ => (r : ℂ) ^ ((-((k : ℤ) + 1)).natAbs) * w ^ (-((k : ℤ) + 1)))
      (r * w⁻¹ / (1 - r * w⁻¹)) := by
    have := (hasSum_geometric_of_norm_lt_one hn2).mul_left ((r : ℂ) * w⁻¹)
    rw [div_eq_mul_inv]
    refine this.congr_fun fun k => ?_
    have habs : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
    rw [habs, show (-((k : ℤ) + 1)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, ← inv_pow, ← mul_pow, pow_succ]
    ring
  exact HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => (r : ℂ) ^ m.natAbs * w ^ m) hA hB

theorem poissonSeries_one {r : ℝ} (hr1 : r < 1) :
    1 / (1 - (r : ℂ) * 1) + r * (1 : ℂ)⁻¹ / (1 - r * (1 : ℂ)⁻¹) = ((1 + r) / (1 - r) : ℝ) := by
  have : (1 : ℂ) - r ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg Complex.re h; simp at this; linarith
  push_cast
  field_simp

theorem norm_poissonSeries_le {r : ℝ} (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1)
    (hr : 1 - r ≤ ‖1 - w‖ / 2) :
    ‖1 / (1 - r * w) + r * w⁻¹ / (1 - r * w⁻¹)‖ ≤ 4 / ‖1 - w‖ := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpos : 0 < ‖1 - w‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw1))
  have hr0 : 0 ≤ r := by
    have : ‖1 - w‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one, hw]; norm_num)
    linarith
  have h1 : ‖1 - w‖ / 2 ≤ ‖1 - (r : ℂ) * w‖ := by
    have : (1 : ℂ) - r * w = (1 - w) + ((1 - r : ℝ) : ℂ) * w := by push_cast; ring
    have h := norm_sub_norm_le (1 - w) (-(((1 - r : ℝ) : ℂ) * w))
    rw [sub_neg_eq_add, ← this, norm_neg, norm_mul, hw, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h
    linarith
  have hinv : ‖1 - w⁻¹‖ = ‖1 - w‖ := by
    rw [show (1 : ℂ) - w⁻¹ = -((1 - w) / w) by field_simp; ring, norm_neg, norm_div, hw, div_one]
  have hwi : ‖w⁻¹‖ = 1 := by rw [norm_inv, hw, inv_one]
  have h2 : ‖1 - w‖ / 2 ≤ ‖1 - (r : ℂ) * w⁻¹‖ := by
    have : (1 : ℂ) - r * w⁻¹ = (1 - w⁻¹) + ((1 - r : ℝ) : ℂ) * w⁻¹ := by push_cast; ring
    have h := norm_sub_norm_le (1 - w⁻¹) (-(((1 - r : ℝ) : ℂ) * w⁻¹))
    rw [sub_neg_eq_add, ← this, norm_neg, norm_mul, hwi, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith), hinv] at h
    linarith
  have hp1 : 0 < ‖1 - (r : ℂ) * w‖ := by linarith
  have hp2 : 0 < ‖1 - (r : ℂ) * w⁻¹‖ := by linarith
  have hrw : ‖(r : ℂ) * w⁻¹‖ ≤ 1 := by
    rw [norm_mul, hwi, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1.le
  calc ‖1 / (1 - r * w) + r * w⁻¹ / (1 - r * w⁻¹)‖
      ≤ ‖1 / (1 - (r : ℂ) * w)‖ + ‖(r : ℂ) * w⁻¹ / (1 - r * w⁻¹)‖ := norm_add_le _ _
    _ ≤ 1 / (‖1 - w‖ / 2) + 1 / (‖1 - w‖ / 2) := by
        rw [norm_div, norm_div, norm_one]
        gcongr
    _ = 4 / ‖1 - w‖ := by field_simp; ring

/-- **The disk step of Aux. lemma 28.** A harmonic function `u` on the unit disk with
`|u(z)| ≤ C (1 − |z|)^{−α}` for some `0 ≤ α < 1/2`, tending continuously to zero at every point of
the unit circle outside a finite set `E`, vanishes identically. -/
theorem eqOn_zero_of_growth {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    {E : Finset ℂ} (hE : ∀ p ∈ E, ‖p‖ = 1) {C α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hgrowth : ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ C * (1 - ‖z‖) ^ (-α))
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, u z = 0 := by
  obtain ⟨F, hFa, hFeq⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hF : DifferentiableOn ℂ F (ball 0 1) := hFa.differentiableOn
  have hu' : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z := fun z hz => hFeq hz
  have hc := norm_diskCoeff_le_of_growth hF hu' hgrowth
  obtain ⟨β, hβ⟩ := diskCoeff_eq_sum hF hu' hα0 hα hc hE hbd
  -- the expansion at `r e^{it}` in terms of the masses
  have hexp : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ t : ℝ,
      (u (polarPt r t) : ℂ) = ∑ p ∈ E, β p * (1 / (1 - r * (exp (t * I) / p)) +
        r * (exp (t * I) / p)⁻¹ / (1 - r * (exp (t * I) / p)⁻¹)) := by
    intro r hr0 hr1 t
    have h1 := hasSum_diskCoeff hF hr0 hr1 t
    rw [hu' _ (polarPt_mem_ball hr0 hr1 t)] at h1
    have h2 : HasSum (fun m : ℤ => ∑ p ∈ E, β p * ((r : ℂ) ^ m.natAbs * (exp (t * I) / p) ^ m))
        (∑ p ∈ E, β p * (1 / (1 - r * (exp (t * I) / p)) +
          r * (exp (t * I) / p)⁻¹ / (1 - r * (exp (t * I) / p)⁻¹))) := by
      refine hasSum_sum fun p hp => (hasSum_poissonSeries hr0 hr1 ?_).mul_left (β p)
      rw [norm_div, Complex.norm_exp_ofReal_mul_I, hE p hp, div_one]
    refine h1.unique (h2.congr_fun fun m => ?_)
    rw [hβ m, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_zpow, ← Complex.exp_int_mul, zpow_neg]
    rw [show (m : ℂ) * (t * I) = (m : ℂ) * t * I by ring]
    ring
  -- every mass vanishes
  have hβ0 : ∀ p₀ ∈ E, β p₀ = 0 := by
    intro p₀ hp₀
    set t₀ := Complex.arg p₀
    have hp₀e : exp (t₀ * I) = p₀ := by
      have := Complex.norm_mul_exp_arg_mul_I p₀
      rwa [hE p₀ hp₀, Complex.ofReal_one, one_mul] at this
    set B := ∑ p ∈ E.erase p₀, ‖β p‖ * (4 / ‖1 - p₀ / p‖)
    have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 ∧
        ∀ p ∈ E.erase p₀, 1 - r ≤ ‖1 - p₀ / p‖ / 2 := by
      have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      refine h0.and ((Filter.eventually_all_finset _).2 fun p hp => ?_)
      have hp' : p ≠ p₀ := Finset.ne_of_mem_erase hp
      have hpE : p ∈ E := Finset.mem_of_mem_erase hp
      have hpos : 0 < ‖1 - p₀ / p‖ / 2 := by
        have hp0 : p ≠ 0 := by intro h; rw [h] at hpE; have := hE 0 hpE; simp at this
        have : p₀ / p ≠ 1 := fun h => hp' ((div_eq_one_iff_eq hp0).1 h).symm
        have := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm this))
        positivity
      have h1 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝 0) := by
        have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      exact (h1.eventually_lt_const hpos).mono fun r hr => hr.le
    -- the lower bound at `r p₀`
    have hineq : ∀ᶠ r in 𝓝[<] (1 : ℝ), ‖β p₀‖ * (1 + r) ≤
        C * (1 - r) ^ (1 - α) + B * (1 - r) := by
      filter_upwards [hev] with r ⟨⟨hr0, hr1⟩, hrp⟩
      have hr1' : 0 < 1 - r := by linarith
      have hu0 := hexp r hr0.le hr1 t₀
      rw [hp₀e, ← Finset.add_sum_erase E _ hp₀, div_self (by
        intro h; rw [h] at hp₀; have := hE 0 hp₀; simp at this), poissonSeries_one hr1] at hu0
      have hrest : ‖∑ p ∈ E.erase p₀, β p * (1 / (1 - r * (p₀ / p)) +
          r * (p₀ / p)⁻¹ / (1 - r * (p₀ / p)⁻¹))‖ ≤ B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
        rw [norm_mul]
        have hpE := Finset.mem_of_mem_erase hp
        have hp0 : p ≠ 0 := by intro h; rw [h] at hpE; have := hE 0 hpE; simp at this
        have hw : ‖p₀ / p‖ = 1 := by rw [norm_div, hE p₀ hp₀, hE p hpE, div_one]
        have hw1 : p₀ / p ≠ 1 := fun h =>
          (Finset.ne_of_mem_erase hp) ((div_eq_one_iff_eq hp0).1 h).symm
        exact mul_le_mul_of_nonneg_left (norm_poissonSeries_le hr1 hw hw1 (hrp p hp))
          (norm_nonneg _)
      have hgr := hgrowth _ (polarPt_mem_ball hr0.le hr1 t₀)
      rw [norm_polarPt hr0.le] at hgr
      have hmain : ‖β p₀‖ * ((1 + r) / (1 - r)) ≤ C * (1 - r) ^ (-α) + B := by
        have h1 : ‖β p₀ * (((1 + r) / (1 - r) : ℝ) : ℂ)‖ ≤ ‖(u (polarPt r t₀) : ℂ)‖ + B := by
          rw [hu0]
          set S := ∑ p ∈ E.erase p₀, β p * (1 / (1 - r * (p₀ / p)) +
              r * (p₀ / p)⁻¹ / (1 - r * (p₀ / p)⁻¹))
          calc ‖β p₀ * (((1 + r) / (1 - r) : ℝ) : ℂ)‖
              = ‖(β p₀ * (((1 + r) / (1 - r) : ℝ) : ℂ) + S) - S‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖β p₀ * (((1 + r) / (1 - r) : ℝ) : ℂ) + S‖ + ‖S‖ := norm_sub_le _ _
            _ ≤ _ := by linarith [hrest]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
          Complex.norm_real, Real.norm_eq_abs] at h1
        linarith
      have hrpow : (1 - r) ^ (-α) * (1 - r) = (1 - r) ^ (1 - α) := by
        rw [← Real.rpow_add_one hr1'.ne']; ring_nf
      have := mul_le_mul_of_nonneg_right hmain hr1'.le
      calc ‖β p₀‖ * (1 + r) = ‖β p₀‖ * ((1 + r) / (1 - r)) * (1 - r) := by field_simp
        _ ≤ (C * (1 - r) ^ (-α) + B) * (1 - r) := this
        _ = C * (1 - r) ^ (1 - α) + B * (1 - r) := by rw [add_mul, mul_assoc, hrpow]
    have hL : Tendsto (fun r : ℝ => ‖β p₀‖ * (1 + r)) (𝓝[<] 1) (𝓝 (‖β p₀‖ * (1 + 1))) :=
      ((continuous_const.mul (continuous_const.add continuous_id)).tendsto 1).mono_left
        nhdsWithin_le_nhds
    have hR : Tendsto (fun r : ℝ => C * (1 - r) ^ (1 - α) + B * (1 - r)) (𝓝[<] 1)
        (𝓝 (C * (1 - 1) ^ (1 - α) + B * (1 - 1))) := by
      refine (Continuous.tendsto ?_ 1).mono_left nhdsWithin_le_nhds
      refine (continuous_const.mul ?_).add (continuous_const.mul (continuous_const.sub continuous_id))
      exact (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr (by linarith)
    have := le_of_tendsto_of_tendsto hL hR hineq
    rw [sub_self, Real.zero_rpow (by linarith), mul_zero, mul_zero, add_zero] at this
    have h2 : ‖β p₀‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  -- hence `u = 0`
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hzp : polarPt ‖z‖ (Complex.arg z) = z := Complex.norm_mul_exp_arg_mul_I z
  have h := hexp ‖z‖ (norm_nonneg _) hz1 (Complex.arg z)
  rw [hzp] at h
  have h0 : ∑ p ∈ E, β p * (1 / (1 - ‖z‖ * (exp (Complex.arg z * I) / p)) +
      ‖z‖ * (exp (Complex.arg z * I) / p)⁻¹ / (1 - ‖z‖ * (exp (Complex.arg z * I) / p)⁻¹)) = 0 :=
    Finset.sum_eq_zero fun p hp => by rw [hβ0 p hp, zero_mul]
  rw [h0] at h
  exact_mod_cast h

end InteractingSLE.Sec6
