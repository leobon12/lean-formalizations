/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.FiniteExceptionDisk

/-!
# The boundary distribution of a square-integrable harmonic function

Packet PROVE-SEC6-A2 (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
pp. 165–166): "Consequently the coefficients `c_n` define a distribution `T ∈ H^{−1/2}(∂𝔻)` whose
Poisson extension is `u`. The radial restrictions of `u` converge to `T` in distributions; this
follows by applying Cauchy–Schwarz to the weighted coefficient sum in (PU4) against the rapidly
decreasing Fourier coefficients of a smooth test function. Since the boundary convergence of `u` is
locally uniform on every arc disjoint from `E`, the distribution `T` is supported on `E`."

For `u = Re F` with `∑ |c_n|² / (|n| + 1) < ∞` (PU4) and test functions `ψ` with
`∑ (1 + |n|) |ψ̂(n)|² < ∞` (`H^{1/2}`; every `C¹` loop qualifies, `summable_sobolev_of_isC1Loop`):

* `summable_norm_mul_of_L2`: `∑ |c_n| |ψ̂(−n)| ≤ (ε/2) ∑ |c_n|²/(|n|+1) + (2ε)⁻¹ ∑ (1+|n|)|ψ̂(−n)|²`
  (weighted Cauchy–Schwarz, in AM–GM form);
* `tendsto_pairing_bdryPair_of_summable`: the radial pairings converge to `T(ψ) = ∑ c_n ψ̂(−n)`;
* `bdryPair_eq_zero_of_vanish_on`: `T(ψ) = 0` if `ψ` vanishes on the angles of an open set `U`
  and `u → 0` at every point of the circle outside `U` (support in a closed exceptional set);
* `circCoeff_exp_neg_mul`, `summable_shift`: multiplication by a Fourier mode shifts the
  coefficients, and costs a factor `1 + |m|` in the `H^{1/2}` norm.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace InteractingSLE.Sec6

/-! ## Weighted Cauchy–Schwarz -/

theorem mul_le_weighted {a b w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) :
    a * b ≤ ε / 2 * (a ^ 2 / w) + (2 * ε)⁻¹ * (w * b ^ 2) := by
  have h : 0 ≤ (ε * a - w * b) ^ 2 / (2 * ε * w) := by positivity
  have h2 : (ε * a - w * b) ^ 2 / (2 * ε * w) =
      ε / 2 * (a ^ 2 / w) + (2 * ε)⁻¹ * (w * b ^ 2) - a * b := by
    field_simp; ring
  linarith

/-- **The `H^{−1/2}` × `H^{1/2}` pairing bound.** -/
theorem summable_norm_mul_of_L2 {c d : ℤ → ℂ}
    (hc : Summable fun n : ℤ => ‖c n‖ ^ 2 / (|(n : ℝ)| + 1))
    (hd : Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖d n‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n => ‖c n‖ * ‖d n‖) ∧
      ∑' n, ‖c n‖ * ‖d n‖ ≤ ε / 2 * ∑' n : ℤ, ‖c n‖ ^ 2 / (|(n : ℝ)| + 1) +
        (2 * ε)⁻¹ * ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖d n‖ ^ 2 := by
  have hle : ∀ n : ℤ, ‖c n‖ * ‖d n‖ ≤ ε / 2 * (‖c n‖ ^ 2 / (|(n : ℝ)| + 1)) +
      (2 * ε)⁻¹ * ((1 + |(n : ℝ)|) * ‖d n‖ ^ 2) := by
    intro n
    have h := mul_le_weighted (a := ‖c n‖) (b := ‖d n‖) (w := |(n : ℝ)| + 1) (by positivity) hε
    rwa [add_comm (|(n : ℝ)|) 1] at h ⊢
  have hg := (hc.mul_left (ε / 2)).add (hd.mul_left (2 * ε)⁻¹)
  have hs : Summable (fun n => ‖c n‖ * ‖d n‖) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hg
  refine ⟨hs, (hs.tsum_le_tsum hle hg).trans_eq ?_⟩
  rw [(hc.mul_left _).tsum_add (hd.mul_left _), tsum_mul_left, tsum_mul_left]

theorem abs_le_sq_of_int (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    rw [← sq_abs]; nlinarith

/-- **`C¹` loops are in `H^{1/2}`** (indeed in `H¹`). -/
theorem summable_sobolev_of_isC1Loop {ψ ψ' : ℝ → ℂ} (hψ : IsC1Loop ψ ψ') :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2 := by
  have h1 := (hasSum_sq_circCoeff hψ.continuous).summable
  have h2 := (hasSum_sq_circCoeff hψ.2.1).summable
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h1.add h2)
  have hd := circCoeff_deriv hψ.1 hψ.2.1 hψ.2.2 n
  rw [hd, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, mul_pow, sq_abs]
  have := abs_le_sq_of_int n
  nlinarith [sq_nonneg ‖circCoeff ψ n‖]

/-- The `H^{1/2}` summability, reflected. -/
theorem summable_sobolev_neg {d : ℤ → ℂ} (hd : Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖d n‖ ^ 2) :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖d (-n)‖ ^ 2 := by
  have := (Equiv.neg ℤ).summable_iff.2 hd
  refine this.congr fun n => ?_
  simp

/-! ## The radial limit and the support of the boundary distribution -/

section Standing

variable {F : ℂ → ℂ} {u : ℂ → ℝ}

/-- **Abel limit.** If `∑ |c_n| |ψ̂(−n)| < ∞`, then
`(2π)⁻¹ ∫₀^{2π} u(re^{it}) ψ(t) dt → T(ψ)` as `r → 1⁻`. -/
theorem tendsto_pairing_bdryPair_of_summable (hF : DifferentiableOn ℂ F (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hs : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ (-n)‖) :
    Tendsto (fun r : ℝ => ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t)
      (𝓝[<] 1) (𝓝 (bdryPair F ψ)) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have heq : (fun r : ℝ => ∑' n : ℤ, diskCoeff F n * (r : ℂ) ^ n.natAbs * circCoeff ψ (-n)) =ᶠ[𝓝[<] 1]
      fun r : ℝ => ((2 * π)⁻¹ : ℝ) * ∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t := by
    filter_upwards [hev] with r hr
    exact (hasSum_pairing hF hu hψ hr.1.le hr.2).tsum_eq
  refine Tendsto.congr' heq ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖diskCoeff F n‖ *
    ‖circCoeff ψ (-n)‖) hs (fun n => ?_) ?_
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

/-- The radial functions converge to zero uniformly on the compact set of angles outside an open
set `U`, if `u → 0` at every point of the circle outside `U`. -/
theorem tendstoUniformlyOn_polar_zero_of_open
    {U : Set ℂ} (hU : IsOpen U)
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ U → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0)) :
    TendstoUniformlyOn (fun r t => u (polarPt r t)) (fun _ => 0) (𝓝[<] 1)
      {t ∈ Icc (0 : ℝ) (2 * π) | exp (t * I) ∉ U} := by
  have hK : IsCompact {t ∈ Icc (0 : ℝ) (2 * π) | exp (t * I) ∉ U} := by
    show IsCompact (Icc (0 : ℝ) (2 * π) ∩ {t : ℝ | exp (t * I) ∉ U})
    refine isCompact_Icc.inter_right ?_
    exact (hU.isClosed_compl).preimage (by fun_prop)
  refine (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    (tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun x hx => ?_)
  refine Uniform.tendsto_nhds_right.1 ?_
  set q := exp (x * I)
  have hq1 : ‖q‖ = 1 := Complex.norm_exp_ofReal_mul_I x
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
  exact ((hbd q hq1 hx.2).comp hlim).mono_left (Filter.prod_mono le_rfl nhdsWithin_le_nhds)

/-- **Support of the boundary distribution in a closed exceptional set** (proof of Aux. lemma 29:
"Since the boundary convergence of `u` is locally uniform on every arc disjoint from `E`, the
distribution `T` is supported on `E`"). If `ψ` vanishes at the angles of an open set `U` and
`u → 0` at every point of the circle outside `U`, then `T(ψ) = 0`. -/
theorem bdryPair_eq_zero_of_vanish_on (hF : DifferentiableOn ℂ F (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z) {U : Set ℂ} (hU : IsOpen U)
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ U → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0))
    {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hs : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff ψ (-n)‖)
    (hvan : ∀ t : ℝ, exp (t * I) ∈ U → ψ t = 0) :
    bdryPair F ψ = 0 := by
  refine tendsto_nhds_unique (tendsto_pairing_bdryPair_of_summable hF hu hψ hs) ?_
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) (2 * π))
    hψ.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, by positivity⟩)
  have hunif := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_polar_zero_of_open hU hbd)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hunif (ε / (M + 1)) (by positivity)] with r hr
  rw [dist_zero_right]
  have hbound : ∀ t ∈ Ι (0 : ℝ) (2 * π), ‖(u (polarPt r t) : ℂ) * ψ t‖ ≤ ε / (M + 1) * M := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) (2 * π) := Ioc_subset_Icc_self (by
      rwa [uIoc_of_le (by positivity)] at ht)
    by_cases hfar : exp (t * I) ∈ U
    · rw [hvan t hfar, mul_zero, norm_zero]
      positivity
    · have h1 := hr t ⟨htI, hfar⟩
      rw [dist_zero_left, Real.norm_eq_abs] at h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1.le (hM t htI) (norm_nonneg _) (by positivity)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hI
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (2 * π)⁻¹ * ‖∫ t in (0 : ℝ)..2 * π, (u (polarPt r t) : ℂ) * ψ t‖
      ≤ (2 * π)⁻¹ * (ε / (M + 1) * M * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ε * (M / (M + 1)) := by field_simp
    _ < ε := by
        have : M / (M + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
        nlinarith

end Standing

/-! ## Fourier modes -/

/-- The Fourier mode `e^{−imt}` is a `C¹` loop. -/
theorem isC1Loop_exp_neg (m : ℤ) :
    IsC1Loop (fun t : ℝ => exp (-((m : ℂ) * t * I)))
      (fun t : ℝ => -((m : ℂ) * I) * exp (-((m : ℂ) * t * I))) := by
  refine ⟨fun t => hasDerivAt_exp_neg_mul_I m t, by fun_prop, ?_⟩
  simp only
  rw [show -((m : ℂ) * ((2 * π : ℝ) : ℂ) * I) = ((-m : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- **Multiplication by a mode shifts the coefficients**: `(e^{−imt} ψ)^(k) = ψ̂(k + m)`. -/
theorem circCoeff_exp_neg_mul (m : ℤ) (ψ : ℝ → ℂ) (k : ℤ) :
    circCoeff (fun t => exp (-((m : ℂ) * t * I)) * ψ t) k = circCoeff ψ (k + m) := by
  unfold circCoeff
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **The cost of a shift in `H^{1/2}`**: `1 + |n| ≤ (1 + |m|)(1 + |m − n|)`. -/
theorem summable_shift {d : ℤ → ℂ} (hd : Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖d n‖ ^ 2)
    (m : ℤ) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖d (-n + m)‖ ^ 2) ∧
      ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖d (-n + m)‖ ^ 2 ≤
        (1 + |(m : ℝ)|) * ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖d n‖ ^ 2 := by
  set e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight m)
  have he : ∀ n, e n = -n + m := fun n => rfl
  set g : ℤ → ℝ := fun k => (1 + |((m - k : ℤ) : ℝ)|) * ‖d k‖ ^ 2
  have hgle : ∀ k, g k ≤ (1 + |(m : ℝ)|) * ((1 + |(k : ℝ)|) * ‖d k‖ ^ 2) := by
    intro k
    simp only [g]
    have h1 : 1 + |((m - k : ℤ) : ℝ)| ≤ (1 + |(m : ℝ)|) * (1 + |(k : ℝ)|) := by
      push_cast
      have := abs_sub (m : ℝ) k
      nlinarith [abs_nonneg (m : ℝ), abs_nonneg (k : ℝ), mul_nonneg (abs_nonneg (m : ℝ))
        (abs_nonneg (k : ℝ))]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hg : Summable g := Summable.of_nonneg_of_le (fun k => by positivity) hgle (hd.mul_left _)
  have hcomp : (fun n : ℤ => (1 + |(n : ℝ)|) * ‖d (-n + m)‖ ^ 2) = g ∘ e := by
    funext n
    simp only [Function.comp, g, he]
    congr 3
    push_cast; ring
  rw [hcomp]
  refine ⟨e.summable_iff.2 hg, ?_⟩
  rw [show tsum (g ∘ e) = ∑' n, g (e n) from rfl, e.tsum_eq g, ← tsum_mul_left]
  exact hg.tsum_le_tsum hgle (hd.mul_left _)

end InteractingSLE.Sec6
