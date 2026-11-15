/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.SubdomainCov
import InteractingSLE.GFF.LocalSets.MarkovNesting
import InteractingSLE.GFF.LocalSets.SubdomainMGF
import InteractingSLE.WangWu.GrowthVariance

/-!
# Conditional covariances with an energy-Cauchy source, as distributions

Packet PROVE-LOCEXT-D, item 2 (infrastructure). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L206,
p. 250, "Conditional Cameron–Martin shifting changes the mean …").

For an open `U ⊆ ℍ` the zero-boundary covariance `Cov_U(φ, ψ) = zeroGFFTestCov U φ ψ` is the inner product of the Gram
vectors `covVec U φ`. Let `s_k` be test functions that are Cauchy for the half-plane energy
(`Cov_ℍ(s_n − s_m, s_n − s_m) ≤ 16^{−N}` for `n, m ≥ N`, `IsCovCauchy`). Then:

* `tendsto_covLim`: `Γ_U(φ) = lim_k Cov_U(φ, s_k)` exists for every test function `φ` (Cauchy–Schwarz and domain
  monotonicity `Cov_U ≤ Cov_ℍ`);
* `abs_covLim_le`: `|Γ_U(φ)| ≤ √(Cov_ℍ(φ, φ)) · (√(Cov_ℍ(s_0, s_0)) + 1)`;
* **`covLimDist`**: `Γ_U` is a distribution on `ℍ` (`covLimDist_apply`), via `TestFunction.limitCLM` and the sup-norm
  bound `Cov_ℍ(φ, φ) ≤ C_K ‖φ‖²_∞` on test functions supported in a compact `K` (`zeroGFFTestCov_self_le_of_ball`);
* `lintegral_sq_le_of_condCharFun`: a conditionally centred Gaussian `Y` with conditional variance `V ≤ ε` has
  `E[Y²] ≤ 4ε` (from the conditional moment generating function and `x²/2 + 2 ≤ eˣ + e⁻ˣ`).

In the tilt of the next file, `Γ_{ℍ∖A}(φ)` is the conditional covariance of the zero-boundary part `h₂(φ)` with the
source pairing `(h₂, v)`, i.e. the Green potential `G_{ℍ∖A} v` paired with `φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets

/-! ### Bilinearity and Cauchy–Schwarz for the zero-boundary covariance -/

section Bilinear

variable {U : Set ℂ}

theorem zeroGFFTestCov_comm (hU : IsOpen U) (hUH : U ⊆ H) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ ψ = zeroGFFTestCov U ψ φ := by
  rw [zeroGFFTestCov_eq_inner_covVec hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH, real_inner_comm]

theorem zeroGFFTestCov_add_right (hU : IsOpen U) (hUH : U ⊆ H) (φ ψ χ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ ⇑(ψ + χ) = zeroGFFTestCov U φ ψ + zeroGFFTestCov U φ χ := by
  rw [zeroGFFTestCov_eq_inner_covVec hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH,
    zeroGFFTestCov_eq_inner_covVec hU hUH, covVec_add hU hUH, inner_add_right]

theorem zeroGFFTestCov_sub_right (hU : IsOpen U) (hUH : U ⊆ H) (φ ψ χ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ ⇑(ψ - χ) = zeroGFFTestCov U φ ψ - zeroGFFTestCov U φ χ := by
  rw [zeroGFFTestCov_eq_inner_covVec hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH,
    zeroGFFTestCov_eq_inner_covVec hU hUH, covVec_sub hU hUH, inner_sub_right]

theorem zeroGFFTestCov_smul_right (hU : IsOpen U) (hUH : U ⊆ H) (c : ℝ) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ ⇑(c • ψ) = c * zeroGFFTestCov U φ ψ := by
  rw [zeroGFFTestCov_eq_inner_covVec hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH, covVec_smul hU hUH,
    real_inner_smul_right]

theorem zeroGFFTestCov_add_left (hU : IsOpen U) (hUH : U ⊆ H) (φ ψ χ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U ⇑(ψ + χ) φ = zeroGFFTestCov U ψ φ + zeroGFFTestCov U χ φ := by
  rw [zeroGFFTestCov_comm hU hUH, zeroGFFTestCov_add_right hU hUH, zeroGFFTestCov_comm hU hUH φ ψ,
    zeroGFFTestCov_comm hU hUH φ χ]

theorem zeroGFFTestCov_smul_left (hU : IsOpen U) (hUH : U ⊆ H) (c : ℝ) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U ⇑(c • ψ) φ = c * zeroGFFTestCov U ψ φ := by
  rw [zeroGFFTestCov_comm hU hUH, zeroGFFTestCov_smul_right hU hUH, zeroGFFTestCov_comm hU hUH φ ψ]

theorem zeroGFFTestCov_self_eq_norm_sq (hU : IsOpen U) (hUH : U ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ φ = ‖covVec U φ‖ ^ 2 := by
  rw [zeroGFFTestCov_eq_inner_covVec hU hUH, real_inner_self_eq_norm_sq]

theorem sqrt_zeroGFFTestCov_self (hU : IsOpen U) (hUH : U ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    Real.sqrt (zeroGFFTestCov U φ φ) = ‖covVec U φ‖ := by
  rw [zeroGFFTestCov_self_eq_norm_sq hU hUH, Real.sqrt_sq (norm_nonneg _)]

/-- **Cauchy–Schwarz** for the zero-boundary covariance. -/
theorem abs_zeroGFFTestCov_le (hU : IsOpen U) (hUH : U ⊆ H) (φ ψ : TestOn upperHalfPlaneOpens) :
    |zeroGFFTestCov U φ ψ| ≤ Real.sqrt (zeroGFFTestCov U φ φ) * Real.sqrt (zeroGFFTestCov U ψ ψ) := by
  rw [sqrt_zeroGFFTestCov_self hU hUH, sqrt_zeroGFFTestCov_self hU hUH, zeroGFFTestCov_eq_inner_covVec hU hUH]
  exact abs_real_inner_le_norm _ _

/-- Domain monotonicity of the variance: `Cov_U(φ, φ) ≤ Cov_ℍ(φ, φ)`. -/
theorem zeroGFFTestCov_self_le_H (hU : IsOpen U) (hUH : U ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U φ φ ≤ zeroGFFTestCov H φ φ :=
  zeroGFFTestCov_mono hU isOpen_H hUH subset_rfl φ

end Bilinear

/-! ### Covariance limits along an energy-Cauchy source -/

section Limit

/-- **Energy-Cauchy test functions**: `Cov_ℍ(s_n − s_m, s_n − s_m) ≤ 16^{−N}` for `n, m ≥ N`. -/
def IsCovCauchy (s : ℕ → TestOn upperHalfPlaneOpens) : Prop :=
  ∀ N n m : ℕ, N ≤ n → N ≤ m → zeroGFFTestCov H ⇑(s n - s m) ⇑(s n - s m) ≤ (1 / 16 : ℝ) ^ N

theorem sqrt_one_div_sixteen_pow (N : ℕ) : Real.sqrt ((1 / 16 : ℝ) ^ N) = (1 / 4 : ℝ) ^ N := by
  rw [show (1 / 16 : ℝ) ^ N = ((1 / 4 : ℝ) ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
    Real.sqrt_sq (by positivity)]

variable {U : Set ℂ} {s : ℕ → TestOn upperHalfPlaneOpens}

theorem sqrt_zeroGFFTestCov_sub_le (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) {N n m : ℕ} (hn : N ≤ n)
    (hm : N ≤ m) : Real.sqrt (zeroGFFTestCov U ⇑(s n - s m) ⇑(s n - s m)) ≤ (1 / 4 : ℝ) ^ N := by
  rw [← sqrt_one_div_sixteen_pow]
  exact Real.sqrt_le_sqrt ((zeroGFFTestCov_self_le_H hU hUH _).trans (hs N n m hn hm))

theorem cauchySeq_zeroGFFTestCov (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s)
    (φ : TestOn upperHalfPlaneOpens) : CauchySeq fun k => zeroGFFTestCov U φ (s k) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set a := Real.sqrt (zeroGFFTestCov U φ φ) with ha
  have ht : Tendsto (fun N : ℕ => a * (1 / 4 : ℝ) ^ N) atTop (𝓝 (a * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul a
  rw [mul_zero] at ht
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, ← zeroGFFTestCov_sub_right hU hUH]
  refine lt_of_le_of_lt ((abs_zeroGFFTestCov_le hU hUH _ _).trans ?_) hN
  exact mul_le_mul_of_nonneg_left (sqrt_zeroGFFTestCov_sub_le hU hUH hs hn le_rfl) (Real.sqrt_nonneg _)

variable (U s) in
/-- `Γ_U(φ) = lim_k Cov_U(φ, s_k)`. -/
def covLim (φ : TestOn upperHalfPlaneOpens) : ℝ := limUnder atTop fun k => zeroGFFTestCov U φ (s k)

theorem tendsto_covLim (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (φ : TestOn upperHalfPlaneOpens) :
    Tendsto (fun k => zeroGFFTestCov U φ (s k)) atTop (𝓝 (covLim U s φ)) :=
  (cauchySeq_zeroGFFTestCov hU hUH hs φ).tendsto_limUnder

theorem covLim_add (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (φ ψ : TestOn upperHalfPlaneOpens) :
    covLim U s (φ + ψ) = covLim U s φ + covLim U s ψ := by
  refine tendsto_nhds_unique (tendsto_covLim hU hUH hs (φ + ψ)) ?_
  refine ((tendsto_covLim hU hUH hs φ).add (tendsto_covLim hU hUH hs ψ)).congr fun k => ?_
  rw [zeroGFFTestCov_add_left hU hUH]

theorem covLim_smul (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (c : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    covLim U s (c • φ) = c * covLim U s φ := by
  refine tendsto_nhds_unique (tendsto_covLim hU hUH hs (c • φ)) ?_
  refine ((tendsto_covLim hU hUH hs φ).const_mul c).congr fun k => ?_
  rw [zeroGFFTestCov_smul_left hU hUH]

variable (s) in
/-- The bound `√(Cov_ℍ(s_0, s_0)) + 1` on `√(Cov_ℍ(s_k, s_k))`. -/
def covBound : ℝ := Real.sqrt (zeroGFFTestCov H (s 0) (s 0)) + 1

theorem sqrt_zeroGFFTestCov_le_covBound (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (k : ℕ) :
    Real.sqrt (zeroGFFTestCov U (s k) (s k)) ≤ covBound s := by
  refine (Real.sqrt_le_sqrt (zeroGFFTestCov_self_le_H hU hUH _)).trans ?_
  rw [sqrt_zeroGFFTestCov_self isOpen_H subset_rfl, covBound, sqrt_zeroGFFTestCov_self isOpen_H subset_rfl]
  have e : covVec H (s k) = covVec H (s 0) + covVec H ⇑(s k - s 0) := by
    rw [covVec_sub isOpen_H subset_rfl]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  have h1 := sqrt_zeroGFFTestCov_sub_le (U := H) isOpen_H subset_rfl hs (N := 0) (n := k) (m := 0)
    (Nat.zero_le _) le_rfl
  rw [sqrt_zeroGFFTestCov_self isOpen_H subset_rfl, pow_zero] at h1
  exact h1

theorem covBound_pos : 0 < covBound s := by
  unfold covBound; positivity

/-- `|Γ_U(φ)| ≤ √(Cov_ℍ(φ, φ)) · (√(Cov_ℍ(s_0, s_0)) + 1)`. -/
theorem abs_covLim_le (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (φ : TestOn upperHalfPlaneOpens) :
    |covLim U s φ| ≤ Real.sqrt (zeroGFFTestCov H φ φ) * covBound s := by
  refine le_of_tendsto ((continuous_abs.tendsto _).comp (tendsto_covLim hU hUH hs φ))
    (Eventually.of_forall fun k => ?_)
  refine (abs_zeroGFFTestCov_le hU hUH _ _).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt (zeroGFFTestCov_self_le_H hU hUH _))
    (sqrt_zeroGFFTestCov_le_covBound hU hUH hs k) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Limit

/-! ### `Γ_U` is a distribution -/

section Dist

variable {U : Set ℂ} {s : ℕ → TestOn upperHalfPlaneOpens}

variable (U s) in
/-- `Γ_U` as a linear map. -/
def covLinMap (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) : TestOn upperHalfPlaneOpens →ₗ[ℝ] ℝ where
  toFun := covLim U s
  map_add' := covLim_add hU hUH hs
  map_smul' c φ := by rw [covLim_smul hU hUH hs, smul_eq_mul, RingHom.id_apply]

/-- **The sup-norm bound of the half-plane variance on a compact support**: for a compact `K ⊆ ℍ` there is `C` with
`Cov_ℍ(φ, φ) ≤ B² C` whenever `|φ| ≤ B` and `tsupport φ ⊆ K`. -/
theorem exists_zeroGFFTestCov_H_le (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (φ : TestOn upperHalfPlaneOpens) (B : ℝ), (∀ x, |φ x| ≤ B) → tsupport φ ⊆ K →
      zeroGFFTestCov H φ φ ≤ B ^ 2 * C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  set R' : ℝ := max R 1 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(Real.pi * R' ^ 2) * (Real.pi * R' ^ 2 * Real.log ((‖(0 : ℂ)‖ + R') / R') + 8 * Real.pi * R' ^ 2),
    fun φ B hB hsupp => ?_⟩
  have h := WangWu.zeroGFFTestCov_self_le_of_ball φ (c := 0) hR'0 hB fun x hx => by
    refine image_eq_zero_of_notMem_tsupport fun hxK => hx ?_
    exact Metric.ball_subset_ball (le_max_left _ _) (hR (hsupp hxK))
  calc zeroGFFTestCov H φ φ = zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ := rfl
    _ ≤ _ := h
    _ = _ := by ring

theorem continuous_covLinMap_comp (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ (upperHalfPlaneOpens : Set ℂ)) :
    Continuous ((covLinMap U s hU hUH hs).comp
      (TestFunction.ofSupportedInCLM ℝ (n := ⊤) (F := ℝ) hK).toLinearMap) := by
  set L := (covLinMap U s hU hUH hs).comp (TestFunction.ofSupportedInCLM ℝ (n := ⊤) (F := ℝ) hK).toLinearMap
    with hLdef
  set ι := ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ (E := ℂ) (F := ℝ) (n := ⊤) (K := K) with hι
  obtain ⟨C, hC⟩ := exists_zeroGFFTestCov_H_le (K : Set ℂ) K.isCompact
  set M : ℝ := Real.sqrt C * covBound s with hM
  have hM0 : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) covBound_pos.le
  have hbound : ∀ f, |L f| ≤ M * ‖ι f‖ := by
    intro f
    set φ : TestOn upperHalfPlaneOpens := TestFunction.ofSupportedIn hK f with hφ
    have hLf : L f = covLim U s φ := rfl
    have hB : ∀ x, |φ x| ≤ ‖ι f‖ := fun x => by
      have := BoundedContinuousFunction.norm_coe_le_norm (ι f) x
      rwa [Real.norm_eq_abs] at this
    have hsupp : tsupport φ ⊆ (K : Set ℂ) := f.tsupport_subset
    have h1 := hC φ ‖ι f‖ hB hsupp
    rw [hLf]
    refine (abs_covLim_le hU hUH hs φ).trans ?_
    calc Real.sqrt (zeroGFFTestCov H φ φ) * covBound s ≤ Real.sqrt (‖ι f‖ ^ 2 * C) * covBound s :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h1) covBound_pos.le
      _ = M * ‖ι f‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), hM]
          ring
  refine continuous_of_tendsto_nhds_zero L ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hιt : Tendsto ι (𝓝 0) (𝓝 0) := by
    have := ι.continuous.tendsto 0
    rwa [map_zero] at this
  filter_upwards [Metric.tendsto_nhds.1 hιt (ε / (M + 1)) (by positivity)] with f hf
  rw [dist_zero_right] at hf
  rw [Real.dist_eq, sub_zero]
  calc |L f| ≤ M * ‖ι f‖ := hbound f
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hf.le hM0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **`Γ_U(φ) = lim_k Cov_U(φ, s_k)` as a distribution on `ℍ`** (for an open `U ⊆ ℍ` and an energy-Cauchy `s`). -/
def covLimDist (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) : DistOn upperHalfPlaneOpens :=
  TestFunction.limitCLM ℝ (covLim U s)
    (fun K hK => ⟨(covLinMap U s hU hUH hs).comp
      (TestFunction.ofSupportedInCLM ℝ (n := ⊤) (F := ℝ) hK).toLinearMap,
      continuous_covLinMap_comp hU hUH hs K hK⟩)
    (fun _ _ _ => rfl)

theorem covLimDist_apply (hU : IsOpen U) (hUH : U ⊆ H) (hs : IsCovCauchy s) (φ : TestOn upperHalfPlaneOpens) :
    covLimDist hU hUH hs φ = covLim U s φ :=
  rfl

end Dist

/-! ### A second-moment bound for conditionally centred Gaussians -/

section Moment

theorem half_sq_add_two_le_exp_add_exp_neg (x : ℝ) : x ^ 2 / 2 + 2 ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · have h1 := Real.quadratic_le_exp_of_nonneg hx
    have h2 := Real.add_one_le_exp (-x)
    linarith
  · have h1 := Real.quadratic_le_exp_of_nonneg (neg_nonneg.2 hx)
    have h2 := Real.add_one_le_exp x
    have e : (-x) ^ 2 = x ^ 2 := by ring
    linarith

variable {Ω : Type*} {𝒢 mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`E[Y²] ≤ 4ε`** for a conditionally centred Gaussian `Y` (conditional characteristic function `e^{−t²V/2}`) whose
conditional variance satisfies `V ≤ ε`. -/
theorem lintegral_sq_le_of_condCharFun [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {ε : ℝ} (hε : 0 < ε) (hVε : ∀ᵐ ω ∂P, V ω ≤ ε) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤ ENNReal.ofReal (4 * ε) := by
  set t : ℝ := 1 / Real.sqrt ε with ht
  have ht2 : t ^ 2 = 1 / ε := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hε.le]
  have hW : Measurable[𝒢] fun _ : Ω => (1 : ℝ≥0∞) := @measurable_const ℝ≥0∞ Ω _ 𝒢 1
  have ep := lintegral_mul_exp_of_condCharFun (P := P) h𝒢 hY hV hV0 hc hW t
  have em := lintegral_mul_exp_of_condCharFun (P := P) h𝒢 hY hV hV0 hc hW (-t)
  simp only [one_mul] at ep em
  -- the right sides are at most `e^{1/2}`
  have hbd : ∫⁻ ω, ENNReal.ofReal (Real.exp (t ^ 2 * V ω / 2)) ∂P ≤ ENNReal.ofReal (Real.exp (1 / 2)) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (t ^ 2 * V ω / 2)) ∂P ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (1 / 2)) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hVε] with ω hω
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          rw [ht2]
          have : 1 / ε * V ω ≤ 1 := by
            rw [one_div, inv_mul_le_iff₀ hε, mul_one]; exact hω
          linarith
      _ = ENNReal.ofReal (Real.exp (1 / 2)) := by rw [lintegral_const, measure_univ, mul_one]
  have hneg : (-t) ^ 2 = t ^ 2 := by ring
  rw [hneg] at em
  -- pointwise: `(tY)²/2 + 2 ≤ e^{tY} + e^{−tY}`
  have hpt : ∀ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) + 2 ≤
      ENNReal.ofReal (Real.exp (t * Y ω)) + ENNReal.ofReal (Real.exp (-t * Y ω)) := fun ω => by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_add (by positivity) (by norm_num),
      ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := half_sq_add_two_le_exp_add_exp_neg (t * Y ω)
    rwa [neg_mul]
  have hmeas : Measurable fun ω => ENNReal.ofReal ((t * Y ω) ^ 2 / 2) := by fun_prop
  have hsum : ∫⁻ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) ∂P + 2 ≤ ENNReal.ofReal (Real.exp (1 / 2)) * 2 := by
    calc ∫⁻ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) ∂P + 2
        = ∫⁻ ω, (ENNReal.ofReal ((t * Y ω) ^ 2 / 2) + 2) ∂P := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (t * Y ω)) + ENNReal.ofReal (Real.exp (-t * Y ω))) ∂P :=
          lintegral_mono hpt
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y ω)) ∂P + ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * Y ω)) ∂P :=
          lintegral_add_left (by fun_prop) _
      _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) + ENNReal.ofReal (Real.exp (1 / 2)) := by
          rw [ep, em]; exact add_le_add hbd hbd
      _ = ENNReal.ofReal (Real.exp (1 / 2)) * 2 := by rw [mul_two]
  -- `e^{1/2} ≤ 2`
  have he : Real.exp (1 / 2) ≤ 2 := by
    rw [← Real.le_log_iff_exp_le (by norm_num)]
    have := Real.log_two_gt_d9
    linarith
  have hsum' : ∫⁻ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) ∂P + 2 ≤ 2 + 2 := by
    refine hsum.trans ?_
    rw [show (2 : ℝ≥0∞) + 2 = ENNReal.ofReal 2 * 2 by
      rw [ENNReal.ofReal_ofNat, ← mul_two]]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal he) _
  have h2 : ∫⁻ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) ∂P ≤ 2 :=
    (ENNReal.add_le_add_iff_right (by norm_num)).1 hsum'
  -- rescale
  have hscale : ∀ ω, ENNReal.ofReal ((t * Y ω) ^ 2 / 2) = ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal (Y ω ^ 2) :=
    fun ω => by
      rw [← ENNReal.ofReal_mul (by positivity), mul_pow, ht2]
      congr 1
      field_simp
  simp_rw [hscale] at h2
  rw [lintegral_const_mul _ (by fun_prop)] at h2
  have hpos : ENNReal.ofReal (1 / (2 * ε)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P
      = (ENNReal.ofReal (1 / (2 * ε)))⁻¹ * (ENNReal.ofReal (1 / (2 * ε)) * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (1 / (2 * ε)))⁻¹ * 2 := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (4 * ε) := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

end Moment

end LocalExt

end InteractingSLE
