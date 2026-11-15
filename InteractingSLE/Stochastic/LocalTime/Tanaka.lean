/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.Occupation

/-!
# Tanaka's formula for a nonnegative process: zero right local time kills the singular push

Packet PROVE-TANAKA. Let `X ≥ 0` satisfy `IsTanakaPath` on `[s, ρ]`:
`X = X_s + a (B - B_s) + ∫ b + c (J - J_s)` with `J` nondecreasing and carried by `{X = 0}`. If
`a ≠ 0`, `c ≠ 0` and `∫_s^ρ X_r⁻¹ dr ≤ N` (the reciprocal integrability; Lean's `0⁻¹ = 0` sets the
integrand to zero on the zero set), then `J_ρ = J_s` almost surely
(`ae_singular_eq_of_isTanakaPath`).

This is the argument of the specification's proof of Theorem 2.4 (p. 37), of the paragraph on
geometric force endpoints after Lemma 2.5 (p. 39), and of Aux. lemma 117 (p. 382): the reciprocal
integrability gives zero right local time at `0` (`(1/ε) ∫ 1{0 < X < ε} d⟨X⟩ ≤ a² ∫ 1{0<X<ε}/X → 0`,
[RY] Ch. VI, Cor. (1.9), p. 227), and Tanaka's formula ([RY] Ch. VI, Thm (1.2) and (1.7),
pp. 222–225; [KS] 3.6.A, p. 203) then gives `∫ 1{X = 0} dX = 0`, i.e. `c (J_ρ - J_s) = 0`.

Proof, in expectations: the identity of `integral_sub_eq_of_isTanakaPath` for `f(x) = x` and for
`f = tanakaFn ε` (with `f'(0) = 0`, `f'' = bump ε ≤ K / x` on `(0, ε)`) gives
`E[∫(1 - f'(X)) b + c (J_ρ - J_s)] = E[(X - f(X))_ρ - (X - f(X))_s] + a²/2 E ∫ bump ε (X)`.
As `ε → 0` the right side tends to `0` (`|x - f(x)| ≤ ε` on `x ≥ 0`, dominated convergence with the
bound `K / X`), and the left side tends to `c E[J_ρ - J_s]` because the zero set of `X` is
Lebesgue-null (`ae_volume_zeroSet_eq_zero`). Since `J_ρ - J_s ≥ 0`, it vanishes almost surely.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology ENNReal

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ}
  {B X J b : ℝ≥0 → Ω → ℝ}

/-- The Tanaka approximation scale `ε_m = 1 / (m + 1)`. -/
def tanakaScale (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

lemma tanakaScale_pos (m : ℕ) : 0 < tanakaScale m := by unfold tanakaScale; positivity

lemma tendsto_tanakaScale : Tendsto tanakaScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma eventually_tanakaScale_le {x : ℝ} (hx : 0 < x) : ∀ᶠ m in atTop, tanakaScale m ≤ x :=
  tendsto_tanakaScale.eventually (ge_mem_nhds hx)

/-- `bump ε x ≤ K x⁻¹` for `x ≥ 0`. -/
lemma bump_le_inv {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) : bump ε x ≤ bumpConst * x⁻¹ := by
  rcases hx.lt_or_eq with hx | rfl
  · rcases lt_or_ge x ε with h | h
    · calc bump ε x ≤ bumpConst / ε := bump_le hε x
        _ ≤ bumpConst / x := by
            gcongr
            · exact div_nonneg (by norm_num) tentMass_pos.le
        _ = bumpConst * x⁻¹ := div_eq_mul_inv _ _
    · rw [bump_eq_zero hε (Or.inr h)]
      exact mul_nonneg (div_nonneg (by norm_num) tentMass_pos.le) (inv_nonneg.2 hx.le)
  · rw [bump_eq_zero hε (Or.inl le_rfl), inv_zero, mul_zero]

/-- Pathwise: `∫_s^ρ bump ε_m (X) → 0`. -/
lemma tendsto_integral_bump {x : ℝ≥0 → ℝ} {s ρ : ℝ≥0} (hsρ : s ≤ ρ)
    (hx : ContinuousOn x (Icc s ρ)) (hnn : ∀ u ∈ Icc s ρ, 0 ≤ x u)
    (hrec : IntervalIntegrable (fun r : ℝ => (x r.toNNReal)⁻¹) volume s ρ) :
    Tendsto (fun m => ∫ r in (s : ℝ)..ρ, bump (tanakaScale m) (x r.toNNReal)) atTop (𝓝 0) := by
  have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
  have hx' := continuousOn_comp_toNNReal hx
  have h0 : (0 : ℝ) = ∫ r in (s : ℝ)..ρ, (0 : ℝ) := by simp
  rw [h0]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun r => bumpConst * (x r.toNNReal)⁻¹) (Eventually.of_forall fun m => ?_)
    (Eventually.of_forall fun m => Eventually.of_forall fun r hr => ?_) (hrec.const_mul _)
    (Eventually.of_forall fun r hr => ?_)
  · rw [uIoc_of_le hsρ']
    exact (((continuous_bump _).comp_continuousOn hx').mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · rw [uIoc_of_le hsρ'] at hr
    have hxr := hnn _ (toNNReal_mem_Icc hr)
    rw [Real.norm_eq_abs, abs_of_nonneg (bump_nonneg (tanakaScale_pos m) _)]
    exact bump_le_inv (tanakaScale_pos m) hxr
  · rw [uIoc_of_le hsρ'] at hr
    have hxr := hnn _ (toNNReal_mem_Icc hr)
    rcases hxr.lt_or_eq with hpos | hzero
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_tanakaScale_le hpos] with m hm
      exact (bump_eq_zero (tanakaScale_pos m) (Or.inr hm)).symm
    · refine tendsto_const_nhds.congr fun m => ?_
      rw [← hzero, bump_eq_zero (tanakaScale_pos m) (Or.inl le_rfl)]

/-- Pathwise: `∫_s^ρ tanakaFn' ε_m (X) b → ∫_s^ρ b` when `X ≥ 0` and `{X = 0}` is null. -/
lemma tendsto_integral_tanakaFn'_mul {x : ℝ≥0 → ℝ} {s ρ : ℝ≥0} {b : ℝ → ℝ} (hsρ : s ≤ ρ)
    (hx : ContinuousOn x (Icc s ρ)) (hnn : ∀ u ∈ Icc s ρ, 0 ≤ x u)
    (hb : IntervalIntegrable b volume s ρ) (hZ : volume (zeroSet x s ρ) = 0) :
    Tendsto (fun m => ∫ r in (s : ℝ)..ρ, tanakaFn' (tanakaScale m) (x r.toNNReal) * b r) atTop
      (𝓝 (∫ r in (s : ℝ)..ρ, 1 * b r)) := by
  have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
  have hx' := continuousOn_comp_toNNReal hx
  have hZ' := measure_eq_zero_iff_ae_notMem.1 hZ
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun r => |b r|) (Eventually.of_forall fun m => ?_)
    (Eventually.of_forall fun m => Eventually.of_forall fun r _ => ?_) hb.abs ?_
  · have := hb.continuousOn_mul (g := fun r => tanakaFn' (tanakaScale m) (x r.toNNReal))
      (((continuous_tanakaFn' _).comp_continuousOn hx').mono (by rw [uIcc_of_le hsρ']))
    exact this.1.aestronglyMeasurable.mono_measure (by rw [uIoc_of_le hsρ'])
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_tanakaFn'_le (tanakaScale_pos m) _)
  · filter_upwards [hZ'] with r hrZ hr
    rw [uIoc_of_le hsρ'] at hr
    have hxr := hnn _ (toNNReal_mem_Icc hr)
    have hne : x r.toNNReal ≠ 0 := fun h => hrZ ⟨Ioc_subset_Icc_self hr, h⟩
    have hpos : 0 < x r.toNNReal := lt_of_le_of_ne hxr (Ne.symm hne)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_tanakaScale_le hpos] with m hm
    rw [tanakaFn'_of_ge (tanakaScale_pos m) hm]

/-! ### The Tanaka argument -/

section TanakaArgument

variable (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t) (hX : ∀ u, Measurable[𝓕 u] (X u))
  (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (h𝒢a : Antitone 𝒢)
  (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
include hB hst hX h𝒢 h𝒢a hpath

/-- The identity for `f(x) = x`: `E[X_ρ - X_s] = E[∫_s^ρ b + c (J_ρ - J_s)]`. -/
lemma integral_sub_eq_id :
    ∫ ω, (X (lifetime 𝒢 s t ω) ω - X s ω) ∂μ =
      ∫ ω, ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
        c * (J (lifetime 𝒢 s t ω) ω - J s ω)) ∂μ := by
  have := integral_sub_eq_of_isTanakaPath (f := fun x => x) (f' := fun _ => 1)
    (f'' := fun _ => 0) hB hst hX h𝒢 h𝒢a (fun x => hasDerivAt_id' x)
    (fun x => hasDerivAt_const x (1 : ℝ)) continuous_const hpath
  simpa using this

/-- The identity for `f = tanakaFn ε` (with `f'(0) = 0`). -/
lemma integral_sub_eq_tanaka (m : ℕ) :
    ∫ ω, (tanakaFn (tanakaScale m) (X (lifetime 𝒢 s t ω) ω) -
      tanakaFn (tanakaScale m) (X s ω)) ∂μ =
      ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω) ∂μ +
      a ^ 2 / 2 * ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        bump (tanakaScale m) (X r.toNNReal ω)) ∂μ := by
  have := integral_sub_eq_of_isTanakaPath (f := tanakaFn (tanakaScale m))
    (f' := tanakaFn' (tanakaScale m)) (f'' := bump (tanakaScale m)) hB hst hX h𝒢 h𝒢a
    (hasDerivAt_tanakaFn _) (hasDerivAt_tanakaFn' _) (continuous_bump _) hpath
  simpa [tanakaFn'_zero] using this

lemma integrable_aid :
    Integrable (fun ω => (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
      c * (J (lifetime 𝒢 s t ω) ω - J s ω)) μ := by
  simpa using integrable_limitA (f' := fun _ => 1) hB hst hX h𝒢 h𝒢a continuous_const hpath

lemma integrable_af (m : ℕ) :
    Integrable (fun ω => ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω) μ := by
  simpa [tanakaFn'_zero] using
    integrable_limitA hB hst hX h𝒢 h𝒢a (continuous_tanakaFn' (tanakaScale m)) hpath

omit hB in
lemma integrable_tanakaS (m : ℕ) :
    Integrable (fun ω => tanakaFn (tanakaScale m) (X (lifetime 𝒢 s t ω) ω) -
      tanakaFn (tanakaScale m) (X s ω)) μ :=
  integrable_limitS hst hX h𝒢 h𝒢a (continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_tanakaFn _ x).continuousAt) hpath

omit hB in
lemma integrable_idS :
    Integrable (fun ω => X (lifetime 𝒢 s t ω) ω - X s ω) μ :=
  integrable_limitS (f := fun x => x) hst hX h𝒢 h𝒢a continuous_id hpath

/-- `E[(∫ b + c ΔJ) - ∫ f'(X) b] = E[(X - f(X))_ρ - (X - f(X))_s] + a²/2 E ∫ bump ε (X)`. -/
lemma integral_aid_sub_af (m : ℕ) :
    ∫ ω, (((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
      c * (J (lifetime 𝒢 s t ω) ω - J s ω)) - ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω) ∂μ =
      ∫ ω, ((X (lifetime 𝒢 s t ω) ω - X s ω) -
        (tanakaFn (tanakaScale m) (X (lifetime 𝒢 s t ω) ω) -
          tanakaFn (tanakaScale m) (X s ω))) ∂μ +
      a ^ 2 / 2 * ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        bump (tanakaScale m) (X r.toNNReal ω)) ∂μ := by
  rw [integral_sub (integrable_aid hB hst hX h𝒢 h𝒢a hpath)
      (integrable_af hB hst hX h𝒢 h𝒢a hpath m),
    integral_sub (integrable_idS hst hX h𝒢 h𝒢a hpath) (integrable_tanakaS hst hX h𝒢 h𝒢a hpath m),
    ← integral_sub_eq_id hB hst hX h𝒢 h𝒢a hpath,
    integral_sub_eq_tanaka hB hst hX h𝒢 h𝒢a hpath m]
  ring

end TanakaArgument

/-! ### The limits -/

section TanakaLimits

lemma tendsto_integral_id_sub_tanaka
    (hnn : ∀ᵐ ω ∂μ, ∀ u ∈ Icc s (lifetime 𝒢 s t ω), 0 ≤ X u ω) :
    Tendsto (fun m => ∫ ω, ((X (lifetime 𝒢 s t ω) ω - X s ω) -
      (tanakaFn (tanakaScale m) (X (lifetime 𝒢 s t ω) ω) -
        tanakaFn (tanakaScale m) (X s ω))) ∂μ) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun m => 2 * tanakaScale m) (fun m => ?_) ?_
  · refine (norm_integral_le_of_norm_le (integrable_const (2 * tanakaScale m)) ?_).trans
      (by simp)
    filter_upwards [hnn] with ω hω
    have h1 := tanakaFn_bounds (tanakaScale_pos m)
      (hω (lifetime 𝒢 s t ω) ⟨le_lifetimeOf _ _ _, le_rfl⟩)
    have h2 := tanakaFn_bounds (tanakaScale_pos m)
      (hω s ⟨le_rfl, le_lifetimeOf (fun u => ω ∈ 𝒢 u) s t⟩)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · simpa using tendsto_tanakaScale.const_mul 2

/-- Pathwise bound `∫_s^ρ bump ε (X) ≤ K ∫_s^ρ X⁻¹`. -/
lemma integral_bump_le {x : ℝ≥0 → ℝ} {ρ : ℝ≥0} (hsρ : s ≤ ρ) (hx : ContinuousOn x (Icc s ρ))
    (hnn : ∀ u ∈ Icc s ρ, 0 ≤ x u)
    (hrec : IntervalIntegrable (fun r : ℝ => (x r.toNNReal)⁻¹) volume s ρ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ r in (s : ℝ)..ρ, bump ε (x r.toNNReal) ≤
      bumpConst * ∫ r in (s : ℝ)..ρ, (x r.toNNReal)⁻¹ := by
  have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hsρ' ?_ (hrec.const_mul _) fun r hr => ?_
  · exact ((continuous_bump _).comp_continuousOn
      (continuousOn_comp_toNNReal hx)).intervalIntegrable_of_Icc hsρ'
  · have hmem : r.toNNReal ∈ Icc s ρ :=
      ⟨Real.le_toNNReal_iff_coe_le (s.2.trans hr.1) |>.2 hr.1,
        (Real.toNNReal_le_iff_le_coe).2 hr.2⟩
    exact bump_le_inv hε (hnn _ hmem)

lemma tendsto_integral_bumpX (hst : s ≤ t) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (h𝒢a : Antitone 𝒢)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hnn : ∀ᵐ ω ∂μ, ∀ u ∈ Icc s (lifetime 𝒢 s t ω), 0 ≤ X u ω)
    (hrec : ∀ᵐ ω ∂μ,
      IntervalIntegrable (fun r : ℝ => (X r.toNNReal ω)⁻¹) volume s (lifetime 𝒢 s t ω) ∧
      ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), (X r.toNNReal ω)⁻¹ ≤ N) :
    Tendsto (fun m => ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      bump (tanakaScale m) (X r.toNNReal ω)) ∂μ) atTop (𝓝 0) := by
  have hK : 0 ≤ bumpConst := div_nonneg (by norm_num) tentMass_pos.le
  have h0 : (0 : ℝ) = ∫ _ : Ω, (0 : ℝ) ∂μ := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun _ => bumpConst * N)
    (F := fun m ω => ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), bump (tanakaScale m) (X r.toNNReal ω))
    (f := fun _ => 0)
    (fun m => (integrable_limitT hst hX h𝒢 h𝒢a (continuous_bump (tanakaScale m))
      hpath).aestronglyMeasurable)
    (integrable_const _) (fun m => ?_) ?_
  · filter_upwards [hpath, hnn, hrec] with ω hP hω hr
    have hsρ : (s : ℝ) ≤ lifetime 𝒢 s t ω := by exact_mod_cast le_lifetimeOf _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (intervalIntegral.integral_nonneg hsρ fun r _ => bump_nonneg (tanakaScale_pos m) _)]
    exact (integral_bump_le (x := fun u => X u ω) (ρ := lifetime 𝒢 s t ω) (le_lifetimeOf _ _ _)
      hP.1 hω hr.1
      (tanakaScale_pos m)).trans
      (mul_le_mul_of_nonneg_left hr.2 hK)
  · filter_upwards [hpath, hnn, hrec] with ω hP hω hr
    exact tendsto_integral_bump (x := fun u => X u ω) (ρ := lifetime 𝒢 s t ω)
      (le_lifetimeOf _ _ _) hP.1 hω hr.1

omit [IsProbabilityMeasure μ] in
lemma ae_tendsto_aid_sub_af
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hnn : ∀ᵐ ω ∂μ, ∀ u ∈ Icc s (lifetime 𝒢 s t ω), 0 ≤ X u ω)
    (hZ : ∀ᵐ ω ∂μ, volume (zeroSet (X · ω) s (lifetime 𝒢 s t ω)) = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun m => ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
      c * (J (lifetime 𝒢 s t ω) ω - J s ω)) - ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω) atTop
      (𝓝 (c * (J (lifetime 𝒢 s t ω) ω - J s ω))) := by
  filter_upwards [hpath, hnn, hZ] with ω hP hω hz
  have h := tendsto_integral_tanakaFn'_mul (x := fun u => X u ω) (ρ := lifetime 𝒢 s t ω)
    (le_lifetimeOf _ _ _) hP.1 hω
    hP.2.2.2.1 hz
  simp only [one_mul] at h
  have := (tendsto_const_nhds (x := (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
      c * (J (lifetime 𝒢 s t ω) ω - J s ω))).sub h
  rwa [add_sub_cancel_left] at this

omit [IsProbabilityMeasure μ] in
lemma ae_abs_aid_sub_af_le
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (m : ℕ) :
    ∀ᵐ ω ∂μ, |((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
      c * (J (lifetime 𝒢 s t ω) ω - J s ω)) - ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
        tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω| ≤ 2 * N + |c| * N := by
  filter_upwards [hpath] with ω hP
  have hsρ : (s : ℝ) ≤ lifetime 𝒢 s t ω := by exact_mod_cast le_lifetimeOf _ _ _
  have hb := hP.2.2.2.1
  have hbN := hP.2.2.2.2.2.2.2.2.1
  have hJ0 : 0 ≤ J (lifetime 𝒢 s t ω) ω - J s ω :=
    sub_nonneg.2 (hP.2.2.2.2.2.1 ⟨le_rfl, le_lifetimeOf _ _ _⟩
      ⟨le_lifetimeOf _ _ _, le_rfl⟩ (le_lifetimeOf _ _ _))
  have hJN : J (lifetime 𝒢 s t ω) ω - J s ω ≤ N := hP.2.2.2.2.2.2.2.2.2
  have hI1 : |∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω| ≤ N :=
    (intervalIntegral.abs_integral_le_integral_abs hsρ).trans hbN
  have hI2 : |∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω| ≤ N := by
    refine (intervalIntegral.abs_integral_le_integral_abs hsρ).trans
      ((intervalIntegral.integral_mono_on hsρ ?_ hb.abs fun r _ => ?_).trans hbN)
    · exact (hb.continuousOn_mul ((continuous_tanakaFn' _).comp_continuousOn
        (continuousOn_comp_toNNReal hP.1) |>.mono (by rw [uIcc_of_le hsρ]))).abs
    · rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_tanakaFn'_le (tanakaScale_pos m) _)
  have hcJ : |c * (J (lifetime 𝒢 s t ω) ω - J s ω)| ≤ |c| * N := by
    rw [abs_mul, abs_of_nonneg hJ0]; exact mul_le_mul_of_nonneg_left hJN (abs_nonneg c)
  calc _ ≤ |(∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
        c * (J (lifetime 𝒢 s t ω) ω - J s ω)| + |∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
          tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω| := abs_sub _ _
    _ ≤ (N + |c| * N) + N := add_le_add ((abs_add_le _ _).trans (add_le_add hI1 hcJ)) hI2
    _ = 2 * N + |c| * N := by ring

end TanakaLimits

/-- **Zero right local time kills the singular push** (localized). If `X ≥ 0` on `[s, ρ]`,
`a ≠ 0`, `c ≠ 0` and `∫_s^ρ X⁻¹ ≤ N` (almost surely), then `J_ρ = J_s` almost surely. -/
theorem ae_singular_eq_of_isTanakaPath (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢) (ha : a ≠ 0) (hc : c ≠ 0)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hnn : ∀ᵐ ω ∂μ, ∀ u ∈ Icc s (lifetime 𝒢 s t ω), 0 ≤ X u ω)
    (hrec : ∀ᵐ ω ∂μ,
      IntervalIntegrable (fun r : ℝ => (X r.toNNReal ω)⁻¹) volume s (lifetime 𝒢 s t ω) ∧
      ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), (X r.toNNReal ω)⁻¹ ≤ N) :
    ∀ᵐ ω ∂μ, J (lifetime 𝒢 s t ω) ω = J s ω := by
  have hZ := ae_volume_zeroSet_eq_zero hB hst hX h𝒢 h𝒢a ha hpath
  have hΘm : ∀ m : ℕ, AEStronglyMeasurable (fun ω =>
      ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), b r.toNNReal ω) +
        c * (J (lifetime 𝒢 s t ω) ω - J s ω)) - ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
          tanakaFn' (tanakaScale m) (X r.toNNReal ω) * b r.toNNReal ω) μ := fun m =>
    ((integrable_aid hB hst hX h𝒢 h𝒢a hpath).sub
      (integrable_af hB hst hX h𝒢 h𝒢a hpath m)).aestronglyMeasurable
  have hlim := ae_tendsto_aid_sub_af hpath hnn hZ
  have hLHS := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => 2 * N + |c| * N) hΘm (integrable_const _)
    (fun m => (ae_abs_aid_sub_af_le hpath m).mono fun ω h => by rwa [Real.norm_eq_abs]) hlim
  have hRHS := (tendsto_integral_id_sub_tanaka hnn).add
    ((tendsto_integral_bumpX hst hX h𝒢 h𝒢a hpath hnn hrec).const_mul (a ^ 2 / 2))
  rw [mul_zero, add_zero] at hRHS
  have hzero : ∫ ω, c * (J (lifetime 𝒢 s t ω) ω - J s ω) ∂μ = 0 :=
    tendsto_nhds_unique hLHS (hRHS.congr fun m =>
      (integral_aid_sub_af hB hst hX h𝒢 h𝒢a hpath m).symm)
  have hΔJ0 : 0 ≤ᵐ[μ] fun ω => J (lifetime 𝒢 s t ω) ω - J s ω := by
    filter_upwards [hpath] with ω hP
    exact sub_nonneg.2 (hP.2.2.2.2.2.1 ⟨le_rfl, le_lifetimeOf _ _ _⟩
      ⟨le_lifetimeOf _ _ _, le_rfl⟩ (le_lifetimeOf _ _ _))
  have hcΔJ : Integrable (fun ω => c * (J (lifetime 𝒢 s t ω) ω - J s ω)) μ := by
    refine (integrable_const (|c| * N)).mono'
      (aestronglyMeasurable_of_tendsto_ae atTop hΘm hlim) ?_
    filter_upwards [hpath, hΔJ0] with ω hP h0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left hP.2.2.2.2.2.2.2.2.2 (abs_nonneg c)
  have hΔJi : Integrable (fun ω => J (lifetime 𝒢 s t ω) ω - J s ω) μ := by
    refine (hcΔJ.const_mul c⁻¹).congr (Eventually.of_forall fun ω => ?_)
    simp only
    field_simp
  have hint0 : ∫ ω, (J (lifetime 𝒢 s t ω) ω - J s ω) ∂μ = 0 := by
    rw [integral_const_mul] at hzero
    exact (mul_eq_zero.1 hzero).resolve_left hc
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hΔJ0 hΔJi).1 hint0] with ω hω
  simp only [Pi.zero_apply] at hω
  linarith

end InteractingSLE.LocalTime
