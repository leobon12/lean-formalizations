/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65Gauss

/-!
# Aux. lemma 37's flat clock, part 1: two conditioning levels with equal variances

Packet PROVE-FLATCLOCK. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L84–L95, p. 198):
"there is one version of the harmonic mean which is constant […] on every interval on which it remains globally
active and its component is unchanged". At two deterministic times this needs no stopping times: if an observable `X`
is conditionally Gaussian given `𝒢₁ ≤ 𝒢₂`, with means `μ₁`, `μ₂` and variances `V₁`, `V₂`, then almost surely
`V₁ = V₂` forces `μ₁ = μ₂`.

**Proof (exponential tilt).** For real `λ` the conditional moment generating functions
(`LocalSets.lintegral_mul_exp_of_condCharFun`) give `E[e^{λ(X − μ₁) − λ²V₁/2}] = 1` (level 1) and, on the
`𝒢₂`-event `D = {V₁ = V₂, a ≤ λ(μ₂ − μ₁)}`,
`E[1_D e^{λ(μ₂ − μ₁) − λ²V₁/2} e^{λ(X − μ₂)}] = E[1_D e^{λ(μ₂ − μ₁) − λ²V₁/2 + λ²V₂/2}] ≥ e^{a} P(D)` (level 2). The
first integrand dominates the second pointwise, so `e^{a} P(D) ≤ 1` for every `a ≤ λ·(μ₂ − μ₁)` threshold; letting
`λ → ±∞` gives `P(V₁ = V₂, |μ₂ − μ₁| ≥ b) = 0` for every `b > 0`.

* `ofReal_exp_mul_measure_le`: the tilt bound `e^{a} P(V₁ = V₂, a ≤ λ(μ₂ − μ₁)) ≤ 1`;
* **`IsCondGaussian.ae_mean_eq_of_var_eq`**: almost surely `V₁ = V₂ → μ₁ = μ₂`.

No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace InteractingSLE.Sec7.FlatClockProof

open Sec6.Prop65

variable {Ω : Type*} {𝒢₁ 𝒢₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The exponential tilt bound**: for `X` conditionally Gaussian given `𝒢₁ ≤ 𝒢₂` (means `μᵢ`, variances `Vᵢ`) and
reals `λ`, `a`: `e^{a} P(V₁ = V₂, a ≤ λ(μ₂ − μ₁)) ≤ 1`. -/
theorem ofReal_exp_mul_measure_le (h12 : 𝒢₁ ≤ 𝒢₂)
    {X μ₁ μ₂ V₁ V₂ : Ω → ℝ} {K₁ K₂ : ℝ} (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K₁)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K₂) (lam a : ℝ) :
    ENNReal.ofReal (Real.exp a) * P {ω | V₁ ω = V₂ ω ∧ a ≤ lam * (μ₂ ω - μ₁ ω)} ≤ 1 := by
  set D : Set Ω := {ω | V₁ ω = V₂ ω ∧ a ≤ lam * (μ₂ ω - μ₁ ω)} with hD
  have hV₁ : Measurable[𝒢₂] V₁ := h₁.measurable_var.mono h12 le_rfl
  have hμ₁ : Measurable[𝒢₂] μ₁ := h₁.measurable_mean.mono h12 le_rfl
  have hDm : MeasurableSet[𝒢₂] D :=
    (measurableSet_eq_fun hV₁ h₂.measurable_var).inter
      (measurableSet_le measurable_const (measurable_const.mul (h₂.measurable_mean.sub hμ₁)))
  -- level 1: `E[e^{λ(X − μ₁) − λ²V₁/2}] = 1`
  set W₁ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-(lam ^ 2 * V₁ ω / 2))) with hW₁
  have hW₁m : Measurable[𝒢₁] W₁ :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul h₁.measurable_var).div_const 2).neg)
  have e1 := LocalSets.lintegral_mul_exp_of_condCharFun (Y := fun ω => X ω - μ₁ ω) h₁.le
    (h₁.measurable_X.sub h₁.measurable_mean') h₁.measurable_var' (Eventually.of_forall h₁.nonneg)
    h₁.centered hW₁m lam
  have hone : ∫⁻ ω, W₁ ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ₁ ω))) ∂P = 1 := by
    rw [e1]
    have h1 : ∀ ω, W₁ ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2)) = 1 := fun ω => by
      rw [hW₁, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, ENNReal.ofReal_one]
    simp only [h1, lintegral_const, measure_univ, mul_one]
  -- level 2, on `D`
  set W₂ : Ω → ℝ≥0∞ := D.indicator fun ω =>
    ENNReal.ofReal (Real.exp (lam * (μ₂ ω - μ₁ ω) - lam ^ 2 * V₁ ω / 2)) with hW₂
  have hW₂m : Measurable[𝒢₂] W₂ := by
    refine Measurable.indicator ?_ hDm
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.mul (h₂.measurable_mean.sub hμ₁)).sub
        ((measurable_const.mul hV₁).div_const 2)))
  have e2 := LocalSets.lintegral_mul_exp_of_condCharFun (Y := fun ω => X ω - μ₂ ω) h₂.le
    (h₂.measurable_X.sub h₂.measurable_mean') h₂.measurable_var' (Eventually.of_forall h₂.nonneg)
    h₂.centered hW₂m lam
  -- the lower bound `e^{a} P(D)`
  have hlow : ENNReal.ofReal (Real.exp a) * P D ≤
      ∫⁻ ω, W₂ ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ∂P := by
    rw [← lintegral_indicator_const (h₂.le _ hDm)]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ D
    · rw [indicator_of_mem hω, hW₂, indicator_of_mem hω, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have hv : V₁ ω = V₂ ω := hω.1
      have ha : a ≤ lam * (μ₂ ω - μ₁ ω) := hω.2
      rw [hv]
      linarith
    · rw [indicator_of_notMem hω]
      exact bot_le
  -- the pointwise comparison of the two tilted integrands
  have hup : ∫⁻ ω, W₂ ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ₂ ω))) ∂P ≤
      ∫⁻ ω, W₁ ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ₁ ω))) ∂P := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ D
    · rw [hW₂, indicator_of_mem hω, hW₁, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add]
      refine le_of_eq (congrArg ENNReal.ofReal (congrArg Real.exp ?_))
      ring
    · rw [hW₂, indicator_of_notMem hω, zero_mul]
      exact bot_le
  calc ENNReal.ofReal (Real.exp a) * P D
      ≤ ∫⁻ ω, W₂ ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ∂P := hlow
    _ = ∫⁻ ω, W₂ ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ₂ ω))) ∂P := e2.symm
    _ ≤ ∫⁻ ω, W₁ ω * ENNReal.ofReal (Real.exp (lam * (X ω - μ₁ ω))) ∂P := hup
    _ = 1 := hone

/-- The event `{V₁ = V₂, b ≤ s(μ₂ − μ₁)}` is null for `b > 0` (let the tilt `λ = y s` grow). -/
theorem measure_var_eq_le_mean_sub_eq_zero (h12 : 𝒢₁ ≤ 𝒢₂)
    {X μ₁ μ₂ V₁ V₂ : Ω → ℝ} {K₁ K₂ : ℝ} (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K₁)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K₂) (s : ℝ) {b : ℝ} (hb : 0 < b) :
    P {ω | V₁ ω = V₂ ω ∧ b ≤ s * (μ₂ ω - μ₁ ω)} = 0 := by
  set D : Set Ω := {ω | V₁ ω = V₂ ω ∧ b ≤ s * (μ₂ ω - μ₁ ω)} with hD
  by_contra hne
  have hfin : P D ≠ ⊤ := measure_ne_top P D
  set p : ℝ := (P D).toReal with hp
  have hp0 : 0 < p := ENNReal.toReal_pos hne hfin
  set y : ℝ := 1 / (b * p) with hy
  have hy0 : 0 < y := by positivity
  have hyb : y * b = 1 / p := by
    rw [hy]; field_simp
  -- the tilt at `λ = y s`, `a = y b`
  have hsub : D ⊆ {ω | V₁ ω = V₂ ω ∧ y * b ≤ (y * s) * (μ₂ ω - μ₁ ω)} := by
    rintro ω ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hy0.le
  have hbound : ENNReal.ofReal (Real.exp (y * b)) * P D ≤ 1 := by
    calc ENNReal.ofReal (Real.exp (y * b)) * P D ≤ ENNReal.ofReal (Real.exp (y * b)) *
          P {ω | V₁ ω = V₂ ω ∧ y * b ≤ (y * s) * (μ₂ ω - μ₁ ω)} := by gcongr
      _ ≤ 1 := ofReal_exp_mul_measure_le h12 h₁ h₂ (y * s) (y * b)
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at hbound
  rw [hyb] at hbound
  have hlt : 1 / p < Real.exp (1 / p) := by
    have := Real.add_one_le_exp (1 / p)
    linarith
  have : 1 < Real.exp (1 / p) * p := by
    have h1 : 1 / p * p = 1 := by field_simp
    calc (1 : ℝ) = 1 / p * p := h1.symm
      _ < Real.exp (1 / p) * p := mul_lt_mul_of_pos_right hlt hp0
  linarith

/-- **Two conditioning levels with equal variances** (the flat clock at two deterministic times): if `X` is
conditionally Gaussian given `𝒢₁ ≤ 𝒢₂`, with means `μ₁`, `μ₂` and variances `V₁`, `V₂`, then almost surely
`V₁ = V₂ → μ₁ = μ₂`. -/
theorem IsCondGaussian.ae_mean_eq_of_var_eq (h12 : 𝒢₁ ≤ 𝒢₂)
    {X μ₁ μ₂ V₁ V₂ : Ω → ℝ} {K₁ K₂ : ℝ} (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K₁)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K₂) :
    ∀ᵐ ω ∂P, V₁ ω = V₂ ω → μ₁ ω = μ₂ ω := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ n : ℕ, ({ω | V₁ ω = V₂ ω ∧ 1 / ((n : ℝ) + 1) ≤ 1 * (μ₂ ω - μ₁ ω)} ∪
      {ω | V₁ ω = V₂ ω ∧ 1 / ((n : ℝ) + 1) ≤ -1 * (μ₂ ω - μ₁ ω)})) ?_
    (measure_iUnion_null fun n => measure_union_null
      (measure_var_eq_le_mean_sub_eq_zero h12 h₁ h₂ 1 Nat.one_div_pos_of_nat)
      (measure_var_eq_le_mean_sub_eq_zero h12 h₁ h₂ (-1) Nat.one_div_pos_of_nat))
  intro ω hω
  simp only [mem_ofPred_eq, Classical.not_imp] at hω
  obtain ⟨hV, hμ⟩ := hω
  have hd : 0 < |μ₂ ω - μ₁ ω| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hμ))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
  simp only [mem_iUnion, mem_union, mem_ofPred_eq]
  refine ⟨n, ?_⟩
  rcases le_total 0 (μ₂ ω - μ₁ ω) with hpos | hneg
  · left
    rw [abs_of_nonneg hpos] at hn
    exact ⟨hV, by linarith⟩
  · right
    rw [abs_of_nonpos hneg] at hn
    exact ⟨hV, by linarith⟩

end InteractingSLE.Sec7.FlatClockProof
