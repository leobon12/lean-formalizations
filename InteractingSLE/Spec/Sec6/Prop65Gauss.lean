/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.SubdomainMGF
import MathFin.Probability.Gaussian.GaussianMoments

/-!
# Proposition 6.5, part 1: conditional Gaussian moments and stopped conditional expectations

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–160).

The proof of Proposition 6.5 uses, at stopping times `S ≤ T`, the conditional Gaussian law of a fixed
observable `X` (a normalized radial bump pairing of the field): `ℒ(X | 𝓕_T) = N(M_T, v_T)`. This file
collects the probabilistic identities that the proof extracts from such a law:

* `condExp_pow_eq_of_condCharFun`: if `E[e^{itY} | 𝒢] = e^{−t² V/2}` with `0 ≤ V ≤ K` `𝒢`-measurable, then
  `Y^k` is integrable and `E[Y^k | 𝒢] = V^{k/2} m_k` (`m_k` the standard Gaussian moments; `m_1 = m_3 = 0`,
  `m_2 = 1`, `m_4 = 3`);
* `condExp_condExp_stoppingTime`: `E[E[W | 𝓕_τ] | 𝓕_σ] = E[W | 𝓕_{σ∧τ}]` for stopping times of a
  filtration indexed by `ℝ≥0` (no right-continuity);
* `exists_measurable_ae_eq_of_condCharFun`: the conditional mean in a conditional characteristic function
  identity is almost surely equal to a `𝒢`-measurable function (it need not be measurable a priori).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology

namespace InteractingSLE.Sec6.Prop65

/-! ### Standard Gaussian moments -/

/-- The `k`-th moment of the standard Gaussian law. -/
def gmom (k : ℕ) : ℝ := ∫ z, z ^ k ∂(gaussianReal 0 1)

lemma gmom_one : gmom 1 = 0 := by
  simp only [gmom, pow_one]
  exact integral_id_gaussianReal

lemma gmom_two : gmom 2 = 1 := by
  rw [gmom, MathFin.integral_sq_gaussianReal]
  simp

lemma gmom_three : gmom 3 = 0 := MathFin.integral_pow3_gaussianReal 1

lemma gmom_four : gmom 4 = 3 := by
  rw [gmom, MathFin.integral_pow4_gaussianReal]
  simp

lemma integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun z : ℝ => z ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : ℝ≥0)).integrable_norm_pow'
  refine (h.congr' ?_ ?_)
  · exact (measurable_id.pow_const k).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by simp [Real.norm_eq_abs]

/-! ### Conditional moments from a conditional characteristic function -/

section CondMoments

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The product integrand `(√V(ω) z)^k` of the mixture law is integrable when `V` is bounded. -/
lemma integrable_mixMap_pow {V : Ω → ℝ} (hV : Measurable V) {K : ℝ} (hVK : ∀ ω, V ω ≤ K)
    (B : Set Ω) (k : ℕ) :
    Integrable (fun p : Ω × ℝ => (Real.sqrt (V p.1) * p.2) ^ k)
      ((P.restrict B).prod (gaussianReal 0 1)) := by
  have hg : Integrable (fun p : Ω × ℝ => Real.sqrt K ^ k * |p.2 ^ k|)
      ((P.restrict B).prod (gaussianReal 0 1)) :=
    ((integrable_pow_gaussianReal k).abs.comp_snd (μ := P.restrict B)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact ((LocalSets.measurable_mixMap hV).pow_const k).aestronglyMeasurable
  · rw [Real.norm_eq_abs, mul_pow, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    exact hVK p.1

/-- **Set integrals of powers**: if `E[e^{itY} | 𝒢] = e^{−t² V/2}` with `0 ≤ V ≤ K`, then for `B ∈ 𝒢`,
`∫_B Y^k = ∫_B V^{k/2} m_k`. -/
theorem setIntegral_pow_eq_of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω) {K : ℝ} (hVK : ∀ ω, V ω ≤ K)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {B : Set Ω} (hB : MeasurableSet[𝒢] B) (k : ℕ) :
    ∫ ω in B, Y ω ^ k ∂P = ∫ ω in B, Real.sqrt (V ω) ^ k * gmom k ∂P := by
  have hmix := LocalSets.map_restrict_eq_mixLaw h𝒢 hY hV (ae_of_all _ hV0) hc hB
  have hpm : Measurable fun x : ℝ => x ^ k := measurable_id.pow_const k
  have hint := integrable_mixMap_pow (P := P) hV hVK B k
  calc ∫ ω in B, Y ω ^ k ∂P = ∫ x, x ^ k ∂((P.restrict B).map Y) :=
        (integral_map hY.aemeasurable hpm.aestronglyMeasurable).symm
    _ = ∫ x, x ^ k ∂(LocalSets.mixLaw P B V) := by rw [hmix]
    _ = ∫ p, (Real.sqrt (V p.1) * p.2) ^ k ∂((P.restrict B).prod (gaussianReal 0 1)) :=
        integral_map (LocalSets.measurable_mixMap hV).aemeasurable hpm.aestronglyMeasurable
    _ = ∫ ω in B, ∫ z, (Real.sqrt (V ω) * z) ^ k ∂(gaussianReal 0 1) ∂P := integral_prod _ hint
    _ = ∫ ω in B, Real.sqrt (V ω) ^ k * gmom k ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [mul_pow]
        rw [integral_const_mul]
        rfl

/-- `Y^k` is integrable under the hypotheses of `setIntegral_pow_eq_of_condCharFun`. -/
theorem integrable_pow_of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω) {K : ℝ} (hVK : ∀ ω, V ω ≤ K)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) (k : ℕ) :
    Integrable (fun ω => Y ω ^ k) P := by
  have hmix := LocalSets.map_restrict_eq_mixLaw h𝒢 hY hV (ae_of_all _ hV0) hc
    (@MeasurableSet.univ _ 𝒢)
  rw [Measure.restrict_univ] at hmix
  have hpm : Measurable fun x : ℝ => x ^ k := measurable_id.pow_const k
  have h1 : Integrable (fun x : ℝ => x ^ k) (LocalSets.mixLaw P univ V) := by
    rw [LocalSets.mixLaw, integrable_map_measure hpm.aestronglyMeasurable
      (LocalSets.measurable_mixMap hV).aemeasurable]
    exact integrable_mixMap_pow (P := P) hV hVK univ k
  rw [← hmix, integrable_map_measure hpm.aestronglyMeasurable hY.aemeasurable] at h1
  exact h1

/-- **Conditional moments of a conditionally centred Gaussian**: `E[Y^k | 𝒢] = V^{k/2} m_k`. -/
theorem condExp_pow_eq_of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable[𝒢] V) (hV0 : ∀ ω, 0 ≤ V ω) {K : ℝ} (hVK : ∀ ω, V ω ≤ K)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) (k : ℕ) :
    P[fun ω => Y ω ^ k | 𝒢] =ᵐ[P] fun ω => Real.sqrt (V ω) ^ k * gmom k := by
  have hVm : Measurable V := hV.mono h𝒢 le_rfl
  have hgm : Measurable[𝒢] fun ω => Real.sqrt (V ω) ^ k * gmom k :=
    (hV.sqrt.pow_const k).mul_const _
  have hgi : Integrable (fun ω => Real.sqrt (V ω) ^ k * gmom k) P := by
    refine Integrable.of_bound ((hgm.mono h𝒢 le_rfl).aestronglyMeasurable)
      (Real.sqrt K ^ k * |gmom k|) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    exact hVK ω
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢
    (integrable_pow_of_condCharFun h𝒢 hY hVm hV0 hVK hc k) (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => (setIntegral_pow_eq_of_condCharFun h𝒢 hY hVm hV0 hVK hc hs k).symm)
    hgm.aestronglyMeasurable).symm

end CondMoments

/-! ### Conditional characteristic functions with a mean -/

section Mean

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

lemma norm_cexp_I_mul_ofReal (x : ℝ) : ‖cexp (I * (x : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- Removing a `𝒢`-measurable mean: if `E[e^{itX} | 𝒢] = e^{itμ} e^{−t²V/2}` with `μ` `𝒢`-measurable,
then `E[e^{it(X−μ)} | 𝒢] = e^{−t²V/2}`. -/
theorem condCharFun_sub_of_condCharFun {X μ V : Ω → ℝ} (hX : Measurable X)
    (hμ : Measurable[𝒢] μ) (h𝒢 : 𝒢 ≤ mΩ) (t : ℝ)
    (hc : P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) :
    P[fun ω => cexp (I * ((t * (X ω - μ ω) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ) := by
  set f : Ω → ℂ := fun ω => cexp (I * ((-(t * μ ω) : ℝ) : ℂ)) with hf
  set g : Ω → ℂ := fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) with hg
  have hfm : StronglyMeasurable[𝒢] f := by
    refine Measurable.stronglyMeasurable ?_
    exact (by fun_prop : Measurable fun x : ℝ => cexp (I * ((-(t * x) : ℝ) : ℂ))).comp hμ
  have hgi : Integrable g P :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => (norm_cexp_I_mul_ofReal _).le)
  have hfgi : Integrable (fun ω => f ω * g ω) P := by
    refine Integrable.of_bound ((hfm.mono h𝒢).aestronglyMeasurable.mul hgi.1) 1
      (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, hf, hg]
    simp only [norm_cexp_I_mul_ofReal, mul_one, le_refl]
  have e : (fun ω => cexp (I * ((t * (X ω - μ ω) : ℝ) : ℂ))) = fun ω => f ω * g ω := by
    funext ω
    rw [hf, hg, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [e]
  have hpull : P[fun ω => f ω * g ω | 𝒢] =ᵐ[P] fun ω => f ω * (P[g | 𝒢]) ω :=
    condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) (m := 𝒢) (μ := P)
      hfm hfgi hgi
  filter_upwards [hpull, hc] with ω h1 h2
  rw [h1, h2, hf, ← mul_assoc, ← Complex.exp_add]
  rw [show I * ((-(t * μ ω) : ℝ) : ℂ) + I * ((t * μ ω : ℝ) : ℂ) = 0 by push_cast; ring,
    Complex.exp_zero, one_mul]

/-- `arg (e^{iθ}) = θ` for `|θ| < π`. -/
lemma arg_cexp_I_mul {θ : ℝ} (hθ : |θ| < Real.pi) : (cexp (I * (θ : ℂ))).arg = θ := by
  rw [mul_comm, Complex.arg_exp_mul_I, toIocMod_eq_self]
  rw [abs_lt] at hθ
  constructor <;> linarith

omit [IsProbabilityMeasure P] in
/-- **The mean is measurable**: if `E[e^{itX} | 𝒢] = e^{itμ} e^{−t²V/2}` for every `t`, with `V`
`𝒢`-measurable and `μ` arbitrary, then `μ` is almost surely equal to a `𝒢`-measurable function. -/
theorem exists_measurable_ae_eq_of_condCharFun {X μ V : Ω → ℝ} (hV : Measurable[𝒢] V)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) :
    ∃ μ' : Ω → ℝ, Measurable[𝒢] μ' ∧ μ' =ᵐ[P] μ := by
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hs
  set F : ℕ → Ω → ℝ := fun n ω => ((n : ℝ) + 1) *
    ((P[fun ω => cexp (I * ((s n * X ω : ℝ) : ℂ)) | 𝒢]) ω *
      ((Real.exp (s n ^ 2 * V ω / 2) : ℝ) : ℂ)).arg with hF
  have hFm : ∀ n, Measurable[𝒢] (F n) := by
    intro n
    refine measurable_const.mul (Complex.measurable_arg.comp ?_)
    exact stronglyMeasurable_condExp.measurable.mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hV.const_mul _).div_const _)))
  refine ⟨fun ω => liminf (fun n => F n ω) atTop, Measurable.liminf hFm, ?_⟩
  filter_upwards [ae_all_iff.2 fun n => hc (s n)] with ω hω
  have hev : (fun n => F n ω) =ᶠ[atTop] fun _ => μ ω := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|μ ω| / Real.pi)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hF]
    simp only
    rw [hω n, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show -(1 / 2) * (s n ^ 2 * V ω) + s n ^ 2 * V ω / 2 = 0 by ring, Real.exp_zero,
      Complex.ofReal_one, mul_one, arg_cexp_I_mul]
    · rw [hs]; field_simp
    · rw [hs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)),
        one_div_mul_eq_div, div_lt_iff₀ hn1]
      have hpi := Real.pi_pos
      have : |μ ω| / Real.pi < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_iff₀ hpi] at this
      linarith
  rw [Filter.liminf_congr hev, liminf_const]

end Mean

/-! ### Conditional expectations at stopping times -/

section Stopping

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- On `{τ ≤ σ}`, an `𝓕_τ`-measurable integrable function is its own conditional expectation given
`𝓕_σ`. -/
theorem condExp_ae_eq_restrict_le_of_stronglyMeasurable {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) {Z : Ω → ℝ}
    (hZm : StronglyMeasurable[hτ.measurableSpace] Z) (hZi : Integrable Z P) :
    P[Z | hσ.measurableSpace] =ᵐ[P.restrict {ω | τ ω ≤ σ ω}] Z := by
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator hZi (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int : Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator Z) P :=
    hZi.indicator (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator Z) P := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact hZm.indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

/-- **Conditional expectations at two stopping times commute**:
`E[E[W | 𝓕_τ] | 𝓕_σ] = E[W | 𝓕_{σ∧τ}]` (no right-continuity of the filtration is needed). -/
theorem condExp_condExp_stoppingTime {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    (hτ : IsStoppingTime 𝓕 τ) (W : Ω → ℝ) :
    P[P[W | hτ.measurableSpace] | hσ.measurableSpace] =ᵐ[P]
      P[W | (hσ.min hτ).measurableSpace] := by
  have hle : (hσ.min hτ).measurableSpace ≤ hτ.measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun ω => min_le_right _ _
  refine ae_of_ae_restrict_of_ae_restrict_compl {ω | σ ω ≤ τ ω} ?_ ?_
  · refine (condExp_min_stopping_time_ae_eq_restrict_le hσ hτ).symm.trans ?_
    exact ae_restrict_of_ae (condExp_condExp_of_le hle hτ.measurableSpace_le)
  · have hsub : {ω | σ ω ≤ τ ω}ᶜ ⊆ {ω | τ ω ≤ σ ω} := fun ω hω => by
      simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
      exact hω.le
    refine ae_restrict_of_ae_restrict_of_subset hsub ?_
    refine (condExp_ae_eq_restrict_le_of_stronglyMeasurable hσ hτ stronglyMeasurable_condExp
      integrable_condExp).trans ?_
    refine (condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).symm.trans ?_
    have e : (hτ.min hσ).measurableSpace = (hσ.min hτ).measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min hσ hτ, IsStoppingTime.measurableSpace_min hτ hσ,
        inf_comm]
    rw [e]

end Stopping

/-! ### Conditionally Gaussian observables -/

section CondGaussian

/-- `X` is conditionally Gaussian given `𝒢`, with `𝒢`-measurable mean `μ` and `𝒢`-measurable variance
`V ∈ [0, K]`: `E[e^{itX} | 𝒢] = e^{itμ} e^{−t²V/2}` for every real `t`. -/
structure IsCondGaussian {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X μ V : Ω → ℝ) (K : ℝ) : Prop where
  le : 𝒢 ≤ mΩ
  measurable_X : Measurable X
  measurable_mean : Measurable[𝒢] μ
  measurable_var : Measurable[𝒢] V
  nonneg : ∀ ω, 0 ≤ V ω
  le_bound : ∀ ω, V ω ≤ K
  charFun : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
    fun ω => cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)

namespace IsCondGaussian

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X μ V : Ω → ℝ} {K : ℝ}

omit [IsProbabilityMeasure P] in
theorem measurable_mean' (h : IsCondGaussian 𝒢 P X μ V K) : Measurable μ :=
  h.measurable_mean.mono h.le le_rfl

omit [IsProbabilityMeasure P] in
theorem measurable_var' (h : IsCondGaussian 𝒢 P X μ V K) : Measurable V :=
  h.measurable_var.mono h.le le_rfl

theorem centered (h : IsCondGaussian 𝒢 P X μ V K) (t : ℝ) :
    P[fun ω => cexp (I * ((t * (X ω - μ ω) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ) :=
  condCharFun_sub_of_condCharFun h.measurable_X h.measurable_mean h.le t (h.charFun t)

theorem integrable_pow (h : IsCondGaussian 𝒢 P X μ V K) (k : ℕ) :
    Integrable (fun ω => (X ω - μ ω) ^ k) P :=
  integrable_pow_of_condCharFun h.le (h.measurable_X.sub h.measurable_mean') h.measurable_var'
    h.nonneg h.le_bound h.centered k

theorem condExp_pow (h : IsCondGaussian 𝒢 P X μ V K) (k : ℕ) :
    P[fun ω => (X ω - μ ω) ^ k | 𝒢] =ᵐ[P] fun ω => Real.sqrt (V ω) ^ k * gmom k :=
  condExp_pow_eq_of_condCharFun h.le (h.measurable_X.sub h.measurable_mean') h.measurable_var
    h.nonneg h.le_bound h.centered k

/-- `∫ W (X − μ)^k = ∫ W V^{k/2} m_k` for `𝒢`-measurable `W` with `W (X − μ)^k` integrable. -/
theorem integral_mul_pow (h : IsCondGaussian 𝒢 P X μ V K) {W : Ω → ℝ} (hW : Measurable[𝒢] W)
    (k : ℕ) (hWi : Integrable (fun ω => W ω * (X ω - μ ω) ^ k) P) :
    ∫ ω, W ω * (X ω - μ ω) ^ k ∂P = ∫ ω, W ω * (Real.sqrt (V ω) ^ k * gmom k) ∂P := by
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒢)
    (μ := P) (f := W) (g := fun ω => (X ω - μ ω) ^ k) hW.stronglyMeasurable hWi (h.integrable_pow k)
  calc ∫ ω, W ω * (X ω - μ ω) ^ k ∂P = ∫ ω, (P[W * fun ω => (X ω - μ ω) ^ k | 𝒢]) ω ∂P :=
        (integral_condExp h.le).symm
    _ = ∫ ω, W ω * (P[fun ω => (X ω - μ ω) ^ k | 𝒢]) ω ∂P := integral_congr_ae hpull
    _ = ∫ ω, W ω * (Real.sqrt (V ω) ^ k * gmom k) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h.condExp_pow k] with ω hω
        rw [hω]

/-- The conditional mean is the mean: `E[X | 𝒢] = μ`. -/
theorem condExp_eq (h : IsCondGaussian 𝒢 P X μ V K) (hXi : Integrable X P) :
    P[X | 𝒢] =ᵐ[P] μ := by
  have hμi : Integrable μ P := by
    have := hXi.sub (h.integrable_pow 1)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  have e : X = μ + fun ω => (X ω - μ ω) ^ 1 := by funext ω; simp
  have h1 := h.condExp_pow 1
  rw [gmom_one] at h1
  calc P[X | 𝒢] = P[μ + fun ω => (X ω - μ ω) ^ 1 | 𝒢] := by rw [← e]
    _ =ᵐ[P] P[μ | 𝒢] + P[fun ω => (X ω - μ ω) ^ 1 | 𝒢] := condExp_add hμi (h.integrable_pow 1) _
    _ =ᵐ[P] μ + 0 := by
        refine EventuallyEq.add ?_ ?_
        · rw [condExp_of_stronglyMeasurable h.le h.measurable_mean.stronglyMeasurable hμi]
        · filter_upwards [h1] with ω hω
          rw [hω]; simp
    _ = μ := add_zero μ

/-- The conditional second moment: `E[X² | 𝒢] = E[X | 𝒢]² + V`. -/
theorem condExp_sq (h : IsCondGaussian 𝒢 P X (P[X | 𝒢]) V K) (hX : MemLp X 2 P) :
    P[fun ω => X ω ^ 2 | 𝒢] =ᵐ[P] fun ω => (P[X | 𝒢]) ω ^ 2 + V ω := by
  set μ := P[X | 𝒢] with hμdef
  have hμ2 : MemLp μ 2 P := hX.condExp one_le_two
  have hY2 : MemLp (fun ω => X ω - μ ω) 2 P := hX.sub hμ2
  have hμμ : Integrable (fun ω => μ ω ^ 2) P := hμ2.integrable_sq
  have hYY : Integrable (fun ω => (X ω - μ ω) ^ 2) P := hY2.integrable_sq
  have hμY : Integrable (fun ω => μ ω * (X ω - μ ω)) P := hμ2.integrable_mul hY2
  have hY1 : Integrable (fun ω => (X ω - μ ω) ^ 1) P := h.integrable_pow 1
  have e : (fun ω => X ω ^ 2) = fun ω => (μ ω ^ 2 + 2 * (μ ω * (X ω - μ ω) ^ 1)) +
      (X ω - μ ω) ^ 2 := by funext ω; ring
  have hμm : StronglyMeasurable[𝒢] μ := stronglyMeasurable_condExp
  have hA : P[fun ω => μ ω ^ 2 | 𝒢] = fun ω => μ ω ^ 2 :=
    condExp_of_stronglyMeasurable h.le ((hμm.measurable.pow_const 2).stronglyMeasurable) hμμ
  have hμY1 : Integrable (fun ω => μ ω * (X ω - μ ω) ^ 1) P :=
    hμY.congr (Eventually.of_forall fun ω => by simp)
  have h1 := h.condExp_pow 1
  rw [gmom_one] at h1
  have hB : P[fun ω => 2 * (μ ω * (X ω - μ ω) ^ 1) | 𝒢] =ᵐ[P] 0 := by
    have hpull : P[fun ω => μ ω * (X ω - μ ω) ^ 1 | 𝒢] =ᵐ[P]
        fun ω => μ ω * (P[fun ω => (X ω - μ ω) ^ 1 | 𝒢]) ω :=
      condExp_mul_of_stronglyMeasurable_left hμm hμY1 hY1
    have hsm : P[fun ω => 2 * (μ ω * (X ω - μ ω) ^ 1) | 𝒢] =ᵐ[P]
        fun ω => 2 * (P[fun ω => μ ω * (X ω - μ ω) ^ 1 | 𝒢]) ω :=
      condExp_smul (2 : ℝ) (fun ω => μ ω * (X ω - μ ω) ^ 1) 𝒢
    filter_upwards [hsm, hpull, h1] with ω a b c
    rw [a, b, c]; simp
  have hC := h.condExp_pow 2
  rw [gmom_two] at hC
  have i1 : Integrable (fun ω => μ ω ^ 2 + 2 * (μ ω * (X ω - μ ω) ^ 1)) P :=
    hμμ.add (hμY1.const_mul 2)
  have hsum1 : P[fun ω => (μ ω ^ 2 + 2 * (μ ω * (X ω - μ ω) ^ 1)) + (X ω - μ ω) ^ 2 | 𝒢] =ᵐ[P]
      fun ω => P[fun ω => μ ω ^ 2 + 2 * (μ ω * (X ω - μ ω) ^ 1) | 𝒢] ω +
        P[fun ω => (X ω - μ ω) ^ 2 | 𝒢] ω :=
    condExp_add i1 (h.integrable_pow 2) 𝒢
  have hsum2 : P[fun ω => μ ω ^ 2 + 2 * (μ ω * (X ω - μ ω) ^ 1) | 𝒢] =ᵐ[P]
      fun ω => P[fun ω => μ ω ^ 2 | 𝒢] ω + P[fun ω => 2 * (μ ω * (X ω - μ ω) ^ 1) | 𝒢] ω :=
    condExp_add hμμ (hμY1.const_mul 2) 𝒢
  rw [e]
  filter_upwards [hsum1, hsum2, hB, hC] with ω a b c d
  rw [a, b, hA, c, d, Real.sq_sqrt (h.nonneg ω)]
  simp

/-- **From a conditional characteristic function with an arbitrary mean**: if
`E[e^{itX} | 𝒢] = e^{itμ} e^{−t²V/2}` for every `t` (`μ` not assumed measurable), then `X` is conditionally
Gaussian with mean `E[X | 𝒢]`, and `E[X | 𝒢] = μ` almost surely. -/
theorem of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) (hX : Measurable X) (hXi : Integrable X P)
    (hV : Measurable[𝒢] V) (hV0 : ∀ ω, 0 ≤ V ω) (hVK : ∀ ω, V ω ≤ K)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) :
    IsCondGaussian 𝒢 P X (P[X | 𝒢]) V K ∧ P[X | 𝒢] =ᵐ[P] μ := by
  obtain ⟨μ', hμ'm, hμ'⟩ := exists_measurable_ae_eq_of_condCharFun hV hc
  have hc' : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * μ' ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ) :=
    fun t => by
      filter_upwards [hc t, hμ'] with ω h1 h2
      rw [h1, h2]
  have g : IsCondGaussian 𝒢 P X μ' V K := ⟨h𝒢, hX, hμ'm, hV, hV0, hVK, hc'⟩
  have hce := g.condExp_eq hXi
  refine ⟨⟨h𝒢, hX, stronglyMeasurable_condExp.measurable, hV, hV0, hVK, fun t => ?_⟩,
    hce.trans hμ'⟩
  filter_upwards [hc' t, hce] with ω h1 h2
  rw [h1, h2]

end IsCondGaussian

/-! ### Two conditioning levels -/

lemma sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

lemma pow_four_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 4 ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h1 := sq_add_three_le a b c
  have h2 := sq_add_three_le (a ^ 2) (b ^ 2) (c ^ 2)
  have h0 : 0 ≤ (a + b + c) ^ 2 := sq_nonneg _
  calc (a + b + c) ^ 4 = ((a + b + c) ^ 2) ^ 2 := by ring
    _ ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 9 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by ring
    _ ≤ 9 * (3 * ((a ^ 2) ^ 2 + (b ^ 2) ^ 2 + (c ^ 2) ^ 2)) := by gcongr
    _ = 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by ring

lemma abs_pow_mul_pow_le {x y R : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) (hR : 1 ≤ R) {a b : ℕ}
    (hab : a + b ≤ 4) : |x ^ a * y ^ b| ≤ R ^ 4 := by
  rw [abs_mul, abs_pow, abs_pow]
  calc |x| ^ a * |y| ^ b ≤ R ^ a * R ^ b := by
        gcongr
    _ = R ^ (a + b) := (pow_add R a b).symm
    _ ≤ R ^ 4 := pow_le_pow_right₀ hR hab

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Integrability from a fourth-power bound in two integrable fourth powers. -/
lemma integrable_of_abs_le_four {Y₁ Y₂ f : Ω → ℝ} (hY₁ : Integrable (fun ω => Y₁ ω ^ 4) P)
    (hY₂ : Integrable (fun ω => Y₂ ω ^ 4) P) [IsFiniteMeasure P] (hf : AEStronglyMeasurable f P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ ω, |f ω| ≤ C * (|Y₁ ω| + |Y₂ ω| + 1) ^ 4) : Integrable f P := by
  have hg : Integrable (fun ω => C * (27 * (Y₁ ω ^ 4 + Y₂ ω ^ 4 + 1))) P :=
    ((hY₁.add hY₂).add (integrable_const 1)).const_mul 27 |>.const_mul C
  refine hg.mono' hf (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (hb ω).trans (mul_le_mul_of_nonneg_left ?_ hC)
  have := pow_four_add_three_le (|Y₁ ω|) (|Y₂ ω|) 1
  simp only [pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y₁ ω ^ 4),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y₂ ω ^ 4), one_pow] at this
  exact this

end CondGaussian

section TwoLevel

variable {Ω : Type*} {𝒢₁ 𝒢₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X μ₁ μ₂ V₁ V₂ : Ω → ℝ} {K : ℝ}

/-- The common integrability bound: every product of at most four factors among `μ₂ − μ₁`,
`X − μ₂` (times a bounded weight) is integrable. -/
lemma integrable_two_level (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K) {W : Ω → ℝ} (hW : Measurable W) {C : ℝ} (hC : 0 ≤ C)
    (hWC : ∀ ω, |W ω| ≤ C) {a b : ℕ} (hab : a + b ≤ 4) :
    Integrable (fun ω => W ω * ((μ₂ ω - μ₁ ω) ^ a * (X ω - μ₂ ω) ^ b)) P := by
  have hm₁ := h₁.measurable_mean'
  have hm₂ := h₂.measurable_mean'
  have hX := h₁.measurable_X
  refine integrable_of_abs_le_four (h₁.integrable_pow 4) (h₂.integrable_pow 4) ?_ hC
    (fun ω => ?_)
  · exact (hW.mul (((hm₂.sub hm₁).pow_const a).mul ((hX.sub hm₂).pow_const b))).aestronglyMeasurable
  · set R := |X ω - μ₁ ω| + |X ω - μ₂ ω| + 1
    have hR : 1 ≤ R := by have := abs_nonneg (X ω - μ₁ ω); have := abs_nonneg (X ω - μ₂ ω); linarith
    have hΔ : |μ₂ ω - μ₁ ω| ≤ R := by
      have : μ₂ ω - μ₁ ω = (X ω - μ₁ ω) - (X ω - μ₂ ω) := by ring
      rw [this]
      have := abs_sub (X ω - μ₁ ω) (X ω - μ₂ ω)
      linarith
    have hY : |X ω - μ₂ ω| ≤ R := by have := abs_nonneg (X ω - μ₁ ω); linarith
    rw [abs_mul]
    exact mul_le_mul (hWC ω) (abs_pow_mul_pow_le hΔ hY hR hab) (abs_nonneg _) hC

/-- **Weighted square increments**: for `𝒢₁ ≤ 𝒢₂` and a bounded `𝒢₁`-measurable `W`,
`∫ W (μ₂ − μ₁)² = ∫ W (V₁ − V₂)`. -/
theorem integral_mul_sq_sub (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K) (h12 : 𝒢₁ ≤ 𝒢₂) {W : Ω → ℝ} (hW : Measurable[𝒢₁] W)
    {C : ℝ} (hC : 0 ≤ C) (hWC : ∀ ω, |W ω| ≤ C) :
    ∫ ω, W ω * (μ₂ ω - μ₁ ω) ^ 2 ∂P = ∫ ω, W ω * (V₁ ω - V₂ ω) ∂P := by
  have hWm : Measurable W := hW.mono h₁.le le_rfl
  have hW₂ : Measurable[𝒢₂] W := hW.mono h12 le_rfl
  have hΔ₂ : Measurable[𝒢₂] fun ω => μ₂ ω - μ₁ ω :=
    h₂.measurable_mean.sub (h₁.measurable_mean.mono h12 le_rfl)
  have hI := fun {a b : ℕ} (hab : a + b ≤ 4) => integrable_two_level h₁ h₂ hWm hC hWC hab
  have hV₁i : Integrable (fun ω => W ω * V₁ ω) P :=
    Integrable.of_bound (hWm.mul h₁.measurable_var').aestronglyMeasurable (C * K)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h₁.nonneg ω)]
        exact mul_le_mul (hWC ω) (h₁.le_bound ω) (h₁.nonneg ω) hC)
  have hV₂i : Integrable (fun ω => W ω * V₂ ω) P :=
    Integrable.of_bound (hWm.mul h₂.measurable_var').aestronglyMeasurable (C * K)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h₂.nonneg ω)]
        exact mul_le_mul (hWC ω) (h₂.le_bound ω) (h₂.nonneg ω) hC)
  -- `∫ W (X − μ₁)² = ∫ W V₁`
  have hA : ∫ ω, W ω * (X ω - μ₁ ω) ^ 2 ∂P = ∫ ω, W ω * V₁ ω ∂P := by
    have hi : Integrable (fun ω => W ω * (X ω - μ₁ ω) ^ 2) P := by
      refine (((hI (a := 2) (b := 0) (by norm_num)).add
        ((hI (a := 1) (b := 1) (by norm_num)).const_mul 2)).add
        (hI (a := 0) (b := 2) (by norm_num))).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]; ring
    rw [h₁.integral_mul_pow hW 2 hi, gmom_two]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [mul_one, Real.sq_sqrt (h₁.nonneg ω)]
  -- expand `X − μ₁ = (μ₂ − μ₁) + (X − μ₂)`
  have hB1 : ∫ ω, (W ω * (μ₂ ω - μ₁ ω)) * (X ω - μ₂ ω) ^ 1 ∂P = 0 := by
    have hm : Measurable[𝒢₂] fun ω => W ω * (μ₂ ω - μ₁ ω) := hW₂.mul hΔ₂
    rw [h₂.integral_mul_pow hm 1
      ((hI (a := 1) (b := 1) (by norm_num)).congr (Eventually.of_forall fun ω => by ring)),
      gmom_one]
    simp
  have hB2 : ∫ ω, W ω * (X ω - μ₂ ω) ^ 2 ∂P = ∫ ω, W ω * V₂ ω ∂P := by
    rw [h₂.integral_mul_pow hW₂ 2
      ((hI (a := 0) (b := 2) (by norm_num)).congr (Eventually.of_forall fun ω => by ring)),
      gmom_two]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [mul_one, Real.sq_sqrt (h₂.nonneg ω)]
  have hexp : ∫ ω, W ω * (X ω - μ₁ ω) ^ 2 ∂P = ∫ ω, W ω * (μ₂ ω - μ₁ ω) ^ 2 ∂P +
      2 * ∫ ω, (W ω * (μ₂ ω - μ₁ ω)) * (X ω - μ₂ ω) ^ 1 ∂P +
      ∫ ω, W ω * (X ω - μ₂ ω) ^ 2 ∂P := by
    have i1 : Integrable (fun ω => W ω * (μ₂ ω - μ₁ ω) ^ 2) P :=
      (hI (a := 2) (b := 0) (by norm_num)).congr (Eventually.of_forall fun ω => by ring)
    have i2 : Integrable (fun ω => (W ω * (μ₂ ω - μ₁ ω)) * (X ω - μ₂ ω) ^ 1) P :=
      (hI (a := 1) (b := 1) (by norm_num)).congr (Eventually.of_forall fun ω => by ring)
    have i3 : Integrable (fun ω => W ω * (X ω - μ₂ ω) ^ 2) P :=
      (hI (a := 0) (b := 2) (by norm_num)).congr (Eventually.of_forall fun ω => by ring)
    have e : (fun ω => W ω * (X ω - μ₁ ω) ^ 2) = fun ω =>
        (W ω * (μ₂ ω - μ₁ ω) ^ 2 + 2 * ((W ω * (μ₂ ω - μ₁ ω)) * (X ω - μ₂ ω) ^ 1)) +
          W ω * (X ω - μ₂ ω) ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω => W ω * (μ₂ ω - μ₁ ω) ^ 2 +
        2 * ((W ω * (μ₂ ω - μ₁ ω)) * (X ω - μ₂ ω) ^ 1)) P := i1.add (i2.const_mul 2)
    rw [e, integral_add i12 i3, integral_add i1 (i2.const_mul 2), integral_const_mul]
  rw [hA, hB1, hB2, mul_zero, add_zero] at hexp
  have hsub : ∫ ω, W ω * (V₁ ω - V₂ ω) ∂P = ∫ ω, W ω * V₁ ω ∂P - ∫ ω, W ω * V₂ ω ∂P := by
    rw [← integral_sub hV₁i hV₂i]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [hsub]
  linarith

/-- **The quartic identity** of the proof of Proposition 6.5:
`E[(μ₂ − μ₁)⁴] = 6 E[(μ₂ − μ₁)² (V₁ − V₂)] − 3 E[(V₁ − V₂)²]`. -/
theorem integral_pow_four_sub (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K) (h12 : 𝒢₁ ≤ 𝒢₂) :
    ∫ ω, (μ₂ ω - μ₁ ω) ^ 4 ∂P = 6 * ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * (V₁ ω - V₂ ω) ∂P -
      3 * ∫ ω, (V₁ ω - V₂ ω) ^ 2 ∂P := by
  have hK : 0 ≤ K := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact (h₁.nonneg ω).trans (h₁.le_bound ω)
  have hI := fun {a b : ℕ} (hab : a + b ≤ 4) =>
    integrable_two_level (W := fun _ => (1 : ℝ)) h₁ h₂ measurable_const zero_le_one
      (fun _ => by simp) hab
  have hIV := fun {a b : ℕ} (hab : a + b ≤ 4) =>
    integrable_two_level (W := V₁) h₁ h₂ h₁.measurable_var' hK
      (fun ω => by rw [abs_of_nonneg (h₁.nonneg ω)]; exact h₁.le_bound ω) hab
  have hIV₂ := fun {a b : ℕ} (hab : a + b ≤ 4) =>
    integrable_two_level (W := V₂) h₁ h₂ h₂.measurable_var' hK
      (fun ω => by rw [abs_of_nonneg (h₂.nonneg ω)]; exact h₂.le_bound ω) hab
  have hΔ₂ : Measurable[𝒢₂] fun ω => μ₂ ω - μ₁ ω :=
    h₂.measurable_mean.sub (h₁.measurable_mean.mono h12 le_rfl)
  have hbV : ∀ (V : Ω → ℝ), Measurable V → (∀ ω, 0 ≤ V ω) → (∀ ω, V ω ≤ K) →
      ∀ (U : Ω → ℝ), Measurable U → (∀ ω, 0 ≤ U ω) → (∀ ω, U ω ≤ K) →
      Integrable (fun ω => V ω * U ω) P := fun V hV hV0 hVK U hU hU0 hUK =>
    Integrable.of_bound (hV.mul hU).aestronglyMeasurable (K * K) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV0 ω), abs_of_nonneg (hU0 ω)]
      exact mul_le_mul (hVK ω) (hUK ω) (hU0 ω) hK)
  have hv11 := hbV V₁ h₁.measurable_var' h₁.nonneg h₁.le_bound V₁ h₁.measurable_var' h₁.nonneg
    h₁.le_bound
  have hv12 := hbV V₁ h₁.measurable_var' h₁.nonneg h₁.le_bound V₂ h₂.measurable_var' h₂.nonneg
    h₂.le_bound
  have hv22 := hbV V₂ h₂.measurable_var' h₂.nonneg h₂.le_bound V₂ h₂.measurable_var' h₂.nonneg
    h₂.le_bound
  -- integrability of the monomials `Δ^a Y₂^b` and their weighted versions
  have j : ∀ a b : ℕ, a + b ≤ 4 → Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ a * (X ω - μ₂ ω) ^ b) P :=
    fun a b hab => (hI hab).congr (Eventually.of_forall fun ω => by simp)
  -- (i) `∫ (X − μ₁)⁴ = 3 ∫ V₁²`
  have e1 : ∫ ω, (X ω - μ₁ ω) ^ 4 ∂P = 3 * ∫ ω, V₁ ω * V₁ ω ∂P := by
    have := h₁.integral_mul_pow (W := fun _ => (1 : ℝ)) measurable_const 4
      ((h₁.integrable_pow 4).congr (Eventually.of_forall fun ω => by simp))
    simp only [one_mul] at this
    rw [this, gmom_four, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have : Real.sqrt (V₁ ω) ^ 4 = V₁ ω * V₁ ω := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (h₁.nonneg ω)]; ring
    simp only [this]; ring
  -- (ii) the conditional moments at level `2`, weighted by powers of `Δ`
  have m : ∀ (a k : ℕ), a + k ≤ 4 → ∫ ω, (μ₂ ω - μ₁ ω) ^ a * (X ω - μ₂ ω) ^ k ∂P =
      ∫ ω, (μ₂ ω - μ₁ ω) ^ a * (Real.sqrt (V₂ ω) ^ k * gmom k) ∂P :=
    fun a k hak => h₂.integral_mul_pow (hΔ₂.pow_const a) k (j a k hak)
  have m1 := m 3 1 (by norm_num)
  have m2 := m 2 2 (by norm_num)
  have m3 := m 1 3 (by norm_num)
  have m4 := m 0 4 (by norm_num)
  rw [gmom_one] at m1
  rw [gmom_three] at m3
  rw [gmom_two] at m2
  rw [gmom_four] at m4
  simp only [mul_zero, integral_zero] at m1 m3
  have m2' : ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * (X ω - μ₂ ω) ^ 2 ∂P = ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * V₂ ω ∂P := by
    rw [m2]; refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [mul_one, Real.sq_sqrt (h₂.nonneg ω)]
  have m4' : ∫ ω, (μ₂ ω - μ₁ ω) ^ 0 * (X ω - μ₂ ω) ^ 4 ∂P = 3 * ∫ ω, V₂ ω * V₂ ω ∂P := by
    rw [m4, ← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have : Real.sqrt (V₂ ω) ^ 4 = V₂ ω * V₂ ω := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (h₂.nonneg ω)]; ring
    simp only [this]; ring
  have e2 : ∫ ω, (X ω - μ₁ ω) ^ 4 ∂P = ∫ ω, (μ₂ ω - μ₁ ω) ^ 4 ∂P +
      4 * ∫ ω, (μ₂ ω - μ₁ ω) ^ 3 * (X ω - μ₂ ω) ^ 1 ∂P +
      6 * ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * (X ω - μ₂ ω) ^ 2 ∂P +
      4 * ∫ ω, (μ₂ ω - μ₁ ω) ^ 1 * (X ω - μ₂ ω) ^ 3 ∂P +
      ∫ ω, (μ₂ ω - μ₁ ω) ^ 0 * (X ω - μ₂ ω) ^ 4 ∂P := by
    have i0 : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 4) P :=
      (j 4 0 (by norm_num)).congr (Eventually.of_forall fun ω => by simp)
    have i1 := (j 3 1 (by norm_num)).const_mul 4
    have i2 := (j 2 2 (by norm_num)).const_mul 6
    have i3 := (j 1 3 (by norm_num)).const_mul 4
    have i4 := j 0 4 (by norm_num)
    have e : (fun ω => (X ω - μ₁ ω) ^ 4) = fun ω =>
        (((μ₂ ω - μ₁ ω) ^ 4 + 4 * ((μ₂ ω - μ₁ ω) ^ 3 * (X ω - μ₂ ω) ^ 1)) +
          6 * ((μ₂ ω - μ₁ ω) ^ 2 * (X ω - μ₂ ω) ^ 2) +
          4 * ((μ₂ ω - μ₁ ω) ^ 1 * (X ω - μ₂ ω) ^ 3)) +
          (μ₂ ω - μ₁ ω) ^ 0 * (X ω - μ₂ ω) ^ 4 := by
      funext ω; ring
    have i01 : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 4 +
        4 * ((μ₂ ω - μ₁ ω) ^ 3 * (X ω - μ₂ ω) ^ 1)) P := i0.add i1
    have i012 : Integrable (fun ω => ((μ₂ ω - μ₁ ω) ^ 4 +
        4 * ((μ₂ ω - μ₁ ω) ^ 3 * (X ω - μ₂ ω) ^ 1)) +
        6 * ((μ₂ ω - μ₁ ω) ^ 2 * (X ω - μ₂ ω) ^ 2)) P := i01.add i2
    have i0123 : Integrable (fun ω => (((μ₂ ω - μ₁ ω) ^ 4 +
        4 * ((μ₂ ω - μ₁ ω) ^ 3 * (X ω - μ₂ ω) ^ 1)) +
        6 * ((μ₂ ω - μ₁ ω) ^ 2 * (X ω - μ₂ ω) ^ 2)) +
        4 * ((μ₂ ω - μ₁ ω) ^ 1 * (X ω - μ₂ ω) ^ 3)) P := i012.add i3
    rw [e, integral_add i0123 i4, integral_add i012 i3, integral_add i01 i2, integral_add i0 i1,
      integral_const_mul, integral_const_mul, integral_const_mul]
  -- (iii) the `V₁`-weighted square identity
  have e3 := integral_mul_sq_sub h₁ h₂ h12 h₁.measurable_var hK
    (fun ω => by rw [abs_of_nonneg (h₁.nonneg ω)]; exact h₁.le_bound ω)
  -- assemble
  have iΔ2V1 : Integrable (fun ω => V₁ ω * (μ₂ ω - μ₁ ω) ^ 2) P :=
    (hIV (a := 2) (b := 0) (by norm_num)).congr (Eventually.of_forall fun ω => by simp)
  have iΔ2V2 : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 2 * V₂ ω) P :=
    (hIV₂ (a := 2) (b := 0) (by norm_num)).congr (Eventually.of_forall fun ω => by simp; ring)
  have s1 : ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * (V₁ ω - V₂ ω) ∂P =
      ∫ ω, V₁ ω * (μ₂ ω - μ₁ ω) ^ 2 ∂P - ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * V₂ ω ∂P := by
    rw [← integral_sub iΔ2V1 iΔ2V2]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have s2 : ∫ ω, V₁ ω * (V₁ ω - V₂ ω) ∂P = ∫ ω, V₁ ω * V₁ ω ∂P - ∫ ω, V₁ ω * V₂ ω ∂P := by
    rw [← integral_sub hv11 hv12]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have s3 : ∫ ω, (V₁ ω - V₂ ω) ^ 2 ∂P =
      ∫ ω, V₁ ω * V₁ ω ∂P - 2 * ∫ ω, V₁ ω * V₂ ω ∂P + ∫ ω, V₂ ω * V₂ ω ∂P := by
    have hcomb : Integrable (fun ω => V₁ ω * V₁ ω - 2 * (V₁ ω * V₂ ω)) P :=
      hv11.sub (hv12.const_mul 2)
    rw [← integral_const_mul, ← integral_sub hv11 (hv12.const_mul 2), ← integral_add hcomb hv22]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [m1, m3, m2', m4'] at e2
  rw [s1, s3]
  rw [s2] at e3
  linarith

/-- **The quartic bound**: if `V₁ − V₂ ≤ δ`, then `E[(μ₂ − μ₁)⁴] ≤ 6 δ E[V₁ − V₂]`. -/
theorem integral_pow_four_sub_le (h₁ : IsCondGaussian 𝒢₁ P X μ₁ V₁ K)
    (h₂ : IsCondGaussian 𝒢₂ P X μ₂ V₂ K) (h12 : 𝒢₁ ≤ 𝒢₂) {δ : ℝ}
    (hD : ∀ ω, V₁ ω - V₂ ω ≤ δ) :
    ∫ ω, (μ₂ ω - μ₁ ω) ^ 4 ∂P ≤ 6 * δ * ∫ ω, (V₁ ω - V₂ ω) ∂P := by
  have hK : 0 ≤ K := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact (h₁.nonneg ω).trans (h₁.le_bound ω)
  have hI2 := integrable_two_level (W := fun _ => (1 : ℝ)) (a := 2) (b := 0) h₁ h₂
    measurable_const zero_le_one (fun _ => by simp) (by norm_num)
  have hsq : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 2) P :=
    hI2.congr (Eventually.of_forall fun ω => by simp)
  have hD2 : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 2 * (V₁ ω - V₂ ω)) P := by
    have h1 := integrable_two_level (W := V₁) (a := 2) (b := 0) h₁ h₂ h₁.measurable_var' hK
      (fun ω => by rw [abs_of_nonneg (h₁.nonneg ω)]; exact h₁.le_bound ω) (by norm_num)
    have h2 := integrable_two_level (W := V₂) (a := 2) (b := 0) h₁ h₂ h₂.measurable_var' hK
      (fun ω => by rw [abs_of_nonneg (h₂.nonneg ω)]; exact h₂.le_bound ω) (by norm_num)
    exact (h1.sub h2).congr (Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)
  have hDi : Integrable (fun ω => (V₁ ω - V₂ ω) ^ 2) P :=
    Integrable.of_bound ((h₁.measurable_var'.sub h₂.measurable_var').pow_const 2).aestronglyMeasurable
      (K ^ 2) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        have : |V₁ ω - V₂ ω| ≤ K := abs_sub_le_iff.2
          ⟨by linarith [h₁.le_bound ω, h₂.nonneg ω], by linarith [h₂.le_bound ω, h₁.nonneg ω]⟩
        exact pow_le_pow_left₀ (abs_nonneg _) this 2)
  have hq := integral_pow_four_sub h₁ h₂ h12
  have hw := integral_mul_sq_sub (W := fun _ => (1 : ℝ)) h₁ h₂ h12 measurable_const zero_le_one
    (fun _ => by simp)
  simp only [one_mul] at hw
  have hle : ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 * (V₁ ω - V₂ ω) ∂P ≤ ∫ ω, δ * (μ₂ ω - μ₁ ω) ^ 2 ∂P :=
    integral_mono hD2 (hsq.const_mul δ) fun ω => by
      rw [mul_comm δ]; exact mul_le_mul_of_nonneg_left (hD ω) (sq_nonneg _)
  rw [integral_const_mul, hw] at hle
  have h3 : 0 ≤ ∫ ω, (V₁ ω - V₂ ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [hq]
  nlinarith

end TwoLevel
