/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.GFF.LocalSets.MarkedAvoidance
import InteractingSLE.Spec.Sec7.LocalExtGLocal

/-!
# Lemma 7.1's conditional clause: identifying a larger conditional law by unit modulus

Packet PROVE-LEMMA72D. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L600–L602) and of Lemma 7.2
(L622–L640): the pocket coupling clause is needed **conditionally on the exterior record** `Q` (Lemma 7.2's proof). The
clause is known given the prefix σ-algebra `𝓐_t`; given the larger σ-algebra `𝒢_t` of the germs of the marked union
`B_t` and the histories, the field paired with `φ` is Gaussian with **the same variance** and an unknown
`𝒢_t`-measurable mean (history-marked locality). Both laws are compatible only if the two means agree:

* `ae_eq_on_of_condExp_eq_of_norm_eq_one` (**unit modulus**): if `|Z| = |Y| = 1`, `Y` is `𝓐`-measurable and
  `E[Z | 𝓐] = Y` on an `𝓐`-event `E`, then `Z = Y` almost surely on `E`
  (`E[|Z − Y|² 1_E] = 2P(E) − 2 Re E[Z Ȳ 1_E] = 0`);
* `ae_condExp_eq_on_of_kernel`: if `E[X | 𝓐] = e^{iM} c` and `E[X | 𝒢] = e^{iM'} c` on an `𝓐`-event `E`
  (`𝓐 ≤ 𝒢`, `0 < c ≤ 1` `𝓐`-measurable), then `E[X | 𝒢'] = e^{iM} c` on `E` for every `𝓐 ≤ 𝒢' ≤ 𝒢`;
* `ae_condExp_cond_eq_on`: the same law under `P[· | G]` for every event `G ∈ 𝒢'` of positive probability;
* `ae_condExp_eq_on_of_norm_eq` (the form used by `Lemma72DClause`): if `|E[X | 𝒢]| = |E[X | 𝓐]|` on an `𝓐`-event
  `E`, then `E[X | 𝒢] = E[X | 𝓐]` on `E` (no measurability of the formula is needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma72D

open Complex

section Unit

variable {Ω : Type*} {𝓐 𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Unit modulus.** If `|Z| = |Y| = 1`, `Y` is `𝓐`-measurable and `E[Z | 𝓐] = Y` almost surely on an `𝓐`-event
`E`, then `Z = Y` almost surely on `E`. -/
theorem ae_eq_on_of_condExp_eq_of_norm_eq_one (h𝓐 : 𝓐 ≤ mΩ) {Z Y : Ω → ℂ} (hZm : Measurable Z)
    (hZ : ∀ ω, ‖Z ω‖ = 1) (hYm : StronglyMeasurable[𝓐] Y) (hY : ∀ ω, ‖Y ω‖ = 1) {E : Set Ω}
    (hE : MeasurableSet[𝓐] E) (hc : ∀ᵐ ω ∂P, ω ∈ E → P[Z | 𝓐] ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ E → Z ω = Y ω := by
  have hEm : MeasurableSet E := h𝓐 _ hE
  set W : Ω → ℂ := E.indicator fun ω => starRingEnd ℂ (Y ω) with hWdef
  have hWm : StronglyMeasurable[𝓐] W :=
    (Complex.continuous_conj.comp_stronglyMeasurable hYm).indicator hE
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E
    · rw [hWdef, indicator_of_mem hω, Complex.norm_conj, hY ω]
    · rw [hWdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hZi : Integrable Z P :=
    Integrable.of_bound hZm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (hZ ω).le)
  have hYm' : Measurable Y := (hYm.mono h𝓐).measurable
  have key := LocalSets.integral_mul_condExp_of_bdd h𝓐 hWm hWb hZi
  -- `∫ W · E[Z | 𝓐] = P(E)`
  have hYY : ∀ ω, starRingEnd ℂ (Y ω) * Y ω = 1 := fun ω => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hY ω]
    norm_num
  have h1 : ∫ ω, W ω * P[Z | 𝓐] ω ∂P = ((P E).toReal : ℂ) := by
    have e : (fun ω => W ω * P[Z | 𝓐] ω) =ᵐ[P] E.indicator fun _ => (1 : ℂ) := by
      filter_upwards [hc] with ω hω
      by_cases hωE : ω ∈ E
      · rw [hWdef, indicator_of_mem hωE, indicator_of_mem hωE, hω hωE, hYY]
      · rw [hWdef, indicator_of_notMem hωE, indicator_of_notMem hωE, zero_mul]
    rw [integral_congr_ae e, integral_indicator hEm, setIntegral_const, Complex.real_smul, mul_one]
    rfl
  -- `∫_E Z Ȳ = P(E)`
  have hZY : Integrable (fun ω => Z ω * starRingEnd ℂ (Y ω)) P := by
    refine Integrable.of_bound (hZm.mul (Complex.continuous_conj.measurable.comp hYm')).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Complex.norm_conj, hZ ω, hY ω, one_mul]
  have h2 : ∫ ω in E, Z ω * starRingEnd ℂ (Y ω) ∂P = ((P E).toReal : ℂ) := by
    rw [← h1, ← key, ← integral_indicator hEm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hωE : ω ∈ E
    · simp only [hWdef, indicator_of_mem hωE]; ring
    · simp only [hWdef, indicator_of_notMem hωE, zero_mul]
  -- `∫_E |Z − Y|² = 0`
  have hsq : ∀ ω, Complex.normSq (Z ω - Y ω) = 2 - 2 * (Z ω * starRingEnd ℂ (Y ω)).re := fun ω => by
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hZ ω, hY ω]
    ring
  have hsqi : Integrable (fun ω => Complex.normSq (Z ω - Y ω)) P := by
    refine Integrable.of_bound (Complex.continuous_normSq.measurable.comp (hZm.sub hYm')).aestronglyMeasurable 4
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), hsq]
    have := Complex.abs_re_le_norm (Z ω * starRingEnd ℂ (Y ω))
    rw [norm_mul, Complex.norm_conj, hZ ω, hY ω, one_mul] at this
    linarith [neg_abs_le (Z ω * starRingEnd ℂ (Y ω)).re]
  have hre : Integrable (fun ω => (Z ω * starRingEnd ℂ (Y ω)).re) P := hZY.re
  have hre2 : ∫ ω in E, (Z ω * starRingEnd ℂ (Y ω)).re ∂P = (P E).toReal := by
    have e := integral_re (𝕜 := ℂ) (hZY.integrableOn (s := E))
    rw [h2] at e
    exact e.trans (Complex.ofReal_re _)
  have h3 : ∫ ω in E, Complex.normSq (Z ω - Y ω) ∂P = 0 := by
    simp_rw [hsq]
    rw [integral_sub (integrable_const _) (hre.const_mul 2).integrableOn, setIntegral_const,
      integral_const_mul, hre2, smul_eq_mul]
    simp only [Measure.real]
    ring
  have h4 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => Complex.normSq_nonneg _)
    hsqi.integrableOn).1 h3
  rw [EventuallyEq, ae_restrict_iff' hEm] at h4
  filter_upwards [h4] with ω hω hωE
  have := hω hωE
  simp only [Pi.zero_apply, Complex.normSq_eq_zero, sub_eq_zero] at this
  exact this

end Unit

section Upgrade

variable {Ω : Type*} {𝓐 𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

omit mΩ [IsProbabilityMeasure P] in
theorem measurable_cexp_I_mul {m : MeasurableSpace Ω} {M : Ω → ℝ} (hM : Measurable[m] M) :
    Measurable[m] fun ω => cexp (I * (M ω : ℂ)) :=
  Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hM).const_mul I)

/-- **The larger conditional law has the smaller mean.** Let `𝓐 ≤ 𝒢' ≤ 𝒢`, `E ∈ 𝓐`, `c` `𝓐`-measurable with
`0 < c ≤ 1`, `M` `𝓐`-measurable and `M'` `𝒢`-measurable. If almost surely on `E`
`E[X | 𝓐] = e^{iM} c` and `E[X | 𝒢] = e^{iM'} c`, then `E[X | 𝒢'] = e^{iM} c` almost surely on `E`. -/
theorem ae_condExp_eq_on_of_kernel (h𝓐𝒢' : 𝓐 ≤ 𝒢') (h𝒢'𝒢 : 𝒢' ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → ℂ}
    (hXi : Integrable X P) {M M' c : Ω → ℝ} (hM : Measurable[𝓐] M) (hM' : Measurable[𝒢] M')
    (hc : Measurable[𝓐] c) (hc0 : ∀ ω, 0 < c ω) (hc1 : ∀ ω, c ω ≤ 1) {E : Set Ω}
    (hE : MeasurableSet[𝓐] E)
    (hA : ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝓐] ω = cexp (I * (M ω : ℂ)) * (c ω : ℂ))
    (hG : ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢] ω = cexp (I * (M' ω : ℂ)) * (c ω : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢'] ω = cexp (I * (M ω : ℂ)) * (c ω : ℂ) := by
  have h𝓐𝒢 : 𝓐 ≤ 𝒢 := h𝓐𝒢'.trans h𝒢'𝒢
  have h𝓐 : 𝓐 ≤ mΩ := h𝓐𝒢.trans h𝒢
  set Z : Ω → ℂ := fun ω => cexp (I * (M' ω : ℂ)) with hZdef
  have hZm𝒢 : Measurable[𝒢] Z := measurable_cexp_I_mul hM'
  have hZm : Measurable Z := hZm𝒢.mono h𝒢 le_rfl
  have hZn : ∀ ω, ‖Z ω‖ = 1 := fun ω => by
    simp only [hZdef]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hZi : Integrable Z P :=
    Integrable.of_bound hZm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (hZn ω).le)
  have hcC : Measurable[𝓐] fun ω => (c ω : ℂ) := Complex.measurable_ofReal.comp hc
  have hcb : ∀ ω, ‖(c ω : ℂ)‖ ≤ 1 := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc0 ω)]; exact hc1 ω
  set Y' : Ω → ℂ := fun ω => (c ω : ℂ) * Z ω with hY'def
  have hY'i : Integrable Y' P := hZi.bdd_mul (hcC.mono h𝓐 le_rfl).aestronglyMeasurable
    (Eventually.of_forall hcb)
  -- the tower along `E`
  have h1 : P[P[X | 𝒢] | 𝓐] =ᵐ[P] P[X | 𝓐] := condExp_condExp_of_le h𝓐𝒢 h𝒢
  have h2 : E.indicator (P[X | 𝒢]) =ᵐ[P] E.indicator Y' := by
    filter_upwards [hG] with ω hω
    by_cases hωE : ω ∈ E
    · rw [indicator_of_mem hωE, indicator_of_mem hωE, hω hωE, hY'def]; simp only; ring
    · rw [indicator_of_notMem hωE, indicator_of_notMem hωE]
  have h3 : P[E.indicator (P[X | 𝒢]) | 𝓐] =ᵐ[P] E.indicator (P[P[X | 𝒢] | 𝓐]) :=
    condExp_indicator integrable_condExp hE
  have h4 : P[E.indicator Y' | 𝓐] =ᵐ[P] E.indicator (P[Y' | 𝓐]) := condExp_indicator hY'i hE
  have h5 : P[E.indicator (P[X | 𝒢]) | 𝓐] =ᵐ[P] P[E.indicator Y' | 𝓐] := condExp_congr_ae h2
  have h6 : P[Y' | 𝓐] =ᵐ[P] fun ω => (c ω : ℂ) * P[Z | 𝓐] ω := by
    have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      hcC.stronglyMeasurable (by simpa [ContinuousLinearMap.mul_apply'] using hY'i) hZi
    simpa [ContinuousLinearMap.mul_apply'] using hpull
  have hZA : ∀ᵐ ω ∂P, ω ∈ E → P[Z | 𝓐] ω = cexp (I * (M ω : ℂ)) := by
    filter_upwards [h1, h3, h4, h5, h6, hA] with ω e1 e3 e4 e5 e6 eA hωE
    have k := e3.symm.trans (e5.trans e4)
    rw [indicator_of_mem hωE, indicator_of_mem hωE, e1, eA hωE, e6] at k
    have hc' : (c ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc0 ω).ne'
    rw [mul_comm (cexp _)] at k
    exact (mul_left_cancel₀ hc' k).symm
  have hunit := ae_eq_on_of_condExp_eq_of_norm_eq_one h𝓐 hZm hZn
    (measurable_cexp_I_mul hM).stronglyMeasurable (fun ω => by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _) hE hZA
  have hG' : ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢] ω = cexp (I * (M ω : ℂ)) * (c ω : ℂ) := by
    filter_upwards [hG, hunit] with ω hω hu hωE
    rw [hω hωE]
    exact congrArg (· * (c ω : ℂ)) (hu hωE)
  have hYm : StronglyMeasurable[𝒢'] fun ω => cexp (I * (M ω : ℂ)) * (c ω : ℂ) :=
    (((measurable_cexp_I_mul hM).mul hcC).mono h𝓐𝒢' le_rfl).stronglyMeasurable
  have hYi : Integrable (fun ω => cexp (I * (M ω : ℂ)) * (c ω : ℂ)) P := by
    refine Integrable.of_bound ((measurable_cexp_I_mul hM).mul hcC |>.mono h𝓐 le_rfl).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hcb ω
  exact Sec6.condExp_ae_eq_on_of_le h𝒢'𝒢 h𝒢 hXi hYm hYi (h𝓐𝒢' _ hE) hG'

omit [IsProbabilityMeasure P] in
/-- **The law on an event passes to `P[· | G]`** for every event `G ∈ 𝒢'` of positive probability. -/
theorem ae_condExp_cond_eq_on [IsFiniteMeasure P] (h𝒢' : 𝒢' ≤ mΩ) {X : Ω → ℂ} (hXm : Measurable X)
    (hXb : ∀ ω, ‖X ω‖ ≤ 1) {Y : Ω → ℂ} (hYm : StronglyMeasurable[𝒢'] Y) (hYi : Integrable Y P) {E : Set Ω}
    (hE : MeasurableSet[𝒢'] E) (hXY : ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢'] ω = Y ω) {G : Set Ω}
    (hG : MeasurableSet[𝒢'] G) (hPG : P G ≠ 0) :
    ∀ᵐ ω ∂(P[|G]), ω ∈ E → (P[|G])[X | 𝒢'] ω = Y ω := by
  have hXi : ∀ μ : Measure Ω, IsFiniteMeasure μ → Integrable X μ := fun μ _ =>
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  have hEY : StronglyMeasurable[𝒢'] (E.indicator Y) := hYm.indicator hE
  have hEYi : Integrable (E.indicator Y) P := hYi.indicator (h𝒢' _ hE)
  have h1 : P[E.indicator X | 𝒢'] =ᵐ[P] E.indicator Y := by
    filter_upwards [condExp_indicator (hXi P inferInstance) hE, hXY] with ω e1 e2
    rw [e1]
    by_cases hωE : ω ∈ E
    · rw [indicator_of_mem hωE, indicator_of_mem hωE, e2 hωE]
    · rw [indicator_of_notMem hωE, indicator_of_notMem hωE]
  have hfin : IsFiniteMeasure (P[|G]) := inferInstance
  have h2 := LocalExt.condExp_cond_ae_eq le_rfl h𝒢' hG hPG ((hXi P inferInstance).indicator (h𝒢' _ hE)) hEY hEYi h1
  filter_upwards [h2, condExp_indicator (hXi (P[|G]) hfin) hE] with ω e2 e3 hωE
  rw [e3, indicator_of_mem hωE, indicator_of_mem hωE] at e2
  exact e2

/-- **Equal moduli force equal conditional expectations.** For `𝓐 ≤ 𝒢`, `|X| ≤ 1` and `E ∈ 𝓐`: if
`|E[X | 𝒢]| = |E[X | 𝓐]|` almost surely on `E`, then `E[X | 𝒢] = E[X | 𝓐]` almost surely on `E`
(`E[|E[X|𝒢] − E[X|𝓐]|² 1_E] = E[(|E[X|𝒢]|² − |E[X|𝓐]|²) 1_E] = 0` by the tower property). -/
theorem ae_condExp_eq_on_of_norm_eq (h𝓐𝒢 : 𝓐 ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → ℂ} (hXm : Measurable X)
    (hXb : ∀ ω, ‖X ω‖ ≤ 1) {E : Set Ω} (hE : MeasurableSet[𝓐] E)
    (hn : ∀ᵐ ω ∂P, ω ∈ E → ‖P[X | 𝒢] ω‖ = ‖P[X | 𝓐] ω‖) :
    ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢] ω = P[X | 𝓐] ω := by
  have h𝓐 : 𝓐 ≤ mΩ := h𝓐𝒢.trans h𝒢
  have hEm : MeasurableSet E := h𝓐 _ hE
  have hXi : Integrable X P :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  have hbd : ∀ m : MeasurableSpace Ω, m ≤ mΩ → ∀ᵐ ω ∂P, ‖P[X | m] ω‖ ≤ 1 := fun m hm => by
    have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) (μ := P) (R := (1 : ℝ)) (f := fun ω => ‖X ω‖)
      (Eventually.of_forall fun ω => by rw [abs_norm]; exact hXb ω)
    filter_upwards [norm_condExp_le (m := m) (μ := P) X, h2] with ω h1 h2
    exact h1.trans ((le_abs_self _).trans (by exact_mod_cast h2))
  set YA : Ω → ℂ := P[X | 𝓐] with hYAdef
  set YG : Ω → ℂ := P[X | 𝒢] with hYGdef
  have hS : MeasurableSet[𝓐] {ω | ‖YA ω‖ ≤ 1} :=
    measurableSet_le (stronglyMeasurable_condExp.norm.measurable) measurable_const
  set YB : Ω → ℂ := {ω | ‖YA ω‖ ≤ 1}.piecewise YA 0 with hYBdef
  have hYBm : StronglyMeasurable[𝓐] YB := stronglyMeasurable_condExp.piecewise hS stronglyMeasurable_const
  have hYB : YB =ᵐ[P] YA := by
    filter_upwards [hbd 𝓐 h𝓐] with ω hω
    exact Set.piecewise_eq_of_mem _ _ _ hω
  have hYBb : ∀ ω, ‖YB ω‖ ≤ 1 := fun ω => by
    by_cases hω : ‖YA ω‖ ≤ 1
    · simp only [hYBdef, Set.piecewise, Set.mem_ofPred_eq, hω, ↓reduceIte]
    · simp only [hYBdef, Set.piecewise, Set.mem_ofPred_eq, hω, ↓reduceIte, Pi.zero_apply, norm_zero]
      exact zero_le_one
  set W : Ω → ℂ := E.indicator fun ω => starRingEnd ℂ (YB ω) with hWdef
  have hWm : StronglyMeasurable[𝓐] W := (Complex.continuous_conj.comp_stronglyMeasurable hYBm).indicator hE
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E
    · rw [hWdef, indicator_of_mem hω, Complex.norm_conj]; exact hYBb ω
    · rw [hWdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hYGi : Integrable YG P := integrable_condExp
  have key0 := LocalSets.integral_mul_condExp_of_bdd h𝓐 hWm hWb hYGi
  have hT : P[YG | 𝓐] =ᵐ[P] YA := condExp_condExp_of_le h𝓐𝒢 h𝒢
  have key : ∫ ω, W ω * YG ω ∂P = ∫ ω, W ω * YA ω ∂P :=
    key0.trans (integral_congr_ae (hT.mono fun ω h => by simp only [h]))
  -- `∫_E YG · conj YB = ∫_E |YB|²`
  have hYBm' : Measurable YB := (hYBm.mono h𝓐).measurable
  have hcross : Integrable (fun ω => YG ω * starRingEnd ℂ (YB ω)) P :=
    hYGi.mul_bdd (Complex.continuous_conj.measurable.comp hYBm').aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Complex.norm_conj]; exact hYBb ω)
  have hsqB : Integrable (fun ω => Complex.normSq (YB ω)) P :=
    Integrable.of_bound (Complex.continuous_normSq.measurable.comp hYBm').aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
        nlinarith [hYBb ω, norm_nonneg (YB ω)])
  have h2 : ∫ ω in E, YG ω * starRingEnd ℂ (YB ω) ∂P = ((∫ ω in E, Complex.normSq (YB ω) ∂P : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator hEm, ← integral_indicator hEm]
    have e1 : (fun ω => W ω * YG ω) = E.indicator fun ω => YG ω * starRingEnd ℂ (YB ω) := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hWdef, indicator_of_mem hω]; ring
      · simp only [hWdef, indicator_of_notMem hω, zero_mul]
    have e2 : (fun ω => W ω * YA ω) =ᵐ[P] E.indicator fun ω => ((Complex.normSq (YB ω) : ℝ) : ℂ) := by
      filter_upwards [hYB] with ω hω
      by_cases hωE : ω ∈ E
      · simp only [hWdef, indicator_of_mem hωE, ← hω]
        rw [mul_comm, Complex.mul_conj]
      · simp only [hWdef, indicator_of_notMem hωE, zero_mul]
    rw [← e1, key, integral_congr_ae e2]
  -- `∫_E |YG − YB|² = 0`
  have hYGb := hbd 𝒢 h𝒢
  have hsq : ∀ᵐ ω ∂P, ω ∈ E → Complex.normSq (YG ω - YB ω) =
      2 * Complex.normSq (YB ω) - 2 * (YG ω * starRingEnd ℂ (YB ω)).re := by
    filter_upwards [hn, hYB] with ω h1 h2 hωE
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (YG ω), h1 hωE, ← h2, ← Complex.normSq_eq_norm_sq]
    ring
  have hsqi : Integrable (fun ω => Complex.normSq (YG ω - YB ω)) P := by
    refine Integrable.of_bound (Complex.continuous_normSq.measurable.comp
      ((stronglyMeasurable_condExp.mono h𝒢).measurable.sub hYBm')).aestronglyMeasurable 4 ?_
    filter_upwards [hYGb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    have := norm_sub_le (YG ω) (YB ω)
    nlinarith [hYBb ω, norm_nonneg (YG ω - YB ω), norm_nonneg (YB ω)]
  have hre : Integrable (fun ω => (YG ω * starRingEnd ℂ (YB ω)).re) P := hcross.re
  have hre2 : ∫ ω in E, (YG ω * starRingEnd ℂ (YB ω)).re ∂P = ∫ ω in E, Complex.normSq (YB ω) ∂P := by
    have e := integral_re (𝕜 := ℂ) (hcross.integrableOn (s := E))
    rw [h2] at e
    exact e.trans (Complex.ofReal_re _)
  have h3 : ∫ ω in E, Complex.normSq (YG ω - YB ω) ∂P = 0 := by
    rw [setIntegral_congr_ae hEm hsq, integral_sub ((hsqB.const_mul 2).integrableOn)
      ((hre.const_mul 2).integrableOn), integral_const_mul, integral_const_mul, hre2, sub_self]
  have h4 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => Complex.normSq_nonneg _)
    hsqi.integrableOn).1 h3
  rw [EventuallyEq, ae_restrict_iff' hEm] at h4
  filter_upwards [h4, hYB] with ω hω hB hωE
  have := hω hωE
  simp only [Pi.zero_apply, Complex.normSq_eq_zero, sub_eq_zero] at this
  rw [this, hB]

end Upgrade

end InteractingSLE.Sec7.Lemma72D
