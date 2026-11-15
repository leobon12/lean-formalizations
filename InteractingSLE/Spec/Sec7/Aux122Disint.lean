/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import MathFin.Probability.Brownian.QuadraticVariationL2
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# §7.4, Aux. lemma 122: disintegration over the initial information (kernel facts)

Packet PROVE-AUX119-130. Specification §7.4.1, Aux. lemma 122, last paragraph of its proof
(`source/spec/p385-432.md` L111–L139, p. 391): "The Brownian motion in that proof is Brownian in the retained
filtration, so it is independent of its time-zero sigma-algebra. Disintegration over that initial information
preserves the integrated SDE and this Brownian property." The same step is Aux. lemma 125's "conditionally on `𝓔`,
… this kernel has the canonical integrated SLE driving marginal" (p. 395).

This file collects the measure-theoretic facts about the regular conditional law `ν ω₀ = condExpKernel P 𝓔 ω₀`
(standard Borel `Ω`) used by the disintegration (`Aux122DisintEvol.lean`):

* `ae_ae_condExpKernel`: a `P`-almost sure property holds `ν ω₀`-almost surely for `P`-almost every `ω₀`;
* `ae_condExpKernel_apply_eq_indicator`, `ae_ae_condExpKernel_mem`: an `𝓔`-event has conditional probability
  `1_s(ω₀)`;
* `ae_ae_condExpKernel_eq`: an `𝓔`-measurable map into a second-countable `T₁` space is `ν ω₀`-almost surely equal
  to its value at `ω₀` (the initial word is fixed under the conditional law);
* `ae_setIntegral_condExpKernel`: set integrals under `ν ω₀` are versions of conditional expectations;
* `condExp_mul_eq_zero`: if `X` is independent of `𝓕_s`, centred and integrable, `Y` is `𝓕_s`-measurable and
  `𝓔 ≤ 𝓕_s`, then `E[Y X | 𝓔] = 0`; for a filtered Brownian motion this gives the three conditional identities
  `E[1_A (B_t − B_s) | 𝓔] = 0`, `E[1_A ((B_t − B_s)² − (t − s)) | 𝓔] = 0` and `E[1_A B_s (B_t − B_s) | 𝓔] = 0`
  (`condExp_indicator_increment`, `condExp_indicator_increment_sq`, `condExp_indicator_mul_increment`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux122Disint

section Kernel

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A `P`-almost sure property holds under almost every conditional law.** -/
theorem ae_ae_condExpKernel (h𝓔 : 𝓔 ≤ mΩ) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), p ω := by
  have h' : ∀ᵐ ω ∂(condExpKernel P 𝓔 ∘ₘ P.trim h𝓔), p ω := by
    rw [condExpKernel_comp_trim h𝓔]
    exact h
  exact ae_of_ae_trim h𝓔 (Measure.ae_ae_of_ae_comp h')

/-- **The conditional probability of an `𝓔`-event is its indicator.** -/
theorem ae_condExpKernel_apply_eq_indicator (h𝓔 : 𝓔 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[𝓔] s) :
    ∀ᵐ ω₀ ∂P, condExpKernel P 𝓔 ω₀ s = s.indicator 1 ω₀ := by
  have hcond : P⟦s | 𝓔⟧ = s.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable h𝓔 (stronglyMeasurable_const.indicator hs)
      ((integrable_const (1 : ℝ)).indicator (h𝓔 s hs))
  filter_upwards [condExpKernel_ae_eq_condExp h𝓔 (h𝓔 s hs)] with ω₀ hω₀
  rw [hcond] at hω₀
  by_cases h : ω₀ ∈ s
  · rw [Set.indicator_of_mem h] at hω₀ ⊢
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at hω₀
    exact hω₀
  · rw [Set.indicator_of_notMem h] at hω₀ ⊢
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hω₀
    exact hω₀.resolve_right (measure_ne_top _ _)

/-- **An `𝓔`-event containing `ω₀` holds almost surely under the conditional law at `ω₀`.** -/
theorem ae_ae_condExpKernel_mem (h𝓔 : 𝓔 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[𝓔] s) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ s → ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), ω ∈ s := by
  filter_upwards [ae_condExpKernel_apply_eq_indicator h𝓔 hs] with ω₀ hω₀ hmem
  rw [Set.indicator_of_mem hmem, Pi.one_apply] at hω₀
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff (h𝓔 s hs)).2 hω₀

/-- **An initially measurable map is fixed by the conditional law.** For an `𝓔`-measurable `f` with values in a
second-countable `T₁` space, `f = f ω₀` holds `ν ω₀`-almost surely for `P`-almost every `ω₀`. -/
theorem ae_ae_condExpKernel_eq {E : Type*} [TopologicalSpace E] [SecondCountableTopology E] [T1Space E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (h𝓔 : 𝓔 ≤ mΩ) {f : Ω → E} (hf : Measurable[𝓔] f) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), f ω = f ω₀ := by
  set 𝓑 := TopologicalSpace.countableBasis E with h𝓑
  have h𝓑c : 𝓑.Countable := TopologicalSpace.countable_countableBasis E
  have h𝓑o : ∀ U ∈ 𝓑, IsOpen U := fun U hU => TopologicalSpace.isOpen_of_mem_countableBasis hU
  have hU : ∀ᵐ ω₀ ∂P, ∀ U ∈ 𝓑, f ω₀ ∉ U → condExpKernel P 𝓔 ω₀ (f ⁻¹' U) = 0 := by
    rw [ae_ball_iff h𝓑c]
    intro U hU
    filter_upwards [ae_condExpKernel_apply_eq_indicator h𝓔 (hf (h𝓑o U hU).measurableSet)] with ω₀ h hn
    rwa [Set.indicator_of_notMem (show ω₀ ∉ f ⁻¹' U from hn)] at h
  filter_upwards [hU] with ω₀ hω₀
  have hsub : {ω | ¬ f ω = f ω₀} ⊆ ⋃ U ∈ {U ∈ 𝓑 | f ω₀ ∉ U}, f ⁻¹' U := by
    intro ω hω
    obtain ⟨U, hU𝓑, hyU, hUsub⟩ := (TopologicalSpace.isBasis_countableBasis E).exists_subset_of_mem_open
      (show f ω ∈ ({f ω₀}ᶜ : Set E) from hω) isOpen_compl_singleton
    exact mem_biUnion ⟨hU𝓑, fun h => hUsub h rfl⟩ hyU
  rw [ae_iff]
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff (h𝓑c.mono (sep_subset _ _))).2 fun U hU => hω₀ U hU.1 hU.2)

/-- **Set integrals under the conditional law are conditional expectations.** -/
theorem ae_setIntegral_condExpKernel (h𝓔 : 𝓔 ≤ mΩ) {g : Ω → ℝ} (hg : Integrable g P) {A : Set Ω}
    (hA : MeasurableSet A) :
    (fun ω₀ => ∫ ω in A, g ω ∂(condExpKernel P 𝓔 ω₀)) =ᵐ[P] P[A.indicator g | 𝓔] := by
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝓔 (hg.indicator hA)] with ω₀ h
  rw [h, integral_indicator hA]

end Kernel

/-! ### Conditional identities of a filtered Brownian motion -/

section Brownian

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A centred variable independent of `𝓕_s` is conditionally orthogonal to `𝓕_s`-measurable ones, also given
`𝓔 ≤ 𝓕_s`**: `E[Y X | 𝓔] = 0`. -/
theorem condExp_mul_eq_zero {s : ℝ≥0} (h𝓔 : 𝓔 ≤ 𝓕 s) {mX : MeasurableSpace Ω} (hmX : mX ≤ mΩ)
    (hind : Indep mX (𝓕 s) P) {X Y : Ω → ℝ} (hXm : StronglyMeasurable[mX] X) (hXi : Integrable X P)
    (hX0 : P[X] = 0) (hY : StronglyMeasurable[𝓕 s] Y) (hYX : Integrable (Y * X) P) :
    P[Y * X | 𝓔] =ᵐ[P] 0 := by
  have h1 : P[Y * X | 𝓕 s] =ᵐ[P] Y * P[X | 𝓕 s] := condExp_mul_of_stronglyMeasurable_left hY hYX hXi
  have h2 : P[X | 𝓕 s] =ᵐ[P] fun _ => P[X] := condExp_indep_eq hmX (𝓕.le s) hXm hind
  have h3 : P[Y * X | 𝓕 s] =ᵐ[P] 0 := by
    filter_upwards [h1, h2] with ω h h'
    rw [h, Pi.mul_apply, h', hX0, mul_zero, Pi.zero_apply]
  calc P[Y * X | 𝓔] =ᵐ[P] P[P[Y * X | 𝓕 s] | 𝓔] := (condExp_condExp_of_le h𝓔 (𝓕.le s)).symm
    _ =ᵐ[P] P[(0 : Ω → ℝ) | 𝓔] := condExp_congr_ae h3
    _ = 0 := condExp_zero

variable {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- The increment σ-algebra of a filtered Brownian motion is independent of the past. -/
theorem indep_increment (hB : IsFilteredBrownianReal 𝓕 B P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (𝓕 s) P :=
  hB.2.2 s t hst

omit [IsProbabilityMeasure P] in
theorem measurable_eval (hB : IsFilteredBrownianReal 𝓕 B P) (t : ℝ≥0) : Measurable (B t) :=
  (hB.2.1 t).mono (𝓕.le t) le_rfl

omit [IsProbabilityMeasure P] in
theorem measurable_increment (hB : IsFilteredBrownianReal 𝓕 B P) (s t : ℝ≥0) :
    Measurable fun ω => B t ω - B s ω :=
  (measurable_eval hB t).sub (measurable_eval hB s)

theorem memLp_two (hB : IsFilteredBrownianReal 𝓕 B P) (s t : ℝ≥0) :
    MemLp (fun ω => B t ω - B s ω) 2 P :=
  (MathFin.QuadraticVariationL2.memLp_increment_four hB.1.toIsPreBrownianReal s t).mono_exponent
    (by norm_num)

/-- `B_t ∈ L²`. -/
theorem memLp_two_eval (hB : IsFilteredBrownianReal 𝓕 B P) (t : ℝ≥0) :
    MemLp (B t) 2 P := by
  have h := memLp_two hB 0 t
  refine h.ae_eq ?_
  filter_upwards [hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  rw [hω, sub_zero]

/-- **`E[1_A (B_t − B_s) | 𝓔] = 0`** for `A ∈ 𝓕_s` and `𝓔 ≤ 𝓕_s`. -/
theorem condExp_indicator_increment (hB : IsFilteredBrownianReal 𝓕 B P) {s t : ℝ≥0} (hst : s ≤ t)
    (h𝓔 : 𝓔 ≤ 𝓕 s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => B t ω - B s ω) | 𝓔] =ᵐ[P] 0 := by
  have hXm : StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance]
      (fun ω => B t ω - B s ω) := (comap_measurable _).stronglyMeasurable
  have hXi : Integrable (fun ω => B t ω - B s ω) P := (memLp_two hB s t).integrable (by norm_num)
  have hX0 : P[fun ω => B t ω - B s ω] = 0 := by
    rw [integral_sub (hB.1.toIsPreBrownianReal.integrable_eval t) (hB.1.toIsPreBrownianReal.integrable_eval s),
      hB.1.toIsPreBrownianReal.integral_eval, hB.1.toIsPreBrownianReal.integral_eval, sub_zero]
  have e : A.indicator (fun ω => B t ω - B s ω) = A.indicator 1 * fun ω => B t ω - B s ω := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  rw [e]
  exact condExp_mul_eq_zero h𝓔 (measurable_increment hB s t).comap_le (indep_increment hB hst) hXm hXi hX0
    (stronglyMeasurable_const.indicator hA) (e ▸ hXi.indicator (𝓕.le s A hA))

/-- **`E[1_A ((B_t − B_s)² − (t − s)) | 𝓔] = 0`** for `A ∈ 𝓕_s` and `𝓔 ≤ 𝓕_s`. -/
theorem condExp_indicator_increment_sq (hB : IsFilteredBrownianReal 𝓕 B P) {s t : ℝ≥0} (hst : s ≤ t)
    (h𝓔 : 𝓔 ≤ 𝓕 s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) | 𝓔] =ᵐ[P] 0 := by
  set X : Ω → ℝ := fun ω => (B t ω - B s ω) ^ 2 - ((t : ℝ) - s) with hXdef
  have hXm : StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance] X :=
    (((comap_measurable _).pow_const 2).sub_const _).stronglyMeasurable
  have hXi : Integrable X P := ((memLp_two hB s t).integrable_sq).sub (integrable_const _)
  have hX0 : P[X] = 0 := MathFin.QuadraticVariationL2.integral_increment_centered_mean
    hB.1.toIsPreBrownianReal hst
  have e : A.indicator X = A.indicator 1 * X := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  rw [e]
  exact condExp_mul_eq_zero h𝓔 (measurable_increment hB s t).comap_le (indep_increment hB hst) hXm hXi hX0
    (stronglyMeasurable_const.indicator hA) (e ▸ hXi.indicator (𝓕.le s A hA))

/-- **`E[1_A B_s (B_t − B_s) | 𝓔] = 0`** for `A ∈ 𝓕_s` and `𝓔 ≤ 𝓕_s`. -/
theorem condExp_indicator_mul_increment (hB : IsFilteredBrownianReal 𝓕 B P) {s t : ℝ≥0} (hst : s ≤ t)
    (h𝓔 : 𝓔 ≤ 𝓕 s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => B s ω * (B t ω - B s ω)) | 𝓔] =ᵐ[P] 0 := by
  have hXm : StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance]
      (fun ω => B t ω - B s ω) := (comap_measurable _).stronglyMeasurable
  have hXi : Integrable (fun ω => B t ω - B s ω) P := (memLp_two hB s t).integrable (by norm_num)
  have hX0 : P[fun ω => B t ω - B s ω] = 0 := by
    rw [integral_sub (hB.1.toIsPreBrownianReal.integrable_eval t) (hB.1.toIsPreBrownianReal.integrable_eval s),
      hB.1.toIsPreBrownianReal.integral_eval, hB.1.toIsPreBrownianReal.integral_eval, sub_zero]
  have hYm : StronglyMeasurable[𝓕 s] (A.indicator (B s)) := (hB.2.1 s).stronglyMeasurable.indicator hA
  have hprod : Integrable (fun ω => B s ω * (B t ω - B s ω)) P :=
    (memLp_two_eval hB s).integrable_mul (memLp_two hB s t)
  have e : A.indicator (fun ω => B s ω * (B t ω - B s ω)) = A.indicator (B s) * fun ω => B t ω - B s ω := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  rw [e]
  exact condExp_mul_eq_zero h𝓔 (measurable_increment hB s t).comap_le (indep_increment hB hst) hXm hXi hX0 hYm
    (e ▸ hprod.indicator (𝓕.le s A hA))

end Brownian

end Aux122Disint

end Sec7

end InteractingSLE
