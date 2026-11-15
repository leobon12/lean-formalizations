/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Ito.FiltrationBasic
import LQGMetric.Field.ZeroBoundaryLaw
import InteractingSLE.GFF.LocalSets.HittingSigma
import InteractingSLE.GFF.LocalSets.Basic

/-!
# Mixing two optional-hull couplings by an independent fair coin (§D.2.3)

Packet PROVE-AUX52-55. Source: §D.2.3 of `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38),
lines 2028–2042, and the mixture step in the proof of Aux. lemma 55 (`source/spec/p241-288.md` L224, p. 250: "if two
couplings gave different functions, mixing them by an independent fair coin would still satisfy the original hull
specification and optional locality").

"Mix two such couplings by an independent fair coin. The field and driving marginals remain fixed. The common optional
conditional kernels and the local-set conditional-independence criterion are preserved under this mixture."

For couplings on `(Ω₁, P₁)` and `(Ω₂, P₂)` the mixture lives on the disjoint union `Ω₁ ⊕ Ω₂` with the measure
`½ P₁ + ½ P₂` (`mixMeasure`); every random object is defined piecewise (`Sum.elim`). This file proves that the
mixture of two couplings satisfying the frozen optional hull specification `IsOptionalHullCoupling` (same `κ` and
force word) satisfies it again (`IsOptionalHullCoupling.mix`):

* laws: a variable has law `μ` under the mixture when it has law `μ` on both pieces (`HasLaw.mix`); this gives the
  Brownian finite-dimensional laws and, through the uniqueness of the zero-boundary GFF law
  (`LQGMetric.IsZBGFFProcess.map_eq`), the field marginal;
* the filtration of the evolution is the piecewise one (`sumFiltration`), in which the mixed Brownian motion has
  independent increments because both pieces give the increment the same Gaussian law;
* the frozen driving filtration of the mixture restricts to the driving filtrations of the pieces
  (`comap_inl_drivingFiltration_le`), so a stopping time of the mixture restricts to stopping times of the pieces,
  and so does its stopped σ-algebra;
* local sets: the frozen `IsLocalSet` is a statement about the joint law of the set and the field, realized by the
  mixture of the two realizations (`IsLocalSet.mix`);
* the kernel: on the event `E'` of `Coupling.exists_drivingStopped_measurable` (a stopped-σ-algebra version of the
  avoidance event on which the frozen right-hand side is measurable for the *mixture's* stopped σ-algebra), the set
  integrals of the field's conditional characteristic function split into the two pieces, where the frozen kernel
  holds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Determination

/-! ### The mixture measure on a disjoint union -/

section MixMeasure

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

theorem measurableEmbedding_inl : MeasurableEmbedding (Sum.inl : Ω₁ → Ω₁ ⊕ Ω₂) where
  injective := Sum.inl_injective
  measurable := measurable_inl
  measurableSet_image' s hs := by
    refine measurableSet_sum_iff.2 ⟨?_, ?_⟩
    · rwa [Set.preimage_image_eq _ Sum.inl_injective]
    · have : (Sum.inr ⁻¹' (Sum.inl '' s) : Set Ω₂) = ∅ := by ext x; simp
      rw [this]; exact MeasurableSet.empty

theorem measurableEmbedding_inr : MeasurableEmbedding (Sum.inr : Ω₂ → Ω₁ ⊕ Ω₂) where
  injective := Sum.inr_injective
  measurable := measurable_inr
  measurableSet_image' s hs := by
    refine measurableSet_sum_iff.2 ⟨?_, ?_⟩
    · have : (Sum.inl ⁻¹' (Sum.inr '' s) : Set Ω₁) = ∅ := by ext x; simp
      rw [this]; exact MeasurableSet.empty
    · rwa [Set.preimage_image_eq _ Sum.inr_injective]

/-- The mixture `½ P₁ + ½ P₂` of two measures, on the disjoint union. -/
def mixMeasure (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) : Measure (Ω₁ ⊕ Ω₂) :=
  (2⁻¹ : ℝ≥0∞) • P₁.map Sum.inl + (2⁻¹ : ℝ≥0∞) • P₂.map Sum.inr

variable {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}

theorem mixMeasure_apply (s : Set (Ω₁ ⊕ Ω₂)) :
    mixMeasure P₁ P₂ s = 2⁻¹ * P₁ (Sum.inl ⁻¹' s) + 2⁻¹ * P₂ (Sum.inr ⁻¹' s) := by
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measurableEmbedding_inl.map_apply, measurableEmbedding_inr.map_apply]

instance [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    IsProbabilityMeasure (mixMeasure P₁ P₂) := by
  constructor
  rw [mixMeasure_apply, Set.preimage_univ, Set.preimage_univ, measure_univ, measure_univ, mul_one,
    ENNReal.inv_two_add_inv_two]

theorem ae_mixMeasure_iff {p : Ω₁ ⊕ Ω₂ → Prop} :
    (∀ᵐ x ∂mixMeasure P₁ P₂, p x) ↔ (∀ᵐ ω ∂P₁, p (Sum.inl ω)) ∧ ∀ᵐ ω ∂P₂, p (Sum.inr ω) := by
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  rw [mixMeasure, ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff h2, Measure.ae_ennreal_smul_measure_iff h2,
    measurableEmbedding_inl.ae_map_iff, measurableEmbedding_inr.ae_map_iff]

theorem mixMeasure_eq_zero_iff {s : Set (Ω₁ ⊕ Ω₂)} :
    mixMeasure P₁ P₂ s = 0 ↔ P₁ (Sum.inl ⁻¹' s) = 0 ∧ P₂ (Sum.inr ⁻¹' s) = 0 := by
  rw [mixMeasure_apply]
  simp

theorem aemeasurable_mixMeasure_iff {γ : Type*} [MeasurableSpace γ] {f : Ω₁ ⊕ Ω₂ → γ} :
    AEMeasurable f (mixMeasure P₁ P₂) ↔ AEMeasurable (f ∘ Sum.inl) P₁ ∧ AEMeasurable (f ∘ Sum.inr) P₂ := by
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  rw [mixMeasure, aemeasurable_add_measure_iff, aemeasurable_smul_measure_iff h2,
    aemeasurable_smul_measure_iff h2, measurableEmbedding_inl.aemeasurable_map_iff,
    measurableEmbedding_inr.aemeasurable_map_iff]

theorem map_mixMeasure {γ : Type*} [MeasurableSpace γ] {f : Ω₁ ⊕ Ω₂ → γ}
    (hf : AEMeasurable f (mixMeasure P₁ P₂)) :
    (mixMeasure P₁ P₂).map f = (2⁻¹ : ℝ≥0∞) • P₁.map (f ∘ Sum.inl) + (2⁻¹ : ℝ≥0∞) • P₂.map (f ∘ Sum.inr) := by
  obtain ⟨h1, h2⟩ := aemeasurable_mixMeasure_iff.1 hf
  have hf₁ : AEMeasurable f (P₁.map Sum.inl) := measurableEmbedding_inl.aemeasurable_map_iff.2 h1
  have hf₂ : AEMeasurable f (P₂.map Sum.inr) := measurableEmbedding_inr.aemeasurable_map_iff.2 h2
  rw [mixMeasure, AEMeasurable.map_add₀ (hf₁.smul_measure _) (hf₂.smul_measure _), Measure.map_smul,
    Measure.map_smul, hf₁.map_map_of_aemeasurable measurable_inl.aemeasurable,
    hf₂.map_map_of_aemeasurable measurable_inr.aemeasurable]
  · exact hf₂
  · exact hf₁

/-- **Laws under a mixture**: a variable with the same law `μ` on both pieces has law `μ` under the mixture. -/
theorem HasLaw.mix {γ : Type*} [MeasurableSpace γ] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {f : Ω₁ ⊕ Ω₂ → γ} {μ : Measure γ} (h₁ : HasLaw (f ∘ Sum.inl) μ P₁) (h₂ : HasLaw (f ∘ Sum.inr) μ P₂) :
    HasLaw f μ (mixMeasure P₁ P₂) := by
  have hf : AEMeasurable f (mixMeasure P₁ P₂) :=
    aemeasurable_mixMeasure_iff.2 ⟨h₁.aemeasurable, h₂.aemeasurable⟩
  refine ⟨hf, ?_⟩
  rw [map_mixMeasure hf, h₁.map_eq, h₂.map_eq, ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]

theorem integrable_mixMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : Ω₁ ⊕ Ω₂ → E} :
    Integrable f (mixMeasure P₁ P₂) ↔ Integrable (f ∘ Sum.inl) P₁ ∧ Integrable (f ∘ Sum.inr) P₂ := by
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 two_ne_zero
  have h2' : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  rw [mixMeasure, integrable_add_measure, integrable_smul_measure h2' h2, integrable_smul_measure h2' h2,
    measurableEmbedding_inl.integrable_map_iff, measurableEmbedding_inr.integrable_map_iff]

theorem integral_mixMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ω₁ ⊕ Ω₂ → E}
    (hf : Integrable f (mixMeasure P₁ P₂)) :
    ∫ x, f x ∂mixMeasure P₁ P₂ = (2⁻¹ : ℝ) • ∫ ω, f (Sum.inl ω) ∂P₁ + (2⁻¹ : ℝ) • ∫ ω, f (Sum.inr ω) ∂P₂ := by
  have h2 : ((2⁻¹ : ℝ≥0∞)).toReal = 2⁻¹ := by simp
  rw [mixMeasure] at hf ⊢
  rw [integral_add_measure (integrable_add_measure.1 hf).1 (integrable_add_measure.1 hf).2,
    integral_smul_measure, integral_smul_measure, h2, measurableEmbedding_inl.integral_map,
    measurableEmbedding_inr.integral_map]

/-- Two indicator integrals under the mixture agree when they agree on both pieces. -/
theorem integral_indicator_mixMeasure_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Ω₁ ⊕ Ω₂ → E} {T : Set (Ω₁ ⊕ Ω₂)} (hf : Integrable (T.indicator f) (mixMeasure P₁ P₂))
    (hg : Integrable (T.indicator g) (mixMeasure P₁ P₂))
    (h₁ : ∫ ω, (Sum.inl ⁻¹' T).indicator (f ∘ Sum.inl) ω ∂P₁ = ∫ ω, (Sum.inl ⁻¹' T).indicator (g ∘ Sum.inl) ω ∂P₁)
    (h₂ : ∫ ω, (Sum.inr ⁻¹' T).indicator (f ∘ Sum.inr) ω ∂P₂ = ∫ ω, (Sum.inr ⁻¹' T).indicator (g ∘ Sum.inr) ω ∂P₂) :
    ∫ x, T.indicator f x ∂mixMeasure P₁ P₂ = ∫ x, T.indicator g x ∂mixMeasure P₁ P₂ := by
  rw [integral_mixMeasure hf, integral_mixMeasure hg]
  have c₁ : ∀ Y : Ω₁ ⊕ Ω₂ → E, (fun ω => T.indicator Y (Sum.inl ω)) = (Sum.inl ⁻¹' T).indicator (Y ∘ Sum.inl) :=
    fun Y => funext fun ω => (Set.indicator_comp_right (s := T) (g := Y) (x := ω) Sum.inl).symm
  have c₂ : ∀ Y : Ω₁ ⊕ Ω₂ → E, (fun ω => T.indicator Y (Sum.inr ω)) = (Sum.inr ⁻¹' T).indicator (Y ∘ Sum.inr) :=
    fun Y => funext fun ω => (Set.indicator_comp_right (s := T) (g := Y) (x := ω) Sum.inr).symm
  change (2⁻¹ : ℝ) • ∫ ω, (fun ω => T.indicator f (Sum.inl ω)) ω ∂P₁ +
      (2⁻¹ : ℝ) • ∫ ω, (fun ω => T.indicator f (Sum.inr ω)) ω ∂P₂ =
    (2⁻¹ : ℝ) • ∫ ω, (fun ω => T.indicator g (Sum.inl ω)) ω ∂P₁ +
      (2⁻¹ : ℝ) • ∫ ω, (fun ω => T.indicator g (Sum.inr ω)) ω ∂P₂
  rw [c₁ f, c₁ g, c₂ f, c₂ g, h₁, h₂]

theorem integrable_indicator_mixMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : Ω₁ ⊕ Ω₂ → E}
    {T : Set (Ω₁ ⊕ Ω₂)} :
    Integrable (T.indicator f) (mixMeasure P₁ P₂) ↔
      Integrable ((Sum.inl ⁻¹' T).indicator (f ∘ Sum.inl)) P₁ ∧
        Integrable ((Sum.inr ⁻¹' T).indicator (f ∘ Sum.inr)) P₂ := by
  rw [integrable_mixMeasure_iff]
  rfl

end MixMeasure

/-! ### The piecewise filtration and the evolution under the mixture -/

section Evolution

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- The filtration of the mixture: an event is in it at time `t` when both of its pieces are. -/
def sumFiltration (𝓕₁ : Filtration ℝ≥0 m₁) (𝓕₂ : Filtration ℝ≥0 m₂) :
    Filtration ℝ≥0 (@Sum.instMeasurableSpace Ω₁ Ω₂ m₁ m₂) where
  seq t := (𝓕₁ t).map Sum.inl ⊓ (𝓕₂ t).map Sum.inr
  mono' _ _ hst := inf_le_inf (MeasurableSpace.map_mono (𝓕₁.mono hst)) (MeasurableSpace.map_mono (𝓕₂.mono hst))
  le' t := inf_le_inf (MeasurableSpace.map_mono (𝓕₁.le t)) (MeasurableSpace.map_mono (𝓕₂.le t))

theorem measurableSet_sumFiltration_iff {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {t : ℝ≥0}
    {s : Set (Ω₁ ⊕ Ω₂)} :
    MeasurableSet[sumFiltration 𝓕₁ 𝓕₂ t] s ↔
      MeasurableSet[𝓕₁ t] (Sum.inl ⁻¹' s) ∧ MeasurableSet[𝓕₂ t] (Sum.inr ⁻¹' s) :=
  Iff.rfl

/-- A process defined piecewise from adapted processes is adapted to the piecewise filtration. -/
theorem measurable_sumFiltration {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {t : ℝ≥0}
    {γ : Type*} [MeasurableSpace γ] {X₁ : Ω₁ → γ} {X₂ : Ω₂ → γ} (h₁ : Measurable[𝓕₁ t] X₁)
    (h₂ : Measurable[𝓕₂ t] X₂) :
    Measurable[sumFiltration 𝓕₁ 𝓕₂ t] (Sum.elim X₁ X₂) :=
  @measurable_fun_sum Ω₁ Ω₂ γ (𝓕₁ t) (𝓕₂ t) _ (Sum.elim X₁ X₂) h₁ h₂

variable {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]

/-- **The mixed Brownian motion** is a Brownian motion of the piecewise filtration: its laws are those of both
pieces, and an increment, whose law is the same `N(0, t − s)` on both pieces, is independent of the past. -/
theorem IsFilteredBrownianReal.mix {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} (h₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁)
    (h₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) :
    IsFilteredBrownianReal (sumFiltration 𝓕₁ 𝓕₂) (fun t => Sum.elim (B₁ t) (B₂ t)) (mixMeasure P₁ P₂) := by
  obtain ⟨hb₁, ha₁, hi₁⟩ := h₁
  obtain ⟨hb₂, ha₂, hi₂⟩ := h₂
  refine ⟨⟨⟨fun I => HasLaw.mix (hb₁.hasLaw I) (hb₂.hasLaw I)⟩, ae_mixMeasure_iff.2 ⟨hb₁.cont, hb₂.cont⟩⟩,
    fun t => measurable_sumFiltration (ha₁ t) (ha₂ t), fun s t hst => ?_⟩
  rw [Indep_iff]
  rintro _ T ⟨S, hS, rfl⟩ hT
  have hL₁ := hb₁.hasLaw_sub t s
  have hL₂ := hb₂.hasLaw_sub t s
  have e₁ : P₁ ((fun ω => B₁ t ω - B₁ s ω) ⁻¹' S) = gaussianReal 0 (nndist t.1 s.1) S := by
    rw [← hL₁.map_eq, Measure.map_apply_of_aemeasurable hL₁.aemeasurable hS]; rfl
  have e₂ : P₂ ((fun ω => B₂ t ω - B₂ s ω) ⁻¹' S) = gaussianReal 0 (nndist t.1 s.1) S := by
    rw [← hL₂.map_eq, Measure.map_apply_of_aemeasurable hL₂.aemeasurable hS]; rfl
  have i₁ := (Indep_iff _ _ _).1 (hi₁ s t hst) _ _ ⟨S, hS, rfl⟩ hT.1
  have i₂ := (Indep_iff _ _ _).1 (hi₂ s t hst) _ _ ⟨S, hS, rfl⟩ hT.2
  rw [mixMeasure_apply, mixMeasure_apply, mixMeasure_apply]
  simp only [Set.preimage_inter] at i₁ i₂ ⊢
  change 2⁻¹ * P₁ ((fun ω => B₁ t ω - B₁ s ω) ⁻¹' S ∩ Sum.inl ⁻¹' T) +
      2⁻¹ * P₂ ((fun ω => B₂ t ω - B₂ s ω) ⁻¹' S ∩ Sum.inr ⁻¹' T) =
    (2⁻¹ * P₁ ((fun ω => B₁ t ω - B₁ s ω) ⁻¹' S) + 2⁻¹ * P₂ ((fun ω => B₂ t ω - B₂ s ω) ⁻¹' S)) *
      (2⁻¹ * P₁ (Sum.inl ⁻¹' T) + 2⁻¹ * P₂ (Sum.inr ⁻¹' T))
  rw [i₁, i₂, e₁, e₂, ← mul_add, ← two_mul,
    ← mul_assoc (2 : ℝ≥0∞), ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  ring

/-- Adaptedness before the lifetime, piecewise. -/
theorem AdaptedBefore.mix {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {ζ₁ : Ω₁ → ℝ≥0∞}
    {ζ₂ : Ω₂ → ℝ≥0∞} {X₁ : ℝ≥0 → Ω₁ → ℝ} {X₂ : ℝ≥0 → Ω₂ → ℝ} (h₁ : AdaptedBefore 𝓕₁ ζ₁ X₁)
    (h₂ : AdaptedBefore 𝓕₂ ζ₂ X₂) :
    AdaptedBefore (sumFiltration 𝓕₁ 𝓕₂) (Sum.elim ζ₁ ζ₂) (fun t => Sum.elim (X₁ t) (X₂ t)) :=
  fun t A hA => ⟨h₁ t A hA, h₂ t A hA⟩

end Evolution

/-! ### The zero-boundary GFF is a statement about a law -/

section GFF

open LQGMetric

variable {U : Opens ℂ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

/-- A process with the law of a zero-boundary GFF process is a zero-boundary GFF process. -/
theorem isZBGFFProcess_of_hasLaw {X : TestOn U → Ω → ℝ} {X' : TestOn U → Ω' → ℝ}
    (hX' : IsZBGFFProcess U X' P') (hXm : ∀ φ, Measurable (X φ))
    (hlaw : HasLaw (zbPath X) (P'.map (zbPath X')) P) : IsZBGFFProcess U X P := by
  have hm' : Measurable (zbPath X') := measurable_pi_iff.2 hX'.measurable
  have hL' : HasLaw (zbPath X') (P'.map (zbPath X')) P' := hasLaw_map hm'.aemeasurable
  have hev : ∀ φ : TestOn U, Measurable fun f : TestOn U → ℝ => f φ := fun φ => measurable_pi_apply φ
  refine ⟨hXm, ⟨fun I => ⟨?_, ?_⟩⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · exact (Finset.measurable_restrict I).comp_aemeasurable hlaw.aemeasurable
  · have hg := (hX'.gaussian.hasGaussianLaw I).isGaussian_map
    have e : P.map (fun ω => I.restrict (X · ω)) = P'.map (fun ω => I.restrict (X' · ω)) := by
      change P.map (I.restrict ∘ zbPath X) = P'.map (I.restrict ∘ zbPath X')
      rw [← Measure.map_map (Finset.measurable_restrict I) hm', ← hlaw.map_eq,
        AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hlaw.aemeasurable]
    rw [e]; exact hg
  · have h1 := hlaw.integral_comp (hev φ).aestronglyMeasurable
    have h2 := hL'.integral_comp (hev φ).aestronglyMeasurable
    change P[(fun f : TestOn U → ℝ => f φ) ∘ zbPath X] = 0
    rw [h1, ← h2]
    exact hX'.centered φ
  · have h1 := hlaw.covariance_comp (hev φ).aemeasurable (hev ψ).aemeasurable
    have h2 := hL'.covariance_comp (hev φ).aemeasurable (hev ψ).aemeasurable
    change cov[(fun f : TestOn U → ℝ => f φ) ∘ zbPath X, (fun f : TestOn U → ℝ => f ψ) ∘ zbPath X; P] = _
    rw [h1, ← h2]
    exact hX'.covariance_eq φ ψ

/-- **The field marginal under a mixture**: mixing two zero-boundary GFF processes gives one. -/
theorem IsZBGFFProcess.mix {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X : TestOn U → Ω₁ ⊕ Ω₂ → ℝ} (h₁ : IsZBGFFProcess U (fun φ ω => X φ (Sum.inl ω)) P₁)
    (h₂ : IsZBGFFProcess U (fun φ ω => X φ (Sum.inr ω)) P₂) :
    IsZBGFFProcess U X (mixMeasure P₁ P₂) := by
  have hm₁ : Measurable (zbPath fun φ ω => X φ (Sum.inl ω)) := measurable_pi_iff.2 h₁.measurable
  have hm₂ : Measurable (zbPath fun φ ω => X φ (Sum.inr ω)) := measurable_pi_iff.2 h₂.measurable
  refine isZBGFFProcess_of_hasLaw h₁ (fun φ => measurable_fun_sum (h₁.measurable φ) (h₂.measurable φ)) ?_
  refine HasLaw.mix (hasLaw_map hm₁.aemeasurable) ⟨hm₂.aemeasurable, ?_⟩
  exact (h₂.map_eq h₁)

end GFF

/-! ### Restricting the frozen driving filtration to a piece -/

section Restrict

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The usual augmentation is compatible with a measurable map that pulls null sets back to null sets. -/
theorem comap_usualAugmentation_le {f : α → β} (hf : Measurable f) {𝓕 : Filtration ℝ≥0 mβ}
    {𝓖 : Filtration ℝ≥0 mα} {P : Measure β} {Q : Measure α} (h𝓕 : ∀ t, (𝓕 t).comap f ≤ 𝓖 t)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → Q (f ⁻¹' s) = 0) (t : ℝ≥0) :
    (usualAugmentation 𝓕 P t).comap f ≤ usualAugmentation 𝓖 Q t := by
  rw [Ito.usualAugmentation_apply, Ito.usualAugmentation_apply]
  refine le_iInf₂ fun v hv => ?_
  refine (MeasurableSpace.comap_mono (iInf₂_le v hv)).trans ?_
  rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply, MeasurableSpace.comap_sup]
  refine sup_le_sup (h𝓕 v) ?_
  rw [Ito.nullSets, Ito.nullSets, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨s, ⟨hs, h0⟩, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom ⟨hf hs, hnull s hs h0⟩

/-- A stopping time composed with a map that pulls the filtration back into another is a stopping time. -/
theorem IsStoppingTime.comp_of_comap_le {f : α → β} {𝓕 : Filtration ℝ≥0 mβ} {𝓖 : Filtration ℝ≥0 mα}
    (h : ∀ t, (𝓕 t).comap f ≤ 𝓖 t) {τ : β → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    IsStoppingTime 𝓖 (τ ∘ f) :=
  fun t => h t _ ⟨_, hτ t, rfl⟩

/-- The stopped σ-algebras are compatible with such a map. -/
theorem IsStoppingTime.comap_measurableSpace_le {f : α → β} {𝓕 : Filtration ℝ≥0 mβ}
    {𝓖 : Filtration ℝ≥0 mα} (h : ∀ t, (𝓕 t).comap f ≤ 𝓖 t) {τ : β → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) :
    hτ.measurableSpace.comap f ≤ (IsStoppingTime.comp_of_comap_le h hτ).measurableSpace := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨?_, fun i => ?_⟩
  · have h1 : (⨆ t, 𝓕 t).comap f ≤ ⨆ t, 𝓖 t := by
      rw [MeasurableSpace.comap_iSup]; exact iSup_mono h
    exact h1 _ ⟨s, hs.1, rfl⟩
  · have e : f ⁻¹' s ∩ {ω | (τ ∘ f) ω ≤ i} = f ⁻¹' (s ∩ {ω | τ ω ≤ i}) := rfl
    rw [e]
    exact h i _ ⟨_, hs.2 i, rfl⟩

end Restrict

/-! ### Local sets under a mixture -/

section LocalSet

open LQGMetric

/-- The conditional characteristic function of a test pairing is integrable. -/
theorem integrable_cexp_pairing {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {l : Ω → DistOn upperHalfPlaneOpens} (hl : Measurable l) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Complex.exp (Complex.I * (l ω φ : ℂ))) P := by
  have hm : Measurable fun ω => l ω φ := (measurable_pi_apply φ).comp ((measurable_distEval _).comp hl)
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hm))).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Complex.norm_exp_I_mul_ofReal]

/-- The cylinder σ-algebra of the distribution space. -/
abbrev mDist : MeasurableSpace (DistOn upperHalfPlaneOpens) := inferInstance

/-- The σ-algebra generated by a random set (hitting σ-algebra) and a random distribution, as in `IsLocalSet`. -/
@[instance_reducible]
def setDistSigma {Ω : Type*} (A : Ω → Set ℂ) (k : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  MeasurableSpace.comap A hittingSigma ⊔ MeasurableSpace.comap k mDist

theorem setDistSigma_le {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ} {k : Ω → DistOn upperHalfPlaneOpens}
    (hA : @Measurable _ _ _ hittingSigma A) (hk : Measurable k) : setDistSigma A k ≤ ‹MeasurableSpace Ω› := by
  refine sup_le ?_ ?_ <;> rintro _ ⟨t, ht, rfl⟩
  exacts [hA ht, hk ht]

theorem comap_setDistSigma {Ω Ω' : Type*} (f : Ω' → Ω) (A : Ω → Set ℂ) (k : Ω → DistOn upperHalfPlaneOpens) :
    (setDistSigma A k).comap f = setDistSigma (A ∘ f) (k ∘ f) := by
  rw [setDistSigma, setDistSigma, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]

/-- **Local sets under a mixture.** The frozen `IsLocalSet` is a statement about the joint law of the set and the
field; the mixture of two realizations realizes the mixture law. The conditional Gaussian kernel of the
realization is a measurable function of the set (`LocalSets.measurable_zeroGFFTestCov_compl`), common to both
pieces, so it survives the mixture although the coin is not observed. -/
theorem IsLocalSet.mix {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {A : Ω₁ ⊕ Ω₂ → Set ℂ} {h : Ω₁ ⊕ Ω₂ → DistOn upperHalfPlaneOpens}
    (h₁ : IsLocalSet (A ∘ Sum.inl) (h ∘ Sum.inl) P₁) (h₂ : IsLocalSet (A ∘ Sum.inr) (h ∘ Sum.inr) P₂) :
    IsLocalSet A h (mixMeasure P₁ P₂) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨am₁, as₁, Ω'₁, _, Q₁, _, A₁, k₁, l₁, hA₁, hk₁, hl₁, hpt₁, hharm₁, hcond₁, hlaw₁⟩ := h₁
  obtain ⟨am₂, as₂, Ω'₂, _, Q₂, _, A₂, k₂, l₂, hA₂, hk₂, hl₂, hpt₂, hharm₂, hcond₂, hlaw₂⟩ := h₂
  have hA : @Measurable _ _ _ hittingSigma (Sum.elim A₁ A₂) := measurable_fun_sum hA₁ hA₂
  have hk : Measurable (Sum.elim k₁ k₂) := measurable_fun_sum hk₁ hk₂
  have hl : Measurable (Sum.elim l₁ l₂) := measurable_fun_sum hl₁ hl₂
  have hpt : ∀ x, Sum.elim A₁ A₂ x ⊆ QuantumZipper.H ∧ IsOpen (QuantumZipper.H \ Sum.elim A₁ A₂ x) := by
    rintro (ω | ω)
    exacts [hpt₁ ω, hpt₂ ω]
  refine ⟨aemeasurable_mixMeasure_iff.2 ⟨am₁, am₂⟩, ae_mixMeasure_iff.2 ⟨as₁, as₂⟩, Ω'₁ ⊕ Ω'₂, inferInstance,
    mixMeasure Q₁ Q₂, inferInstance, Sum.elim A₁ A₂, Sum.elim k₁ k₂, Sum.elim l₁ l₂, hA, hk, hl, hpt,
    ae_mixMeasure_iff.2 ⟨hharm₁, hharm₂⟩, fun φ => ?_, ?_⟩
  · -- the conditional Gaussian kernel of the mixed realization
    have h𝒢le := setDistSigma_le hA hk
    have hcomap₁ := comap_setDistSigma Sum.inl (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)
    have hcomap₂ := comap_setDistSigma Sum.inr (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)
    set K : Ω'₁ ⊕ Ω'₂ → ℂ := fun x =>
      ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (QuantumZipper.H \ Sum.elim A₁ A₂ x) φ φ) : ℝ) : ℂ)
      with hK
    have hKm : Measurable[setDistSigma (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)] K := by
      have e : K = (fun S : Set ℂ => ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
          (QuantumZipper.H \ LocalSets.relClosureH S) φ φ) : ℝ) : ℂ)) ∘ Sum.elim A₁ A₂ := by
        funext x
        simp only [hK, Function.comp_apply, LocalSets.relClosureH_eq (hpt x).1 (hpt x).2]
      rw [e]
      refine Measurable.comp ?_ (Measurable.mono (Measurable.of_comap_le le_rfl) le_sup_left le_rfl)
      exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (LocalSets.measurable_zeroGFFTestCov_compl φ φ)))
    set X : Ω'₁ ⊕ Ω'₂ → ℂ := fun x => Complex.exp (Complex.I * (Sum.elim l₁ l₂ x φ : ℂ)) with hX
    have hXi : Integrable X (mixMeasure Q₁ Q₂) := integrable_cexp_pairing hl φ
    have hX₁ : Integrable (fun ω => Complex.exp (Complex.I * (l₁ ω φ : ℂ))) Q₁ := integrable_cexp_pairing hl₁ φ
    have hX₂ : Integrable (fun ω => Complex.exp (Complex.I * (l₂ ω φ : ℂ))) Q₂ := integrable_cexp_pairing hl₂ φ
    have hKi : Integrable K (mixMeasure Q₁ Q₂) := by
      refine integrable_mixMeasure_iff.2 ⟨?_, ?_⟩
      · exact (integrable_condExp).congr (hcond₁ φ)
      · exact (integrable_condExp).congr (hcond₂ φ)
    have key : ∀ s, MeasurableSet[setDistSigma (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)] s →
        ∫ x in s, K x ∂mixMeasure Q₁ Q₂ = ∫ x in s, X x ∂mixMeasure Q₁ Q₂ := by
      intro s hs
      have hs₁ : MeasurableSet[setDistSigma A₁ k₁] (Sum.inl ⁻¹' s) := by
        have h' : MeasurableSet[(setDistSigma (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)).comap Sum.inl] (Sum.inl ⁻¹' s) :=
          ⟨s, hs, rfl⟩
        rwa [hcomap₁] at h'
      have hs₂ : MeasurableSet[setDistSigma A₂ k₂] (Sum.inr ⁻¹' s) := by
        have h' : MeasurableSet[(setDistSigma (Sum.elim A₁ A₂) (Sum.elim k₁ k₂)).comap Sum.inr] (Sum.inr ⁻¹' s) :=
          ⟨s, hs, rfl⟩
        rwa [hcomap₂] at h'
      have hle₁ := setDistSigma_le hA₁ hk₁
      have hle₂ := setDistSigma_le hA₂ hk₂
      have e₁ : ∫ ω in Sum.inl ⁻¹' s, K (Sum.inl ω) ∂Q₁ =
          ∫ ω in Sum.inl ⁻¹' s, Complex.exp (Complex.I * (l₁ ω φ : ℂ)) ∂Q₁ := by
        rw [← setIntegral_condExp hle₁ hX₁ hs₁]
        exact setIntegral_congr_ae (hle₁ _ hs₁) ((hcond₁ φ).mono fun ω hω _ => hω.symm)
      have e₂ : ∫ ω in Sum.inr ⁻¹' s, K (Sum.inr ω) ∂Q₂ =
          ∫ ω in Sum.inr ⁻¹' s, Complex.exp (Complex.I * (l₂ ω φ : ℂ)) ∂Q₂ := by
        rw [← setIntegral_condExp hle₂ hX₂ hs₂]
        exact setIntegral_congr_ae (hle₂ _ hs₂) ((hcond₂ φ).mono fun ω hω _ => hω.symm)
      have hsm : MeasurableSet s := h𝒢le _ hs
      rw [← integral_indicator hsm, ← integral_indicator hsm, integral_mixMeasure (hKi.indicator hsm),
        integral_mixMeasure (hXi.indicator hsm)]
      rw [← integral_indicator (hle₁ _ hs₁), ← integral_indicator (hle₁ _ hs₁)] at e₁
      rw [← integral_indicator (hle₂ _ hs₂), ← integral_indicator (hle₂ _ hs₂)] at e₂
      have c₁ : ∀ (Y : Ω'₁ ⊕ Ω'₂ → ℂ), (fun ω => s.indicator Y (Sum.inl ω)) =
          (Sum.inl ⁻¹' s).indicator (fun ω => Y (Sum.inl ω)) :=
        fun Y => funext fun ω => (Set.indicator_comp_right (s := s) (g := Y) (x := ω) Sum.inl).symm
      have c₂ : ∀ (Y : Ω'₁ ⊕ Ω'₂ → ℂ), (fun ω => s.indicator Y (Sum.inr ω)) =
          (Sum.inr ⁻¹' s).indicator (fun ω => Y (Sum.inr ω)) :=
        fun Y => funext fun ω => (Set.indicator_comp_right (s := s) (g := Y) (x := ω) Sum.inr).symm
      rw [c₁ K, c₁ X, c₂ K, c₂ X, e₁, e₂]
      rfl
    have hae := ae_eq_condExp_of_forall_setIntegral_eq h𝒢le hXi (fun s _ _ => hKi.integrableOn)
      (fun s hs _ => key s hs) hKm.stronglyMeasurable.aestronglyMeasurable
    exact hae.symm
  · -- the law of the mixed realization
    have hZ : Measurable fun x => (Sum.elim A₁ A₂ x, Sum.elim k₁ k₂ x + Sum.elim l₁ l₂ x) :=
      hA.prodMk ((GFF.measurable_add_distOn _).comp (hk.prodMk hl))
    rw [map_mixMeasure hZ.aemeasurable, map_mixMeasure (aemeasurable_mixMeasure_iff.2 ⟨am₁, am₂⟩)]
    exact congrArg₂ (fun a b => (2⁻¹ : ℝ≥0∞) • a + (2⁻¹ : ℝ≥0∞) • b) hlaw₁ hlaw₂

end LocalSet

/-! ### The coupling under a mixture -/

section Coupling

open LQGMetric QuantumZipper Coupling

/-- A process defined piecewise on the disjoint union. -/
def mixProc {Ω₁ Ω₂ γ : Type*} (X₁ : ℝ≥0 → Ω₁ → γ) (X₂ : ℝ≥0 → Ω₂ → γ) : ℝ≥0 → Ω₁ ⊕ Ω₂ → γ :=
  fun t => Sum.elim (X₁ t) (X₂ t)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
  {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **The integrated evolution under a mixture.** -/
theorem IsIntegratedSLEEvolution.mix [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (e₁ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (e₂ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR (mixMeasure P₁ P₂) (sumFiltration 𝓕₁ 𝓕₂) (mixProc W₁ W₂)
      (fun i => mixProc (VL₁ i) (VL₂ i)) (fun i => mixProc (VR₁ i) (VR₂ i)) (mixProc B₁ B₂)
      (Sum.elim ζ₁ ζ₂) :=
  ⟨IsFilteredBrownianReal.mix e₁.1 e₂.1, AdaptedBefore.mix e₁.2.1 e₂.2.1,
    fun i => AdaptedBefore.mix (e₁.2.2.1 i) (e₂.2.2.1 i), fun i => AdaptedBefore.mix (e₁.2.2.2.1 i) (e₂.2.2.2.1 i),
    ae_mixMeasure_iff.2 ⟨e₁.2.2.2.2, e₂.2.2.2.2⟩⟩

theorem IsMeasurableKilledDriving.mix (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂) :
    IsMeasurableKilledDriving (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂) :=
  fun r A hA => measurableSet_sum_iff.2 ⟨hX₁ r A hA, hX₂ r A hA⟩

theorem comap_inl_killedDrivingFiltration_le (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    (hX : IsMeasurableKilledDriving (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂)) (t : ℝ≥0) :
    (killedDrivingFiltration hX t).comap Sum.inl ≤ killedDrivingFiltration hX₁ t := by
  change (killedDrivingSigma _ _ _ _ t).comap Sum.inl ≤ killedDrivingSigma _ _ _ _ t
  rw [killedDrivingSigma, killedDrivingSigma, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨E, ⟨r, hr, A, hA, rfl⟩, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom ⟨r, hr, A, hA, rfl⟩

theorem comap_inr_killedDrivingFiltration_le (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hX : IsMeasurableKilledDriving (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂)) (t : ℝ≥0) :
    (killedDrivingFiltration hX t).comap Sum.inr ≤ killedDrivingFiltration hX₂ t := by
  change (killedDrivingSigma _ _ _ _ t).comap Sum.inr ≤ killedDrivingSigma _ _ _ _ t
  rw [killedDrivingSigma, killedDrivingSigma, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨E, ⟨r, hr, A, hA, rfl⟩, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom ⟨r, hr, A, hA, rfl⟩

/-- **The frozen driving filtration of the mixture restricts to that of the first piece.** -/
theorem comap_inl_drivingFiltration_le (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    (hX : IsMeasurableKilledDriving (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂)) (t : ℝ≥0) :
    (drivingFiltration (mixMeasure P₁ P₂) hX t).comap Sum.inl ≤ drivingFiltration P₁ hX₁ t :=
  comap_usualAugmentation_le measurable_inl (comap_inl_killedDrivingFiltration_le hX₁ hX)
    (fun _ _ h0 => (mixMeasure_eq_zero_iff.1 h0).1) t

/-- **The frozen driving filtration of the mixture restricts to that of the second piece.** -/
theorem comap_inr_drivingFiltration_le (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hX : IsMeasurableKilledDriving (mixProc W₁ W₂) (fun i => mixProc (VL₁ i) (VL₂ i))
      (fun i => mixProc (VR₁ i) (VR₂ i)) (Sum.elim ζ₁ ζ₂)) (t : ℝ≥0) :
    (drivingFiltration (mixMeasure P₁ P₂) hX t).comap Sum.inr ≤ drivingFiltration P₂ hX₂ t :=
  comap_usualAugmentation_le measurable_inr (comap_inr_killedDrivingFiltration_le hX₂ hX)
    (fun _ _ h0 => (mixMeasure_eq_zero_iff.1 h0).2) t

/-- **The optional hull specification survives the mixture** (§D.2.3: "The field and driving marginals remain fixed.
The common optional conditional kernels and the local-set conditional-independence criterion are preserved under
this mixture"). -/
theorem IsOptionalHullCoupling.mix [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    IsOptionalHullCoupling κ xL xR ρL ρR (mixMeasure P₁ P₂) (sumFiltration 𝓕₁ 𝓕₂) (mixProc W₁ W₂)
      (fun i => mixProc (VL₁ i) (VL₂ i)) (fun i => mixProc (VR₁ i) (VR₂ i)) (mixProc B₁ B₂)
      (Sum.elim ζ₁ ζ₂) (Sum.elim h₁ h₂) := by
  obtain ⟨e₁, hh₁, hg₁, hX₁, hK₁⟩ := hC₁
  obtain ⟨e₂, hh₂, hg₂, hX₂, hK₂⟩ := hC₂
  have hE := IsIntegratedSLEEvolution.mix e₁ e₂
  have hX := IsMeasurableKilledDriving.mix hX₁ hX₂
  have hh : Measurable (Sum.elim h₁ h₂) := measurable_fun_sum hh₁ hh₂
  refine ⟨hE, hh, fun u₀ hu₀ => IsZBGFFProcess.mix (hg₁ u₀ hu₀) (hg₂ u₀ hu₀), hX, fun τ hτ hτζ => ?_⟩
  have hτ₁ := IsStoppingTime.comp_of_comap_le (comap_inl_drivingFiltration_le hX₁ hX) hτ
  have hτ₂ := IsStoppingTime.comp_of_comap_le (comap_inr_drivingFiltration_le hX₂ hX) hτ
  obtain ⟨hτζ₁, hτζ₂⟩ := ae_mixMeasure_iff.1 hτζ
  obtain ⟨hL₁, hk₁⟩ := hK₁ (τ ∘ Sum.inl) hτ₁ hτζ₁
  obtain ⟨hL₂, hk₂⟩ := hK₂ (τ ∘ Sum.inr) hτ₂ hτζ₂
  refine ⟨IsLocalSet.mix hL₁ hL₂, fun u hu φ => ?_⟩
  have k₁ := hk₁ (u ∘ Sum.inl) (fun ω => hu (Sum.inl ω)) φ
  have k₂ := hk₂ (u ∘ Sum.inr) (fun ω => hu (Sum.inr ω)) φ
  obtain ⟨E', hE'm, hE'D, hDE', -, -, hE'R⟩ := exists_drivingStopped_measurable hE hX φ hτ hτζ u hu
  set X : Ω₁ ⊕ Ω₂ → ℂ := fun x => Complex.exp (Complex.I * (Sum.elim h₁ h₂ x φ : ℂ)) with hXdef
  set R : Ω₁ ⊕ Ω₂ → ℂ := frozenRHS κ (mixProc W₁ W₂) u φ (fun x => (τ x).untopD 0) with hRdef
  have hm := hτ.measurableSpace_le
  have hXi : Integrable X (mixMeasure P₁ P₂) := integrable_cexp_pairing hh φ
  -- the two pieces
  have piece₁ : ∀ S, MeasurableSet[hτ.measurableSpace] S →
      Integrable ((Sum.inl ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inl)) P₁ ∧
      ∫ ω, (Sum.inl ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inl) ω ∂P₁ =
        ∫ ω, (Sum.inl ⁻¹' (S ∩ E')).indicator (X ∘ Sum.inl) ω ∂P₁ := by
    intro S hS
    have hS₁ : MeasurableSet[hτ₁.measurableSpace] (Sum.inl ⁻¹' (S ∩ E')) :=
      IsStoppingTime.comap_measurableSpace_le (comap_inl_drivingFiltration_le hX₁ hX) hτ _
        ⟨_, hS.inter hE'm, rfl⟩
    have hle₁ := hτ₁.measurableSpace_le
    have hX₁i : Integrable (X ∘ Sum.inl) P₁ := integrable_cexp_pairing hh₁ φ
    have ae₁ : (Sum.inl ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inl) =ᵐ[P₁]
        (Sum.inl ⁻¹' (S ∩ E')).indicator (condExp hτ₁.measurableSpace P₁ (X ∘ Sum.inl)) := by
      filter_upwards [k₁] with ω hω
      by_cases hωS : ω ∈ Sum.inl ⁻¹' (S ∩ E')
      · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS]
        have h0 : Sum.inl ω ∈ E' := hωS.2
        have h1 := hE'D h0
        simp only [Set.mem_ofPred_eq] at h1
        have hD : Disjoint (tsupport (φ : ℂ → ℝ))
            (fwdHull (fun s : ℝ => W₁ s.toNNReal ω) (((τ (Sum.inl ω)).untopD 0 : ℝ≥0) : ℝ)) := h1
        have e1 := hω hD
        show frozenRHS κ W₁ (u ∘ Sum.inl) φ (fun ω => (τ (Sum.inl ω)).untopD 0) ω =
          condExp hτ₁.measurableSpace P₁ (fun ω' => Complex.exp (Complex.I * (h₁ ω' φ : ℂ))) ω
        exact e1.symm
      · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
    refine ⟨(integrable_condExp.indicator (hle₁ _ hS₁)).congr ae₁.symm, ?_⟩
    rw [integral_congr_ae ae₁, integral_indicator (hle₁ _ hS₁), integral_indicator (hle₁ _ hS₁),
      setIntegral_condExp hle₁ hX₁i hS₁]
  have piece₂ : ∀ S, MeasurableSet[hτ.measurableSpace] S →
      Integrable ((Sum.inr ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inr)) P₂ ∧
      ∫ ω, (Sum.inr ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inr) ω ∂P₂ =
        ∫ ω, (Sum.inr ⁻¹' (S ∩ E')).indicator (X ∘ Sum.inr) ω ∂P₂ := by
    intro S hS
    have hS₂ : MeasurableSet[hτ₂.measurableSpace] (Sum.inr ⁻¹' (S ∩ E')) :=
      IsStoppingTime.comap_measurableSpace_le (comap_inr_drivingFiltration_le hX₂ hX) hτ _
        ⟨_, hS.inter hE'm, rfl⟩
    have hle₂ := hτ₂.measurableSpace_le
    have hX₂i : Integrable (X ∘ Sum.inr) P₂ := integrable_cexp_pairing hh₂ φ
    have ae₂ : (Sum.inr ⁻¹' (S ∩ E')).indicator (R ∘ Sum.inr) =ᵐ[P₂]
        (Sum.inr ⁻¹' (S ∩ E')).indicator (condExp hτ₂.measurableSpace P₂ (X ∘ Sum.inr)) := by
      filter_upwards [k₂] with ω hω
      by_cases hωS : ω ∈ Sum.inr ⁻¹' (S ∩ E')
      · rw [Set.indicator_of_mem hωS, Set.indicator_of_mem hωS]
        have h0 : Sum.inr ω ∈ E' := hωS.2
        have h1 := hE'D h0
        simp only [Set.mem_ofPred_eq] at h1
        have hD : Disjoint (tsupport (φ : ℂ → ℝ))
            (fwdHull (fun s : ℝ => W₂ s.toNNReal ω) (((τ (Sum.inr ω)).untopD 0 : ℝ≥0) : ℝ)) := h1
        have e1 := hω hD
        show frozenRHS κ W₂ (u ∘ Sum.inr) φ (fun ω => (τ (Sum.inr ω)).untopD 0) ω =
          condExp hτ₂.measurableSpace P₂ (fun ω' => Complex.exp (Complex.I * (h₂ ω' φ : ℂ))) ω
        exact e1.symm
      · rw [Set.indicator_of_notMem hωS, Set.indicator_of_notMem hωS]
    refine ⟨(integrable_condExp.indicator (hle₂ _ hS₂)).congr ae₂.symm, ?_⟩
    rw [integral_congr_ae ae₂, integral_indicator (hle₂ _ hS₂), integral_indicator (hle₂ _ hS₂),
      setIntegral_condExp hle₂ hX₂i hS₂]
  have hRi : Integrable (E'.indicator R) (mixMeasure P₁ P₂) := by
    have h := integrable_indicator_mixMeasure_iff.2
      ⟨(piece₁ Set.univ MeasurableSet.univ).1, (piece₂ Set.univ MeasurableSet.univ).1⟩
    rwa [Set.univ_inter] at h
  have key : ∀ S, MeasurableSet[hτ.measurableSpace] S → mixMeasure P₁ P₂ S < ∞ →
      ∫ x in S, E'.indicator R x ∂mixMeasure P₁ P₂ = ∫ x in S, E'.indicator X x ∂mixMeasure P₁ P₂ := by
    intro S hS _
    rw [← integral_indicator (hm _ hS), ← integral_indicator (hm _ hS), Set.indicator_indicator,
      Set.indicator_indicator]
    exact integral_indicator_mixMeasure_eq
      (integrable_indicator_mixMeasure_iff.2 ⟨(piece₁ S hS).1, (piece₂ S hS).1⟩)
      (hXi.indicator ((hm _ hS).inter (hm _ hE'm))) (piece₁ S hS).2 (piece₂ S hS).2
  have hae := ae_eq_condExp_of_forall_setIntegral_eq hm (hXi.indicator (hm _ hE'm))
    (fun S _ _ => hRi.integrableOn) key hE'R.aestronglyMeasurable
  have hind := condExp_indicator (m := hτ.measurableSpace) hXi hE'm
  filter_upwards [hae, hind, hDE'] with x h1 h2 h3 hD
  have hx : x ∈ E' := h3 hD
  have e := h1.trans h2
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx] at e
  exact e.symm

end Coupling

end Determination

end InteractingSLE
