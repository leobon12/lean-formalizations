/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# The general restart kernel: measure-theoretic tools

Packet PROVE-RESTARTKERNEL. Four open inputs ask for the same object in different charts: a Markov kernel `K`
disintegrating a restart variable `X` (chart field and continuations) over a chart datum `β` on an event `M`,
`(P|M).map (β, X) = (P|M).map β ⊗ₘ K`, such that for almost every datum `c` the chart field is a GFF with the word of
`c` under `K c` and the continuations are its flow lines (Lemma 7.8's continuation assertion, Theorem W8, p. 539: "Every
nonempty available continuation is the corresponding angle flow of that same conditional field"; W8's proof, p. 541:
"Universal finite-force determination now identifies each actual conditional future … as the canonical flow of the same
conditional field").

This file proves the measure-theoretic steps common to all of them, for **every** disintegrating kernel:

* `ae_ae_of_map_eq_compProd`: an event of `(β, X)` holding almost surely on `M` holds, for almost every datum `c`,
  `K c`-almost surely (the converse direction is `Restart.ae_mem_of_compProd_eq`);
* `ae_isGFFWithBoundaryData_of_condExp_word`: (R1) of the carrier for a datum `β : Ω → C` that carries its word
  through a measurable map `w : C → BoundaryWord` (`C = BoundaryWord × ℝ` for the retained pair, where the second
  coordinate is the first tip's chart position). It is `Restart.ae_isGFFWithBoundaryData_of_condExp` (the case
  `w = id`) with the word read through `w`; the proof is the same.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric

/-! ### Events of the restart variable under a disintegrating kernel -/

/-- **An almost sure event of `(β, X)` on `M` holds under almost every kernel measure.** If `K` disintegrates the joint
law of `(β, X)` on `M` and a measurable event `E` of `(β, X)` holds almost surely on `M`, then for almost every datum
`c`, `K c`-almost every `s` has `(c, s) ∈ E`. -/
theorem ae_ae_of_map_eq_compProd {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {E : Set (C × S)} (hE : MeasurableSet E) (hae : ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∈ E) :
    ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), (c, s) ∈ E := by
  have h1 : ∀ᵐ p ∂(P.restrict M).map (fun ω => (β ω, X ω)), p ∈ E :=
    (ae_map_iff (p := fun p => p ∈ E) (hβ.prodMk hX).aemeasurable hE).2 ((ae_restrict_iff' hM).2 hae)
  rw [hlaw] at h1
  exact Measure.ae_ae_of_ae_compProd h1

/-! ### (R1) for a datum carrying a word -/

/-- **(R1) of the restart carrier for a datum carrying its word through a measurable map `w`.** Let `𝒢` be a
sub-σ-algebra, `M ∈ 𝒢`, `β` a `𝒢`-measurable datum whose word `w ∘ β` is sorted on `M`, and `X` a random element of
`S` whose coordinate `H ∘ X` is the chart field. If, on `M`, the characteristic functional of the chart field given
`𝒢` is the Gaussian one of the word `w (β ω)`, then for every Markov kernel `K` disintegrating `(β, X)` on `M`, for
almost every datum `c`, the word `w c` is sorted and under `K c` the field `H` is a GFF with boundary datum `w c`.
(`Restart.ae_isGFFWithBoundaryData_of_condExp` is the case `w = id`; same proof.) -/
theorem ae_isGFFWithBoundaryData_of_condExp_word {Ω C S : Type*} {𝒢 : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [MeasurableSpace C] [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M) {β : Ω → C} (hβ : Measurable[𝒢] β)
    {w : C → BoundaryWord} (hw : Measurable w)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted) {X : Ω → S} (hX : Measurable X)
    {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ) :
    ∀ᵐ c ∂(P.restrict M).map β,
      (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hfm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun s => Complex.exp (Complex.I * (H s φ : ℂ)) := fun φ =>
    GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hH)
  have hnorm : ∀ (φ : TestOn upperHalfPlaneOpens) (s : S),
      ‖Complex.exp (Complex.I * (H s φ : ℂ))‖ ≤ 1 := fun φ s =>
    (Complex.norm_exp_I_mul_ofReal _).le
  have hgm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun c => gaussCF (w c) φ := fun φ =>
    (measurable_gaussCF φ).comp hw
  -- Step 1: for each test function, the kernel characteristic value is the Gaussian one for a.e. datum.
  have hstep : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun c => ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c)) =ᵐ[(P.restrict M).map β]
        fun c => gaussCF (w c) φ := by
    intro φ
    have hFm : Measurable fun c => ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c) :=
      ((hfm φ).stronglyMeasurable.integral_kernel (κ := K)).measurable
    have hFb : ∀ c, ‖∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c)‖ ≤ 1 := fun c =>
      (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall (hnorm φ))).trans
        (by simp)
    have hint_f : Integrable (fun ω => Complex.exp (Complex.I * (H (X ω) φ : ℂ))) P :=
      Integrable.of_bound ((hfm φ).comp hX).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => hnorm φ (X ω))
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A _ _ => ?_) (fun A _ _ => ?_)
      fun A hA _ => ?_
    · exact (Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall hFb)).integrableOn
    · exact (Integrable.of_bound (hgm φ).aestronglyMeasurable 1
        (Eventually.of_forall fun c => norm_gaussCF_le (w c) φ)).integrableOn
    have hpre : (fun ω => (β ω, X ω)) ⁻¹' (A ×ˢ univ) = β ⁻¹' A := by
      ext ω; simp
    have hGA : MeasurableSet[𝒢] (β ⁻¹' A ∩ M) := (hβ hA).inter hM
    have hgm' : Measurable fun p : C × S => Complex.exp (Complex.I * (H p.2 φ : ℂ)) :=
      (hfm φ).comp measurable_snd
    calc ∫ c in A, ∫ s, Complex.exp (Complex.I * (H s φ : ℂ)) ∂(K c) ∂((P.restrict M).map β)
        = ∫ p in A ×ˢ univ, Complex.exp (Complex.I * (H p.2 φ : ℂ))
            ∂((P.restrict M).map β ⊗ₘ K) := by
          rw [Measure.setIntegral_compProd hA MeasurableSet.univ]
          · simp only [Measure.restrict_univ]
          · exact (Integrable.of_bound hgm'.aestronglyMeasurable 1
              (Eventually.of_forall fun p => hnorm φ p.2)).integrableOn
      _ = ∫ ω in β ⁻¹' A ∩ M, Complex.exp (Complex.I * (H (X ω) φ : ℂ)) ∂P := by
          rw [← hlaw, setIntegral_map (hA.prod MeasurableSet.univ) hgm'.aestronglyMeasurable
            (hβm.prodMk hX).aemeasurable, hpre, Measure.restrict_restrict (hβm hA)]
      _ = ∫ ω in β ⁻¹' A ∩ M, P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω ∂P :=
          (setIntegral_condExp h𝒢 hint_f hGA).symm
      _ = ∫ ω in β ⁻¹' A ∩ M, gaussCF (w (β ω)) φ ∂P := by
          refine setIntegral_congr_ae (h𝒢 _ hGA) ?_
          filter_upwards [hG φ] with ω hω hωA
          exact hω hωA.2
      _ = ∫ c in A, gaussCF (w c) φ ∂((P.restrict M).map β) := by
          rw [setIntegral_map hA (hgm φ).aestronglyMeasurable hβm.aemeasurable,
            Measure.restrict_restrict (hβm hA)]
  -- Step 2: simultaneously for the countable family of rational combinations, and sorted words.
  have hall := ae_all_iff.2 fun k : RatComb => hstep (ratComb upperHalfPlaneOpens k)
  have hsorted : ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted := by
    exact (ae_map_iff (p := fun c => (w c).IsSorted) hβm.aemeasurable
      (hw BoundaryWord.measurableSet_isSorted)).2 ((ae_restrict_iff' hMm).2 hsort)
  filter_upwards [hall, hsorted] with c hc hcs
  -- Step 3: the law of `H` under `K c` is the word GFF law.
  have hmap : (K c).map H = (w c).gffLaw := by
    refine ext_of_integral_cexp_ratComb fun k => ?_
    rw [integral_map hH.aemeasurable (GFF.measurable_exp_I_mul
      (measurable_distOn_apply _)).aestronglyMeasurable, hc k, gaussCF_eq_integral]
  refine ⟨hcs, hH, fun u₀ hu₀ => ?_⟩
  have h := ((w c).isGFFWithBoundaryData_gffLaw hcs).2 u₀ hu₀
  rw [← hmap] at h
  exact isZBGFFProcess_comp hH h

end Restart

end InteractingSLE
