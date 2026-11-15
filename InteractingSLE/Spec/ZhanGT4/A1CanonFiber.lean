/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonStopBM

/-!
# Stopped image noises from their conditional laws

Packet PROVE-ZHAN-A1CANON. Source: follow-up 5 §1.3 (L203–L222, R73): "If `τ` is bounded by the large-curve protection
time, optional sampling gives the density `M(s, τ)` … Conditional Girsanov gives the image SDE." The conditional form
of a rectangle's image law is a statement under almost every regular conditional law given `𝓕ᵏ_τ`; the rectangle core
`A1Canon.IsCanonImageCore` asks for the unconditional statement in a filtration containing `𝓕ᵏ_τ`. This file converts
the first into the second, generically:

* `supFiltration 𝓔 𝓖`: the filtration `𝓔 ∨ 𝓖_t`;
* `setIntegral_eq_of_isPiSystem`: equal set integrals on a generating π-system containing `univ` give equal
  set integrals on the generated σ-algebra (Dynkin);
* **`martingale_supFiltration_of_condExpKernel`**: a process adapted to `𝓔 ∨ 𝓖` that is, under almost every
  conditional law given `𝓔` (`condExpKernel`), a `𝓖`-martingale, is a `𝓔 ∨ 𝓖`-martingale;
* `lintegral_condExpKernel`: `∫⁻ (∫⁻ f d condExpKernel) dP = ∫⁻ f dP`;
* **`isStoppedBM_of_ae_condExpKernel`**: if under almost every conditional law given `𝓔` the noise `N` is a
  `𝓖`-Brownian motion stopped at `S` (`IsStoppedBM`), it is one for `𝓔 ∨ 𝓖` under `P`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Canon

section Fiber

variable {Ω : Type*} {𝓔 𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit 𝓔 𝓜 in
/-- The filtration `𝓔 ∨ 𝓖_t`. -/
def supFiltration (𝓔 : MeasurableSpace Ω) (h𝓔 : 𝓔 ≤ mΩ) (𝓖 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓔 ⊔ 𝓖 t
  mono' _ _ hst := sup_le_sup le_rfl (𝓖.mono hst)
  le' t := sup_le h𝓔 (𝓖.le t)

omit 𝓜 in
theorem supFiltration_apply (h𝓔 : 𝓔 ≤ mΩ) (𝓖 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    supFiltration 𝓔 h𝓔 𝓖 t = 𝓔 ⊔ 𝓖 t := rfl

omit 𝓜 in
theorem le_supFiltration (h𝓔 : 𝓔 ≤ mΩ) (𝓖 : Filtration ℝ≥0 mΩ) :
    𝓖 ≤ supFiltration 𝓔 h𝓔 𝓖 := fun _ => le_sup_right

/-- **Set integrals agreeing on a generating π-system containing `univ` agree on the generated σ-algebra.** -/
theorem setIntegral_eq_of_isPiSystem {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (h𝓜 : 𝓜 ≤ mΩ) {π : Set (Set Ω)} (hgen : 𝓜 = MeasurableSpace.generateFrom π)
    (hπ : IsPiSystem π) (huniv : univ ∈ π) (h : ∀ s ∈ π, ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P) {s : Set Ω}
    (hs : MeasurableSet[𝓜] s) : ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P := by
  have htot : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by simpa only [Measure.restrict_univ] using h univ huniv
  refine @MeasurableSpace.induction_on_inter Ω 𝓜 (fun s _ => ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P) π hgen hπ
    ?_ (fun s hs => h s hs) ?_ ?_ s hs
  · simp only [Measure.restrict_empty, integral_zero_measure]
  · intro t ht hteq
    have htm : MeasurableSet[mΩ] t := h𝓜 t ht
    have h1 := integral_add_compl htm hf
    have h2 := integral_add_compl htm hg
    linarith
  · intro F hdisj hFm hFeq
    have hFm' : ∀ i, MeasurableSet[mΩ] (F i) := fun i => h𝓜 _ (hFm i)
    rw [integral_iUnion hFm' hdisj hf.integrableOn, integral_iUnion hFm' hdisj hg.integrableOn]
    exact tsum_congr hFeq

variable [StandardBorelSpace Ω] [IsFiniteMeasure P]

/-- **A martingale under almost every conditional law is a martingale of the enlarged filtration.** Let `X` be adapted
to `𝓔 ∨ 𝓖` and integrable, and under almost every conditional law given `𝓔` let it have the `𝓖`-martingale property
(`∫_A X_t = ∫_A X_s` for `A ∈ 𝓖_s`). Then `X` is a `𝓔 ∨ 𝓖`-martingale under `P`. -/
theorem martingale_supFiltration_of_condExpKernel (h𝓔 : 𝓔 ≤ mΩ)
    {𝓖 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hadp : StronglyAdapted (supFiltration 𝓔 h𝓔 𝓖) X)
    (hint : ∀ t, Integrable (X t) P)
    (hfib : ∀ᵐ ω₀ ∂P, ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[𝓖 s] A →
      ∫ ω in A, X t ω ∂(condExpKernel P 𝓔 ω₀) = ∫ ω in A, X s ω ∂(condExpKernel P 𝓔 ω₀)) :
    Martingale X (supFiltration 𝓔 h𝓔 𝓖) P := by
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((supFiltration 𝓔 h𝓔 𝓖).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun C hC _ => ?_) (hadp s).aestronglyMeasurable).symm
  set π : Set (Set Ω) := {C | ∃ (E A : Set Ω), MeasurableSet[𝓔] E ∧ MeasurableSet[𝓖 s] A ∧ C = E ∩ A} with hπdef
  have hgen : supFiltration 𝓔 h𝓔 𝓖 s = MeasurableSpace.generateFrom π := by
    rw [supFiltration_apply]
    refine le_antisymm (sup_le (fun E hE => ?_) (fun A hA => ?_)) (MeasurableSpace.generateFrom_le ?_)
    · exact MeasurableSpace.measurableSet_generateFrom ⟨E, univ, hE, MeasurableSet.univ, (inter_univ E).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, A, MeasurableSet.univ, hA, (univ_inter A).symm⟩
    · rintro _ ⟨E, A, hE, hA, rfl⟩
      exact ((le_sup_left : 𝓔 ≤ 𝓔 ⊔ 𝓖 s) _ hE).inter ((le_sup_right : 𝓖 s ≤ 𝓔 ⊔ 𝓖 s) _ hA)
  have hπ : IsPiSystem π := by
    rintro _ ⟨E, A, hE, hA, rfl⟩ _ ⟨E', A', hE', hA', rfl⟩ _
    exact ⟨E ∩ E', A ∩ A', hE.inter hE', hA.inter hA', inter_inter_inter_comm E A E' A'⟩
  have huniv : univ ∈ π := ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, (inter_univ _).symm⟩
  -- the set integrals on `E ∩ A` via the conditional laws
  have hbasic : ∀ u, ∀ E A, MeasurableSet[𝓔] E → MeasurableSet[𝓖 s] A →
      ∫ ω in E ∩ A, X u ω ∂P = ∫ ω in E, (∫ y in A, X u y ∂(condExpKernel P 𝓔 ω)) ∂P := by
    intro u E A hE hA
    have hAm : MeasurableSet[mΩ] A := 𝓖.le s A hA
    have hi : Integrable (A.indicator (X u)) P := (hint u).indicator hAm
    rw [← setIntegral_indicator hAm, ← setIntegral_condExp h𝓔 hi hE]
    refine setIntegral_congr_ae (h𝓔 E hE) ?_
    filter_upwards [condExp_ae_eq_integral_condExpKernel h𝓔 hi] with ω hω _
    rw [hω, integral_indicator hAm]
  refine (setIntegral_eq_of_isPiSystem (hint t) (hint s) ((supFiltration 𝓔 h𝓔 𝓖).le s) hgen hπ huniv ?_ hC).symm
  rintro _ ⟨E, A, hE, hA, rfl⟩
  rw [hbasic t E A hE hA, hbasic s E A hE hA]
  refine setIntegral_congr_ae (h𝓔 E hE) ?_
  filter_upwards [hfib] with ω hω _
  exact hω s t hst A hA

/-- **Disintegration of lower integrals through the regular conditional laws.** -/
theorem lintegral_condExpKernel (h𝓔 : 𝓔 ≤ mΩ) {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, (∫⁻ y, f y ∂condExpKernel P 𝓔 ω) ∂P = ∫⁻ ω, f ω ∂P := by
  conv_rhs => rw [← condExpKernel_comp_trim (μ := P) h𝓔]
  rw [Measure.lintegral_bind (condExpKernel P 𝓔).measurable.aemeasurable hf.aemeasurable]
  exact (lintegral_trim h𝓔 (Measurable.lintegral_kernel hf)).symm

/-- **A stopped Brownian motion under almost every conditional law is one for the enlarged filtration**: if under
almost every regular conditional law given `𝓔` the noise `N` (with `N₀ = 0`) is a `𝓖`-Brownian motion stopped at `S`,
then `N` is a `𝓔 ∨ 𝓖`-Brownian motion stopped at `S` under `P`. -/
theorem isStoppedBM_of_ae_condExpKernel [NeZero P] (h𝓔 : 𝓔 ≤ mΩ)
    {𝓖 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
    (hfib : ∀ᵐ ω₀ ∂P, IsStoppedBM (condExpKernel P 𝓔 ω₀) 𝓖 N S) (hN0 : ∀ ω, N 0 ω = 0) :
    IsStoppedBM P (supFiltration 𝓔 h𝓔 𝓖) N S := by
  intro a
  obtain ⟨ω₁, hω₁⟩ := hfib.exists
  have hadp : StronglyAdapted (supFiltration 𝓔 h𝓔 𝓖) (stopExp a N S) := fun t =>
    ((hω₁ a).stronglyAdapted t).mono (le_supFiltration h𝓔 𝓖 t)
  have hpos : ∀ t ω, 0 ≤ stopExp a N S t ω := fun t ω => (Real.exp_pos _).le
  have hint : ∀ t, Integrable (stopExp a N S t) P := by
    intro t
    have hm : Measurable (stopExp a N S t) := ((hadp t).measurable).mono ((supFiltration 𝓔 h𝓔 𝓖).le t) le_rfl
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpos t)), ← lintegral_condExpKernel h𝓔 hm.ennreal_ofReal]
    have h1 : ∀ᵐ ω₀ ∂P, ∫⁻ y, ENNReal.ofReal (stopExp a N S t y) ∂condExpKernel P 𝓔 ω₀ = 1 := by
      filter_upwards [hfib] with ω₀ hω₀
      rw [← ofReal_integral_eq_lintegral_ofReal ((hω₀ a).integrable t) (ae_of_all _ (hpos t))]
      have h0 := (hω₀ a).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) (@MeasurableSet.univ _ (𝓖 0))
      simp only [Measure.restrict_univ] at h0
      rw [← h0]
      simp [stopExp, hN0]
    rw [lintegral_congr_ae h1, lintegral_const, one_mul]
    exact measure_lt_top P univ
  refine martingale_supFiltration_of_condExpKernel h𝓔 hadp hint ?_
  filter_upwards [hfib] with ω₀ hω₀ s t hst A hA
  exact ((hω₀ a).setIntegral_eq hst hA).symm

end Fiber

end InteractingSLE.ZhanGT4.A1Canon
