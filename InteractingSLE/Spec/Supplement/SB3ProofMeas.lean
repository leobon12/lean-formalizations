/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# Lemma SB3's stage induction: from conditional kernels to the ambient measure for null-measurable events

Packet PROVE-T14-SB3. PROVE-T14-SB2's handoff (§5 (c)) isolates the measurability step of SB3's stage induction:
`∀ᵐ ω₀, ∀ᵐ ω ∂condExpKernel(ω₀), p ω` gives `∀ᵐ ω ∂P, p ω` when the event `{p}` is measurable
(`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`), whereas the S1 events of the induction are only universally measurable
(supplement p. 577: "This predicate is universally measurable [...] Existence of this one curve code is therefore
analytic"). This file proves the transfer for every **null-measurable** event, which is what universal measurability
supplies for the ambient measure:

* `ae_of_ae_condExpKernel_of_nullMeasurableSet`.

The remaining input of that step is that the S1 event is `P`-null-measurable. Mathlib (a4c8ef0a) has analytic sets
(`MeasureTheory.AnalyticSet`) but not their universal measurability (Lusin's theorem), so that input is not available.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace InteractingSLE

namespace Theorem14

namespace SB

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- A measurable `μ`-null set is null for almost every conditional kernel measure. -/
theorem ae_condExpKernel_eq_zero (hm : m ≤ mΩ) {Z : Set Ω} (hZ : MeasurableSet Z) (h0 : μ Z = 0) :
    ∀ᵐ ω₀ ∂μ, condExpKernel μ m ω₀ Z = 0 := by
  have h1 : ∫⁻ ω₀, condExpKernel μ m ω₀ Z ∂(μ.trim hm) = 0 := by
    rw [← Measure.bind_apply hZ (condExpKernel μ m).aemeasurable]
    exact (congrArg (fun ν : Measure Ω => ν Z) (condExpKernel_comp_trim hm)).trans h0
  have h2 : (fun ω₀ => condExpKernel μ m ω₀ Z) =ᵐ[μ.trim hm] 0 :=
    (lintegral_eq_zero_iff (measurable_condExpKernel hZ)).1 h1
  exact ae_of_ae_trim hm h2

/-- **A null-measurable event of kernel probability one for almost every `ω₀` has probability one** (the
measurability step of SB3's stage induction, for events which are only universally measurable). -/
theorem ae_of_ae_condExpKernel_of_nullMeasurableSet (hm : m ≤ mΩ) {p : Ω → Prop}
    (hp : NullMeasurableSet {ω | p ω} μ) (h : ∀ᵐ ω₀ ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω₀), p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  obtain ⟨t, hts, htm, hteq⟩ := hp.exists_measurable_subset_ae_eq
  -- the difference `{p} \ t` is contained in a measurable null set
  set Z := toMeasurable μ ({ω | p ω} \ t) with hZ
  have hZm : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hZ0 : μ Z = 0 := by
    rw [hZ, measure_toMeasurable]
    exact (ae_eq_set.1 hteq).2
  have hk := ae_condExpKernel_eq_zero hm hZm hZ0
  have ht : ∀ᵐ ω₀ ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ t := by
    filter_upwards [h, hk] with ω₀ hω₀ hZω₀
    have hnZ : ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZω₀
    filter_upwards [hω₀, hnZ] with ω hpω hωZ
    by_contra hωt
    exact hωZ (subset_toMeasurable _ _ ⟨hpω, hωt⟩)
  exact (Sec5.Lemma56Stages.ae_of_ae_condExpKernel hm htm ht).mono fun ω hω => hts hω

end SB

end Theorem14

end InteractingSLE
