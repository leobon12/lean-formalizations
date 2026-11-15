/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Kernel.Condexp

/-!
# Lemma 5.6 for several angles: from the conditional kernels of the stages to almost sure statements

Packet PROVE-SEC5-G (item 2(a) of `planning/handoffs/PROVE-SEC5-F.md`, "What remains"). For the frozen staged
histories (`IsStagedHistory`), each stage `k` is described only under the regular conditional law given the past,
`condExpKernel P (pastSigma … k) ω₀`, for almost every `ω₀`: the stage's driver is a flow-line driver of a
chart-transported field under that kernel. Lemma 5.6 for `ℓ ≥ 2` needs the stage properties `P`-almost surely. The
transfer is integration of a measurable event against the kernel (`condExpKernel_comp_trim`: integrating the kernel
against `P` restricted to the past σ-algebra gives back `P`):

* **`ae_of_ae_condExpKernel`**: if a measurable event has kernel probability one for almost every `ω₀`, it has
  probability one;
* **`ae_imp_of_ae_condExpKernel`**: the same under a condition `A` measurable for the past σ-algebra, which the
  kernel at `ω₀` decides almost surely (`condExpKernel_apply_eq_indicator`: `κ_{ω₀}(A) = 1_A(ω₀)` for almost every
  `ω₀`). This is the form the stages need: stage `k` exists (`ExplState.run … (k + 1)` returns a chart) only on a past
  event, and the kernel statement is asserted only there.

An event of a stage that is not measurable itself (for example the continuity of a path) is transferred through a
measurable subset of kernel probability one (`ae_of_ae_condExpKernel_of_subset`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace InteractingSLE

namespace Sec5

namespace Lemma56Stages

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- **A measurable event of kernel probability one for almost every `ω₀` has probability one.** -/
theorem ae_of_ae_condExpKernel (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet E)
    (h : ∀ᵐ ω₀ ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ E) : ∀ᵐ ω ∂μ, ω ∈ E := by
  have h1 : (fun ω₀ => condExpKernel μ m ω₀ Eᶜ) =ᵐ[μ] fun _ => 0 := h.mono fun ω₀ hω₀ => ae_iff.1 hω₀
  have h2 : (fun ω₀ => condExpKernel μ m ω₀ Eᶜ) =ᵐ[μ.trim hm] fun _ => 0 :=
    ae_eq_trim_of_measurable hm (measurable_condExpKernel hE.compl) measurable_const h1
  have h3 : μ Eᶜ = 0 := by
    rw [← condExpKernel_comp_trim (μ := μ) hm, Measure.bind_apply hE.compl (condExpKernel μ m).aemeasurable]
    rw [lintegral_congr_ae h2, lintegral_zero]
  exact ae_iff.2 h3

/-- A property holding on a measurable subset of kernel probability one, for almost every `ω₀`, holds almost
surely. -/
theorem ae_of_ae_condExpKernel_of_subset (hm : m ≤ mΩ) {p : Ω → Prop} {G : Set Ω} (hG : MeasurableSet G)
    (hGp : ∀ ω ∈ G, p ω) (h : ∀ᵐ ω₀ ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ G) : ∀ᵐ ω ∂μ, p ω :=
  (ae_of_ae_condExpKernel hm hG h).mono fun ω hω => hGp ω hω

/-- **The kernel decides past events**: for `A` measurable for the past σ-algebra, `κ_{ω₀}(A) = 1_A(ω₀)` for
almost every `ω₀`. -/
theorem condExpKernel_apply_eq_indicator (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∀ᵐ ω₀ ∂μ, condExpKernel μ m ω₀ A = A.indicator 1 ω₀ := by
  have hA' : MeasurableSet A := hm A hA
  have h1 := condExpKernel_ae_eq_condExp hm hA' (μ := μ)
  have h2 : μ⟦A|m⟧ =ᵐ[μ] (A.indicator fun _ => (1 : ℝ)) := by
    rw [condExp_of_stronglyMeasurable hm ((stronglyMeasurable_const.indicator hA))
      ((integrable_const (1 : ℝ)).indicator hA')]
  filter_upwards [h1, h2] with ω₀ h1ω h2ω
  rw [h2ω] at h1ω
  have hfin : condExpKernel μ m ω₀ A ≠ ⊤ := measure_ne_top _ _
  by_cases hω : ω₀ ∈ A
  · simp only [indicator_of_mem hω] at h1ω ⊢
    rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, h1ω, ENNReal.ofReal_one, Pi.one_apply]
  · simp only [indicator_of_notMem hω] at h1ω ⊢
    rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, h1ω, ENNReal.ofReal_zero]

/-- **Transfer under a past condition**: if, for almost every `ω₀` in a past event `A`, a measurable event `E` has
kernel probability one, then almost surely `ω ∈ A → ω ∈ E`. -/
theorem ae_imp_of_ae_condExpKernel (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {E : Set Ω}
    (hE : MeasurableSet E) (h : ∀ᵐ ω₀ ∂μ, ω₀ ∈ A → ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ E) :
    ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ E := by
  have hA' : MeasurableSet A := hm A hA
  have hE' : MeasurableSet (Aᶜ ∪ E) := hA'.compl.union hE
  have key : ∀ᵐ ω₀ ∂μ, ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ Aᶜ ∪ E := by
    filter_upwards [h, condExpKernel_apply_eq_indicator hm hA (μ := μ)] with ω₀ hω₀ hind
    by_cases hω : ω₀ ∈ A
    · exact (hω₀ hω).mono fun ω hω => Or.inr hω
    · have h0 : condExpKernel μ m ω₀ A = 0 := by rw [hind, indicator_of_notMem hω]
      have hAc : ∀ᵐ ω ∂(condExpKernel μ m ω₀), ω ∈ Aᶜ := by
        rw [ae_iff]
        simpa [compl_compl] using h0
      exact hAc.mono fun ω hω => Or.inl hω
  filter_upwards [ae_of_ae_condExpKernel hm hE' key] with ω hω hωA
  rcases hω with h | h
  · exact absurd hωA h
  · exact h

end Lemma56Stages

end Sec5

end InteractingSLE
