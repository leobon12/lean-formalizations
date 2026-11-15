/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma56Stages
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# The disintegration step: from the conditional kernels, with a past-measurable parameter, to the ambient measure

Packet PROVE-T14-BR5. GW2a's induction (supplement p. 623: "In the already established complete conditional
counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary piece") proves the
assertion about the next piece under the regular conditional law `ν ω₀ = condExpKernel P 𝒢 ω₀` given the retained
past, with the past data (the launch chart, the conditional boundary word, …) **frozen at their value at `ω₀`**. This
file moves such a statement back to `P`, with the past data evaluated at the sample itself:

* **`ae_of_ae_condExpKernel_param`**: for a `𝒢`-measurable parameter `X : Ω → S` with values in a second-countable
  `T₁` Borel space and a measurable set `A ⊆ S × Ω`, if for `P`-a.e. `ω₀` the event `(X ω₀, ω) ∈ A` has conditional
  probability one, then `(X ω, ω) ∈ A` holds `P`-almost surely. The kernel is concentrated on the fibre of `X`
  (`Sec7.Aux122Disint.ae_ae_condExpKernel_eq`), so the frozen parameter may be replaced by the moving one, and the
  resulting measurable event is integrated back (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`).
* **`ae_imp_of_ae_condExpKernel_param`**: the same on a past event `F` (the event that the next piece is launched).
* `ae_ae_condExpKernel_param`: the converse direction (a `P`-almost sure statement holds kernel-almost surely, with the
  parameter frozen at `ω₀`), which needs no measurability.

The measurability of `A` is essential: kernel-almost sure statements about non-measurable events do not integrate to
`P`-almost sure statements in general (the kernels only see the fibres of `𝒢`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace InteractingSLE

namespace Theorem14

namespace Disintegrate

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {S : Type*} [TopologicalSpace S] [SecondCountableTopology S] [T1Space S]
  [MeasurableSpace S] [OpensMeasurableSpace S]

/-- **The kernel statement with the parameter frozen at `ω₀` holds with the moving parameter.** -/
theorem ae_ae_condExpKernel_param_eq (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → S} (hX : Measurable[𝒢] X) {p : S → Ω → Prop}
    (h : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), p (X ω₀) ω) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), p (X ω) ω := by
  filter_upwards [h, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hX] with ω₀ h1 h2
  filter_upwards [h1, h2] with ω hp hx
  rw [hx]
  exact hp

/-- **Disintegration with a past-measurable parameter.** If `X` is `𝒢`-measurable with values in a second-countable
`T₁` Borel space, `A ⊆ S × Ω` is measurable, and for `P`-almost every `ω₀`, conditionally on `𝒢` (kernel
`condExpKernel P 𝒢 ω₀`), almost surely `(X ω₀, ω) ∈ A`, then `P`-almost surely `(X ω, ω) ∈ A`. -/
theorem ae_of_ae_condExpKernel_param (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → S} (hX : Measurable[𝒢] X) {A : Set (S × Ω)}
    (hA : MeasurableSet A) (h : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (X ω₀, ω) ∈ A) :
    ∀ᵐ ω ∂P, (X ω, ω) ∈ A := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hE : MeasurableSet {ω | (X ω, ω) ∈ A} := (hXm.prodMk measurable_id) hA
  exact Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hE
    (ae_ae_condExpKernel_param_eq (p := fun s ω => (s, ω) ∈ A) h𝒢 hX h)

/-- **Disintegration with a past-measurable parameter, on a past event.** If `F` is a `𝒢`-event and, for `P`-almost
every `ω₀ ∈ F`, conditionally on `𝒢` almost surely `(X ω₀, ω) ∈ A`, then `P`-almost surely `ω ∈ F → (X ω, ω) ∈ A`. -/
theorem ae_imp_of_ae_condExpKernel_param (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → S} (hX : Measurable[𝒢] X) {A : Set (S × Ω)}
    (hA : MeasurableSet A) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    (h : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (X ω₀, ω) ∈ A) :
    ∀ᵐ ω ∂P, ω ∈ F → (X ω, ω) ∈ A := by
  set A' : Set (S × Ω) := {q | q.2 ∈ F → q ∈ A} with hA'
  have hA'm : MeasurableSet A' := ((h𝒢 _ hF).preimage measurable_snd).compl.union hA |>.congr (by
    ext q
    simp only [hA', mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq]
    tauto)
  have h' : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (X ω₀, ω) ∈ A' := by
    filter_upwards [h, Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) h𝒢 hF] with ω₀ hω₀ hind
    by_cases hF₀ : ω₀ ∈ F
    · exact (hω₀ hF₀).mono fun ω hω _ => hω
    · have h0 : condExpKernel P 𝒢 ω₀ F = 0 := by rw [hind, indicator_of_notMem hF₀]
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun ω hω hωF => absurd hωF hω
  exact ae_of_ae_condExpKernel_param h𝒢 hX hA'm h'

/-- **A `P`-almost sure statement holds kernel-almost surely, with the parameter frozen at `ω₀`** (no measurability
needed: a `P`-null set is contained in a measurable `P`-null set, which is null for almost every kernel measure). -/
theorem ae_ae_condExpKernel_param (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → S} (hX : Measurable[𝒢] X) {p : S → Ω → Prop}
    (h : ∀ᵐ ω ∂P, p (X ω) ω) : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), p (X ω₀) ω := by
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 h,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hX] with ω₀ h1 h2
  filter_upwards [h1, h2] with ω hp hx
  rw [← hx]
  exact hp

end Disintegrate

end Theorem14

end InteractingSLE
