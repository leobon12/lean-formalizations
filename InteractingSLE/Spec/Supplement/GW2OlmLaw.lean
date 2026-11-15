/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmTower

/-!
# GW2's open lines: marked locality for the kernel marks, and laws read back from the kernel

Packet PROVE-GW2-STAGEMEAN, R117(b) round.

* **`isHistoryAvoidanceLocal_of_sup_null_eq`**: if `B` is history-marked local for `ℋ` and `𝓚 ⊔ nulls = ℋ ⊔ nulls`
  ((T2)), it is history-marked local for `𝓚` (`Sec7.Lemma72E.isHistoryAvoidanceLocal_sup_nullSets` and monotonicity in
  the marks);
* **`ae_kernel_condExp_event`**: for `P`-a.e. `ω₀`, an identity `μ_{ω₀}[f | 𝓚] = F` holding `μ_{ω₀}`-a.s. on `G`
  turns into the identity `P[f | 𝓚] = F` holding `μ_{ω₀}`-a.s. on `G` — an event of the sample, which the kernel chain
  of the earlier pieces (`KernelTower.ae_ae_of_chain`) integrates to `P` (`GW2Olm.ae_condExp_condExpKernel_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Olm

open WholeField

/-- **Marked locality passes to marks that agree up to null sets.** -/
theorem isHistoryAvoidanceLocal_of_sup_null_eq {Ω : Type*} {𝓚 ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hagree : 𝓚 ⊔ Ito.nullSets P = ℋ ⊔ Ito.nullSets P) (hloc : IsHistoryAvoidanceLocal ℋ B h P) :
    IsHistoryAvoidanceLocal 𝓚 B h P := by
  have h1 := Sec7.Lemma72E.isHistoryAvoidanceLocal_sup_nullSets hloc
  rw [← hagree] at h1
  intro U G hUH hG hd F hF
  exact h1 U G hUH hG hd F (le_sup_left (a := 𝓚) (b := Ito.nullSets P) F hF)

/-- **A kernel identity for the conditional expectation given countably generated marks is an event of the sample
under the kernel.** -/
theorem ae_kernel_condExp_event {Ω : Type*} {𝒢 𝓚 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ 𝓚) (h𝓚 : 𝓚 ≤ mΩ)
    (hcg : @MeasurableSpace.CountablyGenerated Ω 𝓚) {f : Ω → ℂ} (hf : Integrable f P) :
    ∀ᵐ ω₀ ∂P, ∀ {G : Set Ω} {F : Ω → ℂ},
      (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ G → ((condExpKernel P 𝒢 ω₀)[f | 𝓚]) ω = F ω) →
      ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ G → (P[f | 𝓚]) ω = F ω := by
  filter_upwards [ae_condExp_condExpKernel_eq h𝒢 h𝓚 hcg hf] with ω₀ hω₀ G F hk
  filter_upwards [hk, hω₀] with ω h1 h2 hωG
  rw [← h2, h1 hωG]

end InteractingSLE.Theorem14.GW2Olm
