/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TestKernel

/-!
# Transferring GW2 stage estimates from the complete next-piece law

Continuation of PROVE-T14-GW2ROOT2. The full conditional image-law identity is
an explicit mathematical hypothesis. Its measurable sample map prevents the
nonmeasurable-map convention for `Measure.map` from acting as a law identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK3

variable {Ω Ξ : Type*} {σ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} [IsFiniteMeasure P]

/-- A measurable event of the complete next-piece sample has its prescribed
kernel probability, including an almost-sure identification of the raw event. -/
theorem ae_condExpKernel_event_eq_of_map (hσ : σ ≤ mΩ) {A E : Set Ω}
    {U : Ω → Ξ} (hU : Measurable U) {B : Set Ξ} (hB : MeasurableSet B)
    {K : Ω → Measure Ξ}
    (hLaw : ∀ᵐ ω ∂P, ω ∈ A → (condExpKernel P σ ω).map U = K ω)
    (hident : U ⁻¹' B =ᵐ[P] E) :
    ∀ᵐ ω ∂P, ω ∈ A → condExpKernel P σ ω E = K ω B := by
  filter_upwards [hLaw, KernelTower.ae_ae_condExpKernel_of_ae hσ hident]
    with ω hωLaw hωident hωA
  calc
    condExpKernel P σ ω E = condExpKernel P σ ω (U ⁻¹' B) :=
      (measure_congr hωident).symm
    _ = (condExpKernel P σ ω).map U B := (Measure.map_apply hU hB).symm
    _ = K ω B := congrArg (fun μ : Measure Ξ => μ B) (hωLaw hωA)

/-- Integrating a conditional lower bound over a past event gives the
comparison inequality used by the existing no-unit theorem. -/
theorem le_measure_inter_of_ae_condExpKernel (hσ : σ ≤ mΩ) {A E : Set Ω}
    (hE : MeasurableSet E) {p : ℝ≥0∞}
    (hbound : ∀ᵐ ω ∂P, ω ∈ A → p ≤ condExpKernel P σ ω E)
    {C : Set Ω} (hC : MeasurableSet[σ] C) (hCA : C ⊆ A) :
    p * P C ≤ P (C ∩ E) := by
  calc
    p * P C = ∫⁻ ω in C, p ∂P := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ ω in C, condExpKernel P σ ω E ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hbound, ae_restrict_mem (hσ _ hC)]
        with ω hω hωC
      exact hω (hCA hωC)
    _ = P (C ∩ E) := KernelTower.setLIntegral_condExpKernel hσ hC hE

/-- A slow-event bound for the model law becomes a comparison bound on every
retained past event. No independence from the retained counterflow is assumed. -/
theorem le_measure_inter_preimage_of_map (hσ : σ ≤ mΩ) {A : Set Ω}
    {U : Ω → Ξ} (hU : Measurable U) {D : Set Ξ} (hD : MeasurableSet D)
    {K : Ω → Measure Ξ}
    (hLaw : ∀ᵐ ω ∂P, ω ∈ A → (condExpKernel P σ ω).map U = K ω)
    {p : ℝ≥0∞} (hslow : ∀ᵐ ω ∂P, ω ∈ A → p ≤ K ω D)
    {C : Set Ω} (hC : MeasurableSet[σ] C) (hCA : C ⊆ A) :
    p * P C ≤ P (C ∩ U ⁻¹' D) := by
  apply le_measure_inter_of_ae_condExpKernel hσ (hU hD) _ hC hCA
  filter_upwards [ae_condExpKernel_event_eq_of_map hσ hU hD hLaw
    (Eventually.of_forall fun _ => rfl), hslow] with ω hωLaw hωslow hωA
  rw [hωLaw hωA]
  exact hωslow hωA

end InteractingSLE.Theorem14.GW2TipSystem.RootK3
