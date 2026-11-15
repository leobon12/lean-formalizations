/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# GW2's stage chart law, part 1: conditional laws pass from the conditional kernel to `P`

Packet PROVE-GW2-STAGEMEAN, stage-chart-law round. On the conditional-kernel route of GW2's stage identity the stage
facts are proved under `μ_{ω₀} = condExpKernel P 𝒢 ω₀` (the stage field is a GFF of the stage word, the image
counterflow a complete counterflow of it, …). The lines step reads them as conditional laws under `P` given the
marks `𝓗` of the stage union. This file transfers a conditional expectation identity from almost every kernel
measure to `P`, for ANY sub-σ-algebras `𝒢, 𝓗` (no inclusion and no countable generation is needed in this direction):

* `integral_integral_condExpKernel`: `∫ (∫ f dμ_ω) dP(ω) = ∫ f dP`;
* **`ae_condExp_eq_of_ae_condExpKernel`**: if `f`, `F` are bounded, `F` is `𝓗`-measurable, and for almost every `ω₀`
  `μ_{ω₀}[f | 𝓗] = F` `μ_{ω₀}`-almost surely, then `P[f | 𝓗] = F` `P`-almost surely;
* **`ae_condExp_eq_on_of_ae_condExpKernel`**: the same on an `𝓗`-event `G` (the form of a chart law on the live event).

Measure theory only; conditional helper with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE.Theorem14.GW2Scl

variable {Ω : Type*} {𝒢 𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Disintegration of an integral over the conditional kernel.** -/
theorem integral_integral_condExpKernel (h𝒢 : 𝒢 ≤ mΩ) {f : Ω → ℂ} (hf : Integrable f P) :
    ∫ ω, ∫ x, f x ∂(condExpKernel P 𝒢 ω) ∂P = ∫ x, f x ∂P := by
  calc ∫ ω, ∫ x, f x ∂(condExpKernel P 𝒢 ω) ∂P = ∫ ω, (P[f | 𝒢]) ω ∂P :=
        (integral_congr_ae (condExp_ae_eq_integral_condExpKernel h𝒢 hf)).symm
    _ = ∫ x, f x ∂P := integral_condExp h𝒢

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A bounded strongly measurable function is integrable for a finite measure. -/
theorem integrable_of_bound (Q : Measure Ω) [IsFiniteMeasure Q] {f : Ω → ℂ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f Q :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

/-- **A conditional expectation identity under almost every conditional kernel measure holds under `P`.** -/
theorem ae_condExp_eq_of_ae_condExpKernel (h𝒢 : 𝒢 ≤ mΩ) (h𝓗 : 𝓗 ≤ mΩ) {f F : Ω → ℂ} {C : ℝ}
    (hfm : StronglyMeasurable f) (hfb : ∀ ω, ‖f ω‖ ≤ C) (hFm : StronglyMeasurable[𝓗] F) (hFb : ∀ ω, ‖F ω‖ ≤ C)
    (hk : ∀ᵐ ω₀ ∂P, (condExpKernel P 𝒢 ω₀)[f | 𝓗] =ᵐ[condExpKernel P 𝒢 ω₀] F) :
    P[f | 𝓗] =ᵐ[P] F := by
  have hFm' : StronglyMeasurable F := hFm.mono h𝓗
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝓗 (integrable_of_bound P hfm hfb)
    (fun s _ _ => (integrable_of_bound P hFm' hFb).integrableOn) (fun s hs _ => ?_)
    hFm.aestronglyMeasurable).symm
  have hsm : MeasurableSet s := h𝓗 _ hs
  have hFs : StronglyMeasurable (s.indicator F) := hFm'.indicator hsm
  have hfs : StronglyMeasurable (s.indicator f) := hfm.indicator hsm
  have hFsb : ∀ ω, ‖s.indicator F ω‖ ≤ C := fun ω => by
    by_cases hω : ω ∈ s
    · rw [indicator_of_mem hω]; exact hFb ω
    · rw [indicator_of_notMem hω, norm_zero]; exact (norm_nonneg _).trans (hFb ω)
  have hfsb : ∀ ω, ‖s.indicator f ω‖ ≤ C := fun ω => by
    by_cases hω : ω ∈ s
    · rw [indicator_of_mem hω]; exact hfb ω
    · rw [indicator_of_notMem hω, norm_zero]; exact (norm_nonneg _).trans (hfb ω)
  rw [← integral_indicator hsm, ← integral_indicator hsm,
    ← integral_integral_condExpKernel h𝒢 (integrable_of_bound P hFs hFsb),
    ← integral_integral_condExpKernel h𝒢 (integrable_of_bound P hfs hfsb)]
  refine integral_congr_ae ?_
  filter_upwards [hk] with ω₀ hω₀
  rw [integral_indicator hsm, integral_indicator hsm]
  calc ∫ x in s, F x ∂(condExpKernel P 𝒢 ω₀)
      = ∫ x in s, ((condExpKernel P 𝒢 ω₀)[f | 𝓗]) x ∂(condExpKernel P 𝒢 ω₀) :=
        setIntegral_congr_ae hsm (hω₀.mono fun x hx _ => hx.symm)
    _ = ∫ x in s, f x ∂(condExpKernel P 𝒢 ω₀) :=
        setIntegral_condExp h𝓗 (integrable_of_bound _ hfm hfb) hs

/-- **The transfer on an `𝓗`-event**: if for almost every `ω₀`, `μ_{ω₀}[f | 𝓗] = F` almost surely on `G`, then
`P[f | 𝓗] = F` almost surely on `G`. -/
theorem ae_condExp_eq_on_of_ae_condExpKernel (h𝒢 : 𝒢 ≤ mΩ) (h𝓗 : 𝓗 ≤ mΩ) {f F : Ω → ℂ} {C : ℝ}
    (hfm : StronglyMeasurable f) (hfb : ∀ ω, ‖f ω‖ ≤ C) (hFm : StronglyMeasurable[𝓗] F) (hFb : ∀ ω, ‖F ω‖ ≤ C)
    {G : Set Ω} (hG : MeasurableSet[𝓗] G)
    (hk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ G → (condExpKernel P 𝒢 ω₀)[f | 𝓗] ω = F ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[f | 𝓗] ω = F ω := by
  have hGm : MeasurableSet G := h𝓗 _ hG
  have hfG : StronglyMeasurable (G.indicator f) := hfm.indicator hGm
  have hFG : StronglyMeasurable[𝓗] (G.indicator F) := hFm.indicator hG
  have hb : ∀ {g : Ω → ℂ}, (∀ ω, ‖g ω‖ ≤ C) → ∀ ω, ‖G.indicator g ω‖ ≤ C := fun {g} hg ω => by
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]; exact hg ω
    · rw [indicator_of_notMem hω, norm_zero]; exact (norm_nonneg _).trans (hg ω)
  have hmain : P[G.indicator f | 𝓗] =ᵐ[P] G.indicator F := by
    refine ae_condExp_eq_of_ae_condExpKernel h𝒢 h𝓗 hfG (hb hfb) hFG (hb hFb) ?_
    filter_upwards [hk] with ω₀ hω₀
    filter_upwards [condExp_indicator (integrable_of_bound (condExpKernel P 𝒢 ω₀) hfm hfb) hG, hω₀]
      with ω h1 h2
    rw [h1]
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, indicator_of_mem hω]; exact h2 hω
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  filter_upwards [hmain, condExp_indicator (integrable_of_bound P hfm hfb) hG] with ω h1 h2 hω
  rw [h2, indicator_of_mem hω, indicator_of_mem hω] at h1
  exact h1

end InteractingSLE.Theorem14.GW2Scl
