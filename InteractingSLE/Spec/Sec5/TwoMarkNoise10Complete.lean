/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10First
import InteractingSLE.Spec.Coupling.WholeField5Ext

/-!
# Brownian continuation from a frozen exponential-martingale version

This is a conditional continuation adapter. The frozen noise and clock data
remain an explicit mathematical input; the local martingales and finite endpoint
proved in this continuation are prerequisites for constructing that input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

/-- Frozen exponential-martingale data give a Brownian extension preserving the image filtration. -/
theorem exists_brownian_extension_of_frozen_noise {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 𝓘 : Filtration ℝ≥0 mΩ} {κ a b : ℝ}
    {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e τ : Ω → ℝ≥0∞} {M : ℝ≥0 → Ω → ℝ} {ℓ : ℝ≥0 → Ω → ℝ≥0}
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hTC : Sec6.Prop65.IsTCExpMartingale P 𝓘 M ℓ)
    (hℓ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ℓ u ω = u)
    (hM : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω →
      M u ω = newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
        (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u) :
    ∃ (𝓙 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (β : ℝ≥0 → Ω × Ω → ℝ),
      (∀ u, MeasurableSpace.comap (Prod.fst : Ω × Ω → Ω) (𝓘 u) ≤ 𝓙 u) ∧
      IsFilteredBrownianReal 𝓙 β (P.prod P) ∧
      (∀ p, Continuous (β · p)) ∧
      ∀ᵐ p ∂(P.prod P), ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ p.1 →
        newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
          (W · p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) u = β u p := by
  have := hE.brownian.isProbabilityMeasure'
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, -⟩ := QuantumZipper.RS.exists_good_version0 hE.brownian.1
  have hFB := hB₀.toIsPreBrownianReal.isFilteredPreBrownian hB₀m
  obtain ⟨hβ, hβc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC hFB hB₀c hB₀0
  refine ⟨WholeField.prodFiltration 𝓘 (Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable),
    WholeField.complNoise M ℓ B₀, WholeField.comap_fst_le_prodFiltration _ _, hβ, hβc, ?_⟩
  have hLift := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae (hℓ.and hM)
  filter_upwards [hLift] with p hp u hu
  rw [WholeField.complNoise_of_eq (hp.1 u hu)]
  exact (hp.2 u hu).symm

/-- A frozen version in an enlarged image filtration suffices for compatible Brownian continuation. -/
theorem exists_brownian_extension_of_frozen_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 𝓘 : Filtration ℝ≥0 mΩ} {κ a b : ℝ}
    {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ} {e τ : Ω → ℝ≥0∞}
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hFrozenVersion :
      ∃ (𝓚 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (ℓ : ℝ≥0 → Ω → ℝ≥0),
        (∀ u, 𝓘 u ≤ 𝓚 u) ∧ Sec6.Prop65.IsTCExpMartingale P 𝓚 M ℓ ∧
        (∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ℓ u ω = u) ∧
        ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω →
          M u ω = newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
            (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u) :
    ∃ (𝓙 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (β : ℝ≥0 → Ω × Ω → ℝ),
      (∀ u, MeasurableSpace.comap (Prod.fst : Ω × Ω → Ω) (𝓘 u) ≤ 𝓙 u) ∧
      IsFilteredBrownianReal 𝓙 β (P.prod P) ∧
      (∀ p, Continuous (β · p)) ∧
      ∀ᵐ p ∂(P.prod P), ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ p.1 →
        newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
          (W · p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) u = β u p := by
  obtain ⟨𝓚, M, ℓ, hIK, hTC, hℓ, hM⟩ := hFrozenVersion
  obtain ⟨𝓙, β, hKJ, hβ, hβc, heq⟩ := exists_brownian_extension_of_frozen_noise hE hTC hℓ hM
  exact ⟨𝓙, β, fun u => (MeasurableSpace.comap_mono (hIK u)).trans (hKJ u), hβ, hβc, heq⟩

end InteractingSLE.Sec5.TwoMark.Noise10
