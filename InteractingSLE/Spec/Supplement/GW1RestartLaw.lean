/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairParam
import InteractingSLE.Spec.Restart.StoppedK2
import InteractingSLE.Spec.Sec7.LocalExtJWord

/-!
# BW1: an infinite relative stopped coupling is a complete coupling

The stopped K2 produces the full optional specification through its stop. Once
the relative lifetime is infinite, no extension theorem or additional kernel
assumption is required. The local path's maximality clauses are then vacuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartLaw

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A local evolution with almost surely infinite lifetime is maximal. -/
theorem isIntegratedSLEEvolution_of_upTo_ae_top
    (h : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  refine ⟨h.brownian, h.adapted_W, h.adapted_VL, h.adapted_VR, ?_⟩
  filter_upwards [h.ae_path, hζ] with ω hp ht
  rw [ht] at hp ⊢
  exact LocalExt.isIntegratedSLEPath_top_of_isSLEPathUpTo hp

/-- The full stopped optional specification becomes the frozen complete one at
infinite relative lifetime. The actual lifetime variable is preserved. -/
theorem isOptionalHullCoupling_of_stopped_ae_top
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hc : Restart.StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨he, -, hm, hg, hX, ho⟩ := hc
  refine ⟨isIntegratedSLEEvolution_of_upTo_ae_top he hζ, hm, hg, hX, ?_⟩
  intro τ hτ hτζ
  apply ho τ hτ
  filter_upwards [hτζ] with ω ht
  exact ⟨ht.le, fun heq => by rw [heq] at ht; exact not_lt_of_ge le_top ht⟩

/-- In the counterflow frame the same completion gives precisely the frozen
centered counterflow driver, including all finite relative optional kernels. -/
theorem isCenteredCounterflowDriver_of_stopped_ae_top
    {b : ℝ → ℝ} {jumps : Finset ℝ}
    {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {VL' : Fin (flowLineNL b jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR' : Fin (flowLineNR b jumps 0) → ℝ≥0 → Ω → ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hc : Restart.StoppedExtend.IsStoppedHullCoupling (16 / κ)
      (flowLineXL b jumps 0) (flowLineXR b jumps 0)
      (flowLineRhoL (16 / κ) b jumps 0 0) (flowLineRhoR (16 / κ) b jumps 0 0)
      P 𝓕 W VL' VR' B ζ h') (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsCenteredCounterflowDriver κ P h W ζ := by
  refine ⟨b, jumps, h', hb, htr, h', 𝓕, VL', VR', B, ?_,
    isOptionalHullCoupling_of_stopped_ae_top hc hζ⟩
  intro ω φ φ' hφ
  have he : φ' = φ := by
    ext z
    simpa only [Complex.ofReal_zero, add_zero] using hφ z
  subst φ'
  simp only [zero_mul, add_zero]

end InteractingSLE.Theorem14.GW1RestartLaw
