/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3PrimeRegularize

/-!
# S3: read the actual stage word under its retained kernel

Recover the conditional characteristic functional from the conditional GFF
law of the supplied stage witness. This keeps its word and its exact retained
sigma algebra, rather than selecting an unrelated version of either one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- A conditional word GFF determines the characteristic functional given
that same retained record. -/
theorem ae_condExp_gaussCF_of_kernel {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) {β : Ω → BoundaryWord} {G : Set Ω}
    (hsort : ∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted)
    (hlaw : ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (β ω).fn (β ω).jumps)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ := by
  have hi := GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply φ).comp hY)
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝒢 hi, hsort, hlaw]
    with ω hce hs hl hω
  exact hce.trans (integral_cexp_eq_gaussCF (hs hω) (hl hω) φ)

/-- The actual word of a stage witness gives the Gaussian chart law on its
launch event, with the original past sigma algebra. -/
theorem IsStageWitness.ae_condExp_gaussCF {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hE : IsStagedHistory κ b jumps P h spec E)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hsort : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' φ : ℂ)) |
        pastSigma κ b jumps spec E k] ω = gaussCF (β ω) φ :=
  ae_condExp_gaussCF_of_kernel (hE.2.1 k) hW.2.1 hsort hW.2.2.2 φ

end InteractingSLE.Theorem14.SB.S3
