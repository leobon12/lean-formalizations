/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Times
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly

/-!
# Continuity of an actual source column on its closed real interval

PROVE-ZHAN-GT4-A22. A direct adapter from the landed source-column calculus.
The normalized divided differences include the fused entrance at own time zero.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4.A1EightSeed
open A1SeedField

/-- Source-column calculus gives closed-interval continuity of the normalized
density without requiring an additional continuity premise at the seed entrance. -/
theorem continuousOn_density_of_source_column {X : Type*} {mX : MeasurableSpace X} {n : ℕ}
    {H₁ H₂ : Set ℂ} {δ p q dd Tm κ t : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} {W₂ : ℝ → ℝ}
    {sdata : X → SeedData n} {Vlo Vhi : X → ℝ → ℝ} {T : X → ℝ≥0} {B D : ℝ≥0 → X → ℝ}
    (hp : IsProtectedPair H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (hrec : ∀ x, IsSourceRecord H₁ H₂ p Tm κ rr W₂ t (sdata x) (Vlo x) (Vhi x) (T x))
    (hT : IsStoppingTime 𝓕 fun x => (T x : WithTop ℝ≥0))
    (hst : IsColumnStoch 𝓕 P κ sdata T B D) (x : X) :
    ContinuousOn (fun u => Real.exp ((sdata x).normEll u - (sdata x).normEll 0)) (Icc (0 : ℝ) (T x)) := by
  have : IsProbabilityMeasure P := hst.1.isProbabilityMeasure'
  have hc := ((isSourceColumn_of_stoch hrec hT hst).calculus hp hκ).2 x
  apply A1Patch.continuousOn_of_continuous_stopped
  exact hc

end InteractingSLE.ZhanGT4.A1EightSeed
