/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3D10

/-!
# A concrete two-time field from normalized seed height data

Packet PROVE-ZHAN-GT4-A22. Define the field by the actual normalized
one-height formula, including divided differences at the entrance.
All its finite frozen columns agree with the actual seeded density
by construction, without a separate finite-column agreement hypothesis.
Reciprocity with an opposite-view height family remains a geometric input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι]

/-- The normalized seeded field at own time `s` and frozen height `t`.
The data at every height must be the corresponding actual `SeedData`. -/
def seedHeightField {n : ℕ} (d : ℝ → Ω → SeedData n) (ω : Ω) (s t : ℝ) : ℝ :=
  Real.exp ((d t ω).normEll s - (d t ω).normEll 0)

/-- The concrete height field is strictly positive, including both axes. -/
theorem seedHeightField_pos {n : ℕ} (d : ℝ → Ω → SeedData n) (ω : Ω) (s t : ℝ) :
    0 < seedHeightField d ω s t := Real.exp_pos _

/-- Normalization on the own-time axis holds even for coincident seeds. -/
theorem seedHeightField_zero_left {n : ℕ} (d : ℝ → Ω → SeedData n) (ω : Ω) (t : ℝ) :
    seedHeightField d ω 0 t = 1 := by
  simp only [seedHeightField, sub_self, Real.exp_zero]

/-- The zero-height field is normalized when its identity-chart logarithm
is constant. `normEll_eq_zero_of_identity` below supplies the actual zero. -/
theorem seedHeightField_zero_right {n : ℕ} {d : ℝ → Ω → SeedData n}
    (h0 : ∀ ω s, (d 0 ω).normEll s = (d 0 ω).normEll 0) (ω : Ω) (s : ℝ) :
    seedHeightField d ω s 0 = 1 := by
  simp only [seedHeightField, h0 ω s, sub_self, Real.exp_zero]

omit [Fintype ι] in
/-- Every finite column of the concrete field is the actual stopped seed
density at that height. No finite-compatibility premise is needed. -/
theorem seedHeightField_column_agreement {n : ℕ} (d : ℝ → Ω → SeedData n)
    (S : ι → Ω → ℝ≥0) (H : ι → ℝ) (tb : ℝ) :
    SeedFiniteColumnAgreement (seedHeightField d) S H tb (fun i => d (min (H i) tb)) := by
  intro i u ω
  rfl

/-- Actual one-height density martingales produce finite laws of the
concrete normalized height field. In particular the old abstract finite
column-agreement input is discharged. -/
theorem seed_height_column_law {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (d : ℝ → Ω → SeedData n)
    {S : ι → Ω → ℝ≥0} {H : ι → ℝ} {tb : ℝ}
    (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S i ω : WithTop ℝ≥0))
    (hH : ∀ i, 0 ≤ H i) (i₀ : ι)
    (hM : ∀ i, Martingale (seedDensityProcess (d (min (H i) tb)) (S i)) 𝓕 P)
    (hc : ∀ i ω, Continuous (seedDensityProcess (d (min (H i) tb)) (S i) · ω))
    (hb : ∀ i, ∃ K : ℝ, ∀ u ω,
      Real.exp (-K) ≤ seedDensityProcess (d (min (H i) tb)) (S i) u ω ∧
      seedDensityProcess (d (min (H i) tb)) (S i) u ω ≤ Real.exp K) :
    Martingale (colProd (seedHeightField d) S H tb) 𝓕 P ∧
      (∀ ω u, ContinuousWithinAt (colProd (seedHeightField d) S H tb · ω) (Ici u) u) ∧
      (∃ C : ℝ, ∀ u ω, |colProd (seedHeightField d) S H tb u ω| ≤ C) ∧
      ∀ U : ℝ≥0, (∀ i ω, S i ω ≤ U) →
        (∫ ω, colProdT (seedHeightField d) S H tb ω ∂P) = 1 :=
  seed_finite_column_law hS hH i₀ (seedHeightField_pos d)
    (seedHeightField_column_agreement d S H tb) hM hc hb

/-- Each finite D11 patch agrees with this same explicit density on every
rectangle it contains, independently of the other rectangles in its family. -/
theorem seedHeightField_patch_eq_on_rectangle {n : ℕ} (d : ℝ → Ω → SeedData n)
    {S₁ S₂ : ι → ℝ} (hS₁ : ∀ i, 0 ≤ S₁ i) (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) {i : ι}
    (hsi : s ≤ S₁ i) (hti : t ≤ S₂ i) :
    patch S₁ S₂ (seedHeightField d ω) s t = seedHeightField d ω s t :=
  patch_eq_of_inStair hS₁ (seedHeightField_zero_left d ω) hs hsi hti (seedHeightField_pos d ω s t)

/-- Two finite families agree on each common rectangle, pathwise. This
is density compatibility inside the rectangles; marginal compatibility
of their terminal measures still requires both optional samplings. -/
theorem seedHeightField_patches_eq {n : ℕ} {ι' : Type*} [Fintype ι']
    (d : ℝ → Ω → SeedData n) {S₁ S₂ : ι → ℝ} {T₁ T₂ : ι' → ℝ}
    (hS₁ : ∀ i, 0 ≤ S₁ i) (hT₁ : ∀ i, 0 ≤ T₁ i) (ω : Ω) {s t : ℝ}
    (hs : 0 ≤ s) {i : ι} {j : ι'} (hsi : s ≤ S₁ i) (hti : t ≤ S₂ i)
    (hsj : s ≤ T₁ j) (htj : t ≤ T₂ j) :
    patch S₁ S₂ (seedHeightField d ω) s t = patch T₁ T₂ (seedHeightField d ω) s t := by
  rw [seedHeightField_patch_eq_on_rectangle d hS₁ ω hs hsi hti,
    seedHeightField_patch_eq_on_rectangle d hT₁ ω hs hsj htj]

end InteractingSLE.ZhanGT4
