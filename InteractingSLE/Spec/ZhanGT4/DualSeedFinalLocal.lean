/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalErrors
import InteractingSLE.Spec.ZhanGT4.DualSeedLawInterval

/-!
# Removing coefficient and Taylor localization path by path

Packet PROVE-ZHAN-GT4-A22. No measurable choice of a path-dependent
bound is needed: clip at each integer and intersect countably many
probability-one events.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w : ℝ≥0 → Ω → ℝ}

/-- Integer clipping of an adapted real coefficient. -/
def seedClip (w : ℝ≥0 → Ω → ℝ) (k : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  max (-(k : ℝ)) (min (k : ℝ) (w u ω))

/-- Clipping preserves adaptedness. -/
theorem seedClip_adapted (hw : StronglyAdapted 𝓕 w) (k : ℕ) :
    StronglyAdapted 𝓕 (seedClip w k) := fun u =>
  (measurable_const.max (measurable_const.min (hw u).measurable)).stronglyMeasurable

/-- The clipped coefficient is bounded by its clipping level. -/
theorem abs_seedClip_le (w : ℝ≥0 → Ω → ℝ) (k : ℕ) (u : ℝ≥0) (ω : Ω) :
    |seedClip w k u ω| ≤ k := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Clipping fixes every value already within the prescribed bounds. -/
theorem seedClip_eq {k : ℕ} {u : ℝ≥0} {ω : Ω} (hb : |w u ω| ≤ k) :
    seedClip w k u ω = w u ω := by
  rw [seedClip, min_eq_right (abs_le.1 hb).2, max_eq_right (abs_le.1 hb).1]

/-- A pathwise bounded adapted coefficient has vanishing quadratic error.
The bound may be random and need not be integrable or measurable. -/
theorem seedQuadraticError_tendsto_ae_of_pathwiseBounded
    (hB : IsFilteredPreBrownian B 𝓕 P) (hw : StronglyAdapted 𝓕 w) (t : ℝ≥0)
    (hloc : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ u ≤ t, |w u ω| ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun n => seedQuadraticError B w n t ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Tendsto (fun n => seedQuadraticError B (seedClip w k) n t ω) atTop (𝓝 0) :=
    ae_all_iff.2 fun k => seedQuadraticError_tendsto_ae hB (seedClip_adapted hw k)
      (Nat.cast_nonneg k) (abs_seedClip_le w k) t
  filter_upwards [hall, hloc] with ω hω ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_ge C
  have heq (n : ℕ) : seedQuadraticError B (seedClip w k) n t ω =
      seedQuadraticError B w n t ω := by
    unfold seedQuadraticError
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [seedClip_eq ((hC _ (min_le_right _ _)).trans hk)]
  simpa only [heq] using hω k

/-- A cubic-plus-vanishing-remainder estimate may use a different finite
constant on every path, and need hold only for sufficiently fine meshes. -/
theorem seedTaylorError_tendsto_ae_of_pathwiseBounded
    (hB : IsFilteredBrownianReal 𝓕 B P) {E : ℕ → Ω → ℝ} (t : ℝ≥0)
    (he : ∀ᵐ ω ∂P, ∃ (C : ℝ) (R : ℕ → ℝ),
      Tendsto R atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, |E n ω| ≤ C * seedCubicError B n t ω + R n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 0) := by
  filter_upwards [seedCubicError_tendsto_ae hB t, he] with ω hω ⟨C, R, hR, hb⟩
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hu := (hω.const_mul C).add hR
  simp only [mul_zero, add_zero] at hu
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (by
    simpa only [Real.norm_eq_abs] using hb) hu

end InteractingSLE.ZhanGT4
