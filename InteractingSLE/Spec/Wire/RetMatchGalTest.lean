/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchGalRead

/-!
# Galmarino's test for the raw state-path filtration

This is the deterministic test of Revuz–Yor I, Exercise (4.21)(1), p. 47.
Mathlib's natural-filtration comap theorem supplies the saturation of its
events. No augmentation or probability measure occurs in the test.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchGal

open LawUnique

variable {nL nR : ℕ}

/-- The raw natural filtration of the coordinate process on complete state paths. -/
def statePathFiltration : Filtration ℝ≥0
    (inferInstance : MeasurableSpace (ℝ≥0 → DrivingValue nL nR)) :=
  Filtration.natural (fun t (w : ℝ≥0 → DrivingValue nL nR) => w t)
    (fun t => (measurable_pi_apply t).stronglyMeasurable)

/-- An event of the raw natural filtration depends only on the closed prefix. -/
theorem mem_iff_of_statePath_prefix {t : ℝ≥0} {A : Set (ℝ≥0 → DrivingValue nL nR)}
    (hA : MeasurableSet[statePathFiltration t] A)
    {w v : ℝ≥0 → DrivingValue nL nR} (hag : ∀ u ≤ t, w u = v u) :
    w ∈ A ↔ v ∈ A := by
  have hcomap : MeasurableSet[MeasurableSpace.comap
      (fun w : ℝ≥0 → DrivingValue nL nR => fun u : Iic t => w u)
      inferInstance] A := by
    have heq := Filtration.natural_eq_comap
      (fun r (w : ℝ≥0 → DrivingValue nL nR) => w r)
      (fun r => (measurable_pi_apply r).stronglyMeasurable) t
    exact heq ▸ hA
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hcomap
  have he : (fun u : Iic t => w u) = fun u : Iic t => v u :=
    funext fun u => hag u u.2
  change (fun u : Iic t => w u) ∈ B ↔ (fun u : Iic t => v u) ∈ B
  rw [he]

/-- A raw stopping sublevel is unchanged when its closed prefix is unchanged. -/
theorem le_of_isStoppingTime_prefix {τ : (ℝ≥0 → DrivingValue nL nR) → WithTop ℝ≥0}
    (hτ : IsStoppingTime statePathFiltration τ)
    {w v : ℝ≥0 → DrivingValue nL nR} {t : ℝ≥0}
    (hag : ∀ u ≤ t, w u = v u) (hle : τ w ≤ t) : τ v ≤ t :=
  (mem_iff_of_statePath_prefix (hτ t) hag).1 hle

/-- Galmarino's test: a raw stopping time is determined by the path through
its value. The proof also applies to arbitrary, possibly discontinuous paths. -/
theorem eq_of_isStoppingTime_prefix {τ : (ℝ≥0 → DrivingValue nL nR) → WithTop ℝ≥0}
    (hτ : IsStoppingTime statePathFiltration τ) (w v : ℝ≥0 → DrivingValue nL nR)
    (hag : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ τ w → w u = v u) : τ v = τ w := by
  apply le_antisymm
  · by_contra hn
    have hlt : τ w < τ v := not_le.1 hn
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hv : τ v ≤ (t : WithTop ℝ≥0) :=
      le_of_isStoppingTime_prefix hτ (fun u hu => hag u
        ((WithTop.coe_le_coe.2 hu).trans_eq ht)) ht.ge
    exact (not_le_of_gt hlt) (hv.trans_eq ht)
  · by_contra hn
    have hlt : τ v < τ w := not_le.1 hn
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hw : τ w ≤ (t : WithTop ℝ≥0) :=
      le_of_isStoppingTime_prefix hτ (fun u hu => (hag u
        ((WithTop.coe_le_coe.2 hu).trans (ht.trans_lt hlt).le)).symm) ht.ge
    exact (not_le_of_gt hlt) (hw.trans_eq ht)

end InteractingSLE.Wire.RetMatchGal
