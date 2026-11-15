/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NestRule

/-!
# The comparison stop in the physical slit argument

Packet PROVE-AUX61-SLITW. For a comparison time `q`, the larger union is read at
`max T q`. This is again a Galmarino rule, and its retained records contain both
the records at `T` and the own record at `q`. The event `q ≤ T` is recorded at `T`.
The corresponding unions agree on this event and contain both smaller sets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open Aux61ULoc

section Rules

variable {X Y R : Type*} [MeasurableSpace Y] [MeasurableSpace R]
  {stop : ℝ≥0 → R → R} {ρ : Y × R → ℝ≥0∞}

omit [MeasurableSpace Y] [MeasurableSpace R] in
/-- Raising a rule stop to a deterministic comparison time preserves Galmarino's property. -/
theorem isGalmarinoRule_max (hρ : IsGalmarinoRule stop ρ) (q : ℝ≥0) :
    IsGalmarinoRule stop (fun p => max (ρ p) (q : ℝ≥0∞)) := by
  intro y g t ht
  have he : ρ (y, stop t g) = ρ (y, g) := hρ y g t (ht.imp
    (fun h => (le_max_left _ _).trans h) (fun h => (le_max_left _ _).trans h))
  exact congrArg (fun v => max v (q : ℝ≥0∞)) he

/-- The rule time itself is measurable from its own stopped record. -/
theorem measurable_ruleTime (hρm : Measurable ρ)
    (hρ : IsGalmarinoRule stop ρ) (Y₀ : X → Y) (R₀ : X → R) :
    Measurable[ruleMarks stop ρ Y₀ R₀] (fun x => ρ (Y₀ x, R₀ x)) := by
  have hm := hρm.comp (comap_measurable
    (fun x => (Y₀ x, stopAt stop (ρ (Y₀ x, R₀ x)) (R₀ x))))
  dsimp only [Function.comp_def] at hm
  have he : (fun x => ρ (Y₀ x, stopAt stop (ρ (Y₀ x, R₀ x)) (R₀ x))) =
      (fun x => ρ (Y₀ x, R₀ x)) := by
    funext x
    exact Aux61Nest.galmarino_stopAt_of_le hρ le_rfl
  rw [he] at hm
  exact hm

/-- SLIT's comparison event belongs to the marks at the original rule stop. -/
theorem measurableSet_comparison (hρm : Measurable ρ)
    (hρ : IsGalmarinoRule stop ρ) (Y₀ : X → Y) (R₀ : X → R) (q : ℝ≥0) :
    MeasurableSet[ruleMarks stop ρ Y₀ R₀] {x | (q : ℝ≥0∞) ≤ ρ (Y₀ x, R₀ x)} :=
  measurableSet_le measurable_const (measurable_ruleTime hρm hρ Y₀ R₀)

/-- The larger stop retains the original stopped records. -/
theorem ruleMarks_le_max (hstop : IsRecordStop stop) (hρm : Measurable ρ)
    (hρ : IsGalmarinoRule stop ρ) (Y₀ : X → Y) (R₀ : X → R) (q : ℝ≥0) :
    ruleMarks stop ρ Y₀ R₀ ≤ ruleMarks stop (fun p => max (ρ p) (q : ℝ≥0∞)) Y₀ R₀ :=
  Aux61Nest.ruleMarks_mono hstop hρm hρ (fun _ _ => le_max_left _ _) Y₀ R₀

/-- The larger stop also retains the record at the deterministic comparison time. -/
theorem comparisonMarks_le_max (hstop : IsRecordStop stop) (Y₀ : X → Y) (R₀ : X → R) (q : ℝ≥0) :
    ruleMarks stop (fun _ => (q : ℝ≥0∞)) Y₀ R₀ ≤
      ruleMarks stop (fun p => max (ρ p) (q : ℝ≥0∞)) Y₀ R₀ :=
  Aux61Nest.ruleMarks_mono hstop measurable_const (fun _ _ _ _ => rfl)
    (fun _ _ => le_max_right _ _) Y₀ R₀

end Rules

section Unions

variable {X : Type*} {A : X → Set ℂ} {K : ℝ≥0 → X → Set ℂ}
  {T U : X → ℝ≥0∞}

/-- Ordered physical stops give nested unions; the value at an infinite stop is `H`. -/
theorem unionAt_mono (hK : ∀ x, Monotone (fun t => K t x)) (hTU : ∀ x, T x ≤ U x) (x : X) :
    unionAt A K T x ⊆ unionAt A K U x := by
  by_cases hU : U x < ⊤
  · have hT : T x < ⊤ := (hTU x).trans_lt hU
    simp only [unionAt, hT, hU, ↓reduceIte]
    have hle : (T x).toNNReal ≤ (U x).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hT.ne, ENNReal.coe_toNNReal hU.ne]
      exact hTU x
    exact inter_subset_inter_right _ (union_subset_union_right _ (hK x hle))
  · simp only [unionAt, hU, ↓reduceIte]
    split_ifs
    · exact inter_subset_left
    · exact Subset.rfl

/-- At `max T q` the larger union contains the comparison hull. -/
theorem comparison_subset_unionAt_max (hK : ∀ x, Monotone (fun t => K t x)) (q : ℝ≥0) (x : X) :
    K q x ∩ H ⊆ unionAt A K (fun x => max (T x) (q : ℝ≥0∞)) x := by
  by_cases hT : max (T x) (q : ℝ≥0∞) < ⊤
  · simp only [unionAt, hT, ↓reduceIte]
    have hq : q ≤ (max (T x) (q : ℝ≥0∞)).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hT.ne]
      exact le_max_right _ _
    exact fun _ hz => ⟨hz.2, Or.inr (hK x hq hz.1)⟩
  · simp only [unionAt, hT, ↓reduceIte]
    exact inter_subset_right

/-- On SLIT's comparison event the larger union is exactly the original union. -/
theorem unionAt_max_eq {q : ℝ≥0} {x : X} (hq : (q : ℝ≥0∞) ≤ T x) :
    unionAt A K (fun x => max (T x) (q : ℝ≥0∞)) x = unionAt A K T x := by
  simp only [unionAt, max_eq_left hq]

end Unions

end InteractingSLE.Sec5.Aux61SlitW
