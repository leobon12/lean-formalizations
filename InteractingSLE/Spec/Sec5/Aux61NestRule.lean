/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ULocStop

/-!
# Nesting of the retained marks at ordered Galmarino rule stops

Packet PROVE-AUX61-NEST. The smaller stopped record is a measurable function of
the larger stopped record. This supplies the marks inclusion needed before
adding the time-zero germ in the Aux. 61 chart argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nest

open Aux61ULoc

variable {X Y R : Type*} [MeasurableSpace Y] [MeasurableSpace R]
  {stop : ℝ≥0 → R → R}

/-- Stopping twice at ordered, possibly infinite times keeps the earlier record. -/
theorem stopAt_stopAt_of_le (hs : IsRecordStop stop) {s t : ℝ≥0∞} (hst : s ≤ t)
    (g : R) : stopAt stop s (stopAt stop t g) = stopAt stop s g := by
  by_cases ht : t < ⊤
  · have hs' : s < ⊤ := hst.trans_lt ht
    have hle : s.toNNReal ≤ t.toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hs'.ne, ENNReal.coe_toNNReal ht.ne]
      exact hst
    simp only [stopAt, ht, hs', ↓reduceIte, hs.stop_stop _ _ _ hle]
  · simp only [stopAt, ht, ↓reduceIte]

omit [MeasurableSpace Y] [MeasurableSpace R] in
/-- A Galmarino rule is unchanged by retaining a later, possibly infinite record. -/
theorem galmarino_stopAt_of_le {ρ : Y × R → ℝ≥0∞}
    (hρ : IsGalmarinoRule stop ρ) {y : Y} {g : R} {t : ℝ≥0∞}
    (hle : ρ (y, g) ≤ t) : ρ (y, stopAt stop t g) = ρ (y, g) := by
  by_cases ht : t < ⊤
  · rw [stopAt, ite_eq_left ht]
    exact hρ y g t.toNNReal (Or.inr (by rwa [ENNReal.coe_toNNReal ht.ne]))
  · simp only [stopAt, ht, ↓reduceIte]

omit [MeasurableSpace Y] in
/-- The earlier rule-stopped record is recovered from the later one by the
same stopping rule. -/
theorem stopAt_rule_of_le (hs : IsRecordStop stop) {ρ σ : Y × R → ℝ≥0∞}
    (hρ : IsGalmarinoRule stop ρ) {y : Y} {g : R} (hle : ρ (y, g) ≤ σ (y, g)) :
    stopAt stop (ρ (y, stopAt stop (σ (y, g)) g)) (stopAt stop (σ (y, g)) g) =
      stopAt stop (ρ (y, g)) g := by
  rw [galmarino_stopAt_of_le hρ hle]
  exact stopAt_stopAt_of_le hs hle g

/-- Ordered Galmarino rule stops have nested retained-record sigma algebras.
Only the earlier rule needs the Galmarino property. -/
theorem ruleMarks_mono (hs : IsRecordStop stop) {ρ σ : Y × R → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsGalmarinoRule stop ρ)
    (hle : ∀ y g, ρ (y, g) ≤ σ (y, g)) (Y₀ : X → Y) (R₀ : X → R) :
    ruleMarks stop ρ Y₀ R₀ ≤ ruleMarks stop σ Y₀ R₀ := by
  have hm : Measurable (fun p : Y × R => (p.1, stopAt stop (ρ p) p.2)) :=
    measurable_fst.prodMk ((measurable_stopAt hs).comp (hρm.prodMk measurable_snd))
  apply MeasurableSpace.comap_le_comap_of_eq_comp _ hm
  funext x
  exact Prod.ext rfl (stopAt_rule_of_le hs hρ (hle (Y₀ x) (R₀ x))).symm

end InteractingSLE.Sec5.Aux61Nest
