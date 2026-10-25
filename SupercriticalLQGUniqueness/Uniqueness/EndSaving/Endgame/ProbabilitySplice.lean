import Mathlib




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

 
theorem probability_splice
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A T B : Set Ω) (η : Set.Ioo (0 : ℝ) 1)
    (hsub : A ⊆ T ∪ B)
    (hA : ENNReal.ofReal (1 - (η : ℝ) / 2) ≤ P A)
    (hB : P B ≤ ENNReal.ofReal ((η : ℝ) / 2)) :
    ENNReal.ofReal (1 - (η : ℝ)) ≤ P T := by
  have hη : 0 ≤ (η : ℝ) / 2 := by have := η.property.1; linarith
  have hsubη : 0 ≤ 1 - (η : ℝ) / 2 := by have := η.property.2; linarith
  have hone : (1 : ℝ≥0∞) ≤ P T + ENNReal.ofReal (η : ℝ) := by
    calc
      1 = ENNReal.ofReal (1 - (η : ℝ) / 2) + ENNReal.ofReal ((η : ℝ) / 2) := by
        rw [← ENNReal.ofReal_add hsubη hη]
        norm_num
      _ ≤ P A + ENNReal.ofReal ((η : ℝ) / 2) := add_le_add hA le_rfl
      _ ≤ P (T ∪ B) + ENNReal.ofReal ((η : ℝ) / 2) :=
        add_le_add (measure_mono hsub) le_rfl
      _ ≤ P T + P B + ENNReal.ofReal ((η : ℝ) / 2) :=
        add_le_add (measure_union_le _ _) le_rfl
      _ ≤ P T + ENNReal.ofReal ((η : ℝ) / 2) + ENNReal.ofReal ((η : ℝ) / 2) := by
        exact add_le_add (add_le_add le_rfl hB) le_rfl
      _ = P T + ENNReal.ofReal (η : ℝ) := by
        rw [add_assoc, ← ENNReal.ofReal_add hη hη]
        rw [show (η : ℝ) / 2 + (η : ℝ) / 2 = (η : ℝ) by ring]
  rw [ENNReal.ofReal_sub 1 η.property.1.le, ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr hone

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
