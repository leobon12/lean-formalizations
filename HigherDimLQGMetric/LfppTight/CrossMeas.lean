import HigherDimLQGMetric.LfppTight.CrossGeom
import LQGMetric.Meas.CR

/-! Borel measurability of the crossing observable on continuous pair functions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_measurable_supPairs {d : ℕ} (A : Set (Rd d)) :
    Measurable fun D : C(Rd d × Rd d, ℝ) => supPairs D A := by
  have he : (fun D : C(Rd d × Rd d, ℝ) => supPairs D A) =
      fun D => ⨆ p ∈ A ×ˢ A, ENNReal.ofReal (D p) := by
    funext D
    unfold supPairs
    rw [biSup_prod]
  rw [he]
  refine LQGMetric.measurable_biSup_of_continuous
    (f := fun (D : C(Rd d × Rd d, ℝ)) (p : Rd d × Rd d) =>
      ENNReal.ofReal (D p))
    (fun D => ENNReal.continuous_ofReal.comp D.continuous) (fun p => ?_) _
  exact (ENNReal.continuous_ofReal.comp (continuous_eval_const p)).measurable

theorem l6a_measurable_infPairs {d : ℕ} (A B : Set (Rd d)) :
    Measurable fun D : C(Rd d × Rd d, ℝ) => infPairs D A B := by
  have he : (fun D : C(Rd d × Rd d, ℝ) => infPairs D A B) =
      fun D => ⨅ p ∈ A ×ˢ B, ENNReal.ofReal (D p) := by
    funext D
    unfold infPairs
    rw [biInf_prod]
  rw [he]
  refine LQGMetric.measurable_biInf_of_continuous
    (f := fun (D : C(Rd d × Rd d, ℝ)) (p : Rd d × Rd d) =>
      ENNReal.ofReal (D p))
    (fun D => ENNReal.continuous_ofReal.comp D.continuous) (fun p => ?_) _
  exact (ENNReal.continuous_ofReal.comp (continuous_eval_const p)).measurable

theorem l6a_measurableSet_cross {d : ℕ} (A B C : Set (Rd d)) (c : ℝ) :
    MeasurableSet {D : C(Rd d × Rd d, ℝ) |
      supPairs D A ≤ ENNReal.ofReal c * infPairs D B C} :=
  measurableSet_le (l6a_measurable_supPairs A)
    (measurable_const.mul (l6a_measurable_infPairs B C))

end HigherDimLQGMetric
