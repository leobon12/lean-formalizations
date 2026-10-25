import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_half_logsq_rate_le {a c t : ℝ}
    (ha : 0 < a) (hc : 0 < c) (ht : 2 < t) :
    Real.exp (-(c * (t / 2) ^ 2 / (a * Real.log (t / 2)))) ≤
      Real.exp (-((c / (4 * a)) * t ^ 2 / Real.log t)) := by
  have ht2 : 1 < t / 2 := by linarith
  have hlog2 : 0 < Real.log (t / 2) := Real.log_pos ht2
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogle : Real.log (t / 2) ≤ Real.log t :=
    Real.log_le_log (by linarith) (by linarith)
  apply Real.exp_le_exp.mpr
  have hden : 0 < a * Real.log (t / 2) := mul_pos ha hlog2
  have hden2 : 0 < 4 * a * Real.log t := by positivity
  have hnum : 0 ≤ c * t ^ 2 := by positivity
  have hq : c * t ^ 2 / (4 * a * Real.log t) ≤
      c * t ^ 2 / (4 * a * Real.log (t / 2)) := by
    apply div_le_div_of_nonneg_left hnum (by positivity : 0 < 4 * a * Real.log (t / 2))
    gcongr
  have heq₁ : c * (t / 2) ^ 2 / (a * Real.log (t / 2)) =
      c * t ^ 2 / (4 * a * Real.log (t / 2)) := by ring
  have heq₂ : (c / (4 * a)) * t ^ 2 / Real.log t =
      c * t ^ 2 / (4 * a * Real.log t) := by ring
  rw [heq₁, heq₂]
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
