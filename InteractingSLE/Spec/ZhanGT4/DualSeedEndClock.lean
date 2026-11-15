/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandRestart

/-!
# Returning a restarted band to the original clock

Packet PROVE-ZHAN-GT4-A22. Freeze a restarted process before its restart
and kill its coefficients there. Its defects on original-clock cells
after the restart are exactly the restarted defects on translated cells.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*}

/-- A restarted process read on the original clock, constant before `ε`. -/
def seedEndProcess (ε : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  X (r - ε) ω

/-- Its original-clock coefficient vanishes before `ε`. -/
def seedEndCoef (ε : ℝ≥0) (c : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  if ε ≤ r then c (r - ε) ω else 0

/-- Returning the process to the original clock preserves continuity. -/
theorem continuous_seedEndProcess {X : ℝ≥0 → Ω → ℝ} (ε : ℝ≥0) (ω : Ω)
    (hX : Continuous (X · ω)) : Continuous (seedEndProcess ε X · ω) :=
  hX.comp (continuous_id.sub continuous_const)

/-- Returning the coefficient preserves its uniform bound. -/
theorem abs_seedEndCoef_le {c : ℝ≥0 → Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ u ω, |c u ω| ≤ K) (ε r : ℝ≥0) (ω : Ω) : |seedEndCoef ε c r ω| ≤ K := by
  unfold seedEndCoef
  split_ifs
  · exact hc _ _
  · simpa only [abs_zero] using hK

/-- A cell wholly after the restart has exactly the restarted defect. -/
theorem seedEnd_itoDefect_eq {X c₁ c₂ B : ℝ≥0 → Ω → ℝ} {ε a b : ℝ≥0}
    (hεa : ε ≤ a) (hab : a ≤ b) (ω : Ω) :
    Ito.itoDefect (seedEndProcess ε X) (seedEndCoef ε c₁) (seedEndCoef ε c₂) B a b ω =
      Ito.itoDefect X c₁ c₂ (shiftBM B ε) (a - ε) (b - ε) ω := by
  have hεb := hεa.trans hab
  simp only [Ito.itoDefect, seedEndProcess, seedEndCoef, ite_eq_left hεa, shiftBM,
    add_tsub_cancel_of_le hεa, add_tsub_cancel_of_le hεb, NNReal.coe_sub hεa, NNReal.coe_sub hεb]
  ring

/-- Before the restart the process is constant and its defect is zero. -/
theorem seedEnd_itoDefect_eq_zero_before {X c₁ c₂ B : ℝ≥0 → Ω → ℝ} {ε a b : ℝ≥0}
    (hab : a ≤ b) (hb : b ≤ ε) (ω : Ω) :
    Ito.itoDefect (seedEndProcess ε X) (seedEndCoef ε c₁) (seedEndCoef ε c₂) B a b ω = 0 := by
  rcases lt_or_eq_of_le (hab.trans hb) with ha | ha
  · simp only [Ito.itoDefect, seedEndProcess, seedEndCoef, not_le_of_gt ha, ite_false,
      tsub_eq_zero_of_le ha.le, tsub_eq_zero_of_le hb, sub_self, zero_mul, mul_zero]
  · have he : b = a := le_antisymm (hb.trans ha.symm.le) hab
    subst b
    simp only [Ito.itoDefect, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

end InteractingSLE.ZhanGT4
