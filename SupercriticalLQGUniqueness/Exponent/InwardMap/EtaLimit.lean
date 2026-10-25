import SupercriticalLQGUniqueness.Exponent.InwardMap.GradientSup




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

theorem le_mul_of_forall_eta (X K : ℝ≥0∞) (C : ℝ) (hC : 0 < C)
    (h : ∀ η : ℝ, 0 < η →
      X ≤ ENNReal.ofReal C * (K + ENNReal.ofReal η)) :
    X ≤ ENNReal.ofReal C * K := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let η : ℝ := (ε:ℝ) / C
  have hη : 0 < η := div_pos (by exact_mod_cast hε) hC
  calc
    X ≤ ENNReal.ofReal C * (K + ENNReal.ofReal η) := h η hη
    _ = ENNReal.ofReal C * K + (ε:ℝ≥0∞) := by
      rw [mul_add, ← ENNReal.ofReal_mul hC.le]
      have heq : C * η = (ε:ℝ) := by
        dsimp [η]
        field_simp
      rw [heq, ENNReal.ofReal_coe_nnreal]


end SupercriticalLQGUniqueness.Exponent.InwardMap
