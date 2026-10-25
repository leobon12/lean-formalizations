import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.ScaledSetGeoCode




 
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem middle_eq_of_triangle_bounds
    (L x y z : ℝ≥0∞) (a b c : ℝ)
    (hL : L ≠ ∞) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1)
    (hx : x ≤ ENNReal.ofReal a * L)
    (hy : y ≤ ENNReal.ofReal b * L)
    (hz : z ≤ ENNReal.ofReal c * L)
    (htri : L ≤ x + y + z) :
    y = ENNReal.ofReal b * L := by
  let A := ENNReal.ofReal a * L
  let B := ENNReal.ofReal b * L
  let C := ENNReal.ofReal c * L
  have hAC : A ≠ ∞ ∧ C ≠ ∞ := by
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL⟩
  have hweight : ENNReal.ofReal a + ENNReal.ofReal b +
      ENNReal.ofReal c = 1 := by
    calc
      _ = ENNReal.ofReal (a + b) + ENNReal.ofReal c := by
        rw [ENNReal.ofReal_add ha hb]
      _ = ENNReal.ofReal (a + b + c) := by
        rw [ENNReal.ofReal_add (add_nonneg ha hb) hc]
      _ = 1 := by rw [hsum]; norm_num
  have hABC : A + B + C = L := by
    calc
      A + B + C = (ENNReal.ofReal a + ENNReal.ofReal b +
          ENNReal.ofReal c) * L := by simp only [A, B, C]; ring
      _ = L := by rw [hweight]; simp
  have htarget : A + B + C ≤ A + y + C := by
    calc
      A + B + C = L := hABC
      _ ≤ x + y + z := htri
      _ ≤ A + y + C := by gcongr
  have hmid : A + B ≤ A + y :=
    ENNReal.le_of_add_le_add_right hAC.2 htarget
  have hB : B ≤ y := ENNReal.le_of_add_le_add_left hAC.1 hmid
  exact le_antisymm hy hB

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
