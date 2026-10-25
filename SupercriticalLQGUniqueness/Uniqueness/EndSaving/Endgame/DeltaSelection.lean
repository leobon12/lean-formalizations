import Mathlib




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

theorem endpoint_delta_selection
    (α ν εA εC C η κ : ℝ)
    (hα : 0 < α) (hν : 0 < ν) (hεA : 0 < εA) (hεC : 0 < εC)
    (hC : 0 < C) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ →
        let ε := (2 * δ) ^ α⁻¹
        0 < ε ∧ ε ≤ εA ∧ ε ≤ εC ∧
          δ ^ ν ≤ κ / 4 ∧ δ ^ ν ≤ 1 ∧
          δ ≤ η / (2 * ((203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1))) := by
  let m : ℝ := min εA εC
  have hm : 0 < m := lt_min hεA hεC
  let k : ℝ := (203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1)
  have hk : 0 < k := by dsimp [k]; positivity
  let t : ℝ := min (m ^ α / 2) ((κ / 4) ^ ν⁻¹)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  let δv : ℝ := min t (min (η / (2 * k)) (1 / 2))
  have hδv : 0 < δv := lt_min ht (lt_min (by positivity) (by norm_num))
  have hδv1 : δv < 1 := by
    have h := (min_le_right t (min (η / (2 * k)) (1 / 2))).trans
      (min_le_right (η / (2 * k)) (1 / 2))
    linarith
  refine ⟨⟨δv, hδv, hδv1⟩, ?_⟩
  intro δ hδ hδle
  have hδt : δ ≤ t := hδle.trans (min_le_left _ _)
  have hδlow : δ ≤ (κ / 4) ^ ν⁻¹ := hδt.trans (min_le_right _ _)
  have hδeps : 2 * δ ≤ m ^ α := by
    have h := hδt.trans (min_le_left _ _)
    linarith only [h]
  have hδrate : δ ≤ η / (2 * k) :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδhalf : δ ≤ 1 / 2 :=
    hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεpos : 0 < (2 * δ) ^ α⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  have hεm : (2 * δ) ^ α⁻¹ ≤ m := by
    calc
      (2 * δ) ^ α⁻¹ ≤ (m ^ α) ^ α⁻¹ :=
        Real.rpow_le_rpow (by positivity) hδeps (inv_nonneg.mpr hα.le)
      _ = m := Real.rpow_rpow_inv hm.le hα.ne'
  have hxκ : δ ^ ν ≤ κ / 4 := by
    calc
      δ ^ ν ≤ ((κ / 4) ^ ν⁻¹) ^ ν :=
        Real.rpow_le_rpow hδ.le hδlow hν.le
      _ = κ / 4 := Real.rpow_inv_rpow (by positivity) hν.ne'
  have hx1 : δ ^ ν ≤ 1 := by
    calc
      δ ^ ν ≤ 1 ^ ν := Real.rpow_le_rpow hδ.le (by linarith only [hδhalf]) hν.le
      _ = 1 := by simp
  exact ⟨hεpos, hεm.trans (min_le_left _ _), hεm.trans (min_le_right _ _),
    hxκ, hx1, hδrate⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
