import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.C45GridBound




 
set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

theorem windowGrid_card_le_half_power
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧
      ∀ (R : EndSaving.Interfaces.AdmissibleRadii) (b : Set.Ioi (0 : ℝ))
        (ε : ℝ) (hε : 0 < ε), x₀ ≤ ε⁻¹ →
        ((windowGrid R ξ Q ε hε b).card : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ) := by
  set c' := (ξ : ℝ) * (2 * (Q + 3) - min (Q - 3) (2 * (Q - 3)))
  have hc'0 : 0 < c' := by
    have hm := min_le_left (Q - 3) (2 * (Q - 3))
    have : 0 < 2 * (Q + 3) - min (Q - 3) (2 * (Q - 3)) := by linarith
    exact mul_pos ξ.property this
  set C₁ := 3 * (2 * c' + 2)
  have hC₁0 : 0 < C₁ := by positivity
  set δ := C₁⁻¹
  have hδ0 : 0 < δ := inv_pos.mpr hC₁0
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).def hδ0
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨max (max x₁ (Real.exp 1)) 1, le_max_right _ _, ?_⟩
  intro R b ε hε hx
  set x := ε⁻¹
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hxe : Real.exp 1 ≤ x :=
    (le_max_right x₁ (Real.exp 1)).trans ((le_max_left _ _).trans hx)
  have hxx₁ : x₁ ≤ x :=
    (le_max_left x₁ (Real.exp 1)).trans ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hε1 : ε ≤ 1 := (one_le_inv₀ hε).mp hx1
  set L := Real.log x
  have hL1 : 1 ≤ L := by
    rw [show L = Real.log x from rfl, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxe
  have hlog8 : 1 ≤ Real.log 8 := by
    have h := Real.exp_one_lt_d9
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hb8 : Real.logb 8 x ≤ L := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hb2 : Real.logb 2 x ≤ 2 * L := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hb2n : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hmB : EndSaving.CorrectedChoices.mBox ξ Q ε ≤ C₁ * L ^ 2 := by
    rw [EndSaving.CorrectedChoices.mBox_eq hε hε1 ξ.property hQ, ← show x = ε⁻¹ from rfl]
    have h1 : Real.logb 8 x + 2 ≤ 3 * L := by linarith
    have h2 : c' * Real.logb 2 x + 2 ≤ (2 * c' + 2) * L := by
      dsimp [c']
      nlinarith
    calc
      (Real.logb 8 x + 2) * (c' * Real.logb 2 x + 2)
          ≤ (3 * L) * ((2 * c' + 2) * L) := by
            apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C₁ * L ^ 2 := by dsimp [C₁]; ring
  have hsq : L ^ 2 ≤ δ * x ^ (1 / 2 : ℝ) := by
    have h := hx₁ x hxx₁
    have hLn : 0 ≤ L := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hLn _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at h
    rwa [show L ^ (2 : ℝ) = L ^ 2 by norm_cast] at h
  have hmBhalf : EndSaving.CorrectedChoices.mBox ξ Q ε ≤ x ^ (1 / 2 : ℝ) := by
    calc
      EndSaving.CorrectedChoices.mBox ξ Q ε ≤ C₁ * L ^ 2 := hmB
      _ ≤ C₁ * (δ * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq hC₁0.le
      _ = x ^ (1 / 2 : ℝ) := by simp [δ, hC₁0.ne']
  exact (windowGrid_card_le R ξ Q hε hε1 b).trans hmBhalf

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
