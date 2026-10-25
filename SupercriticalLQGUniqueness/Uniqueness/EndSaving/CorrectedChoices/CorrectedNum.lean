import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChoicesNumV2




 








set_option autoImplicit false

noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CorrectedChoices

open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
def mBox (ξ Q ε : ℝ) : ℝ :=
  (Real.logb 8 ε⁻¹ + 2) *
    max 0 (Real.logb 2 (ε ^ (ξ * min (Q - 3) (2 * (Q - 3)))) - Real.logb 2 ((1 / 2) * ε ^ (2 * ξ * (Q + 3))) + 1)

theorem mBox_eq {ξ Q ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hξ : 0 < ξ) (hQ : 0 < Q) :
    mBox ξ Q ε = (Real.logb 8 ε⁻¹ + 2) * (ξ * (2 * (Q + 3) - min (Q - 3) (2 * (Q - 3))) * Real.logb 2 ε⁻¹ + 2) := by
  unfold mBox
  have hl : 0 ≤ Real.logb 2 ε⁻¹ :=
    Real.logb_nonneg (by norm_num) ((one_le_inv₀ hε).mpr hε1)
  have h1 : Real.logb 2 (ε ^ (ξ * min (Q - 3) (2 * (Q - 3)))) = -(ξ * min (Q - 3) (2 * (Q - 3))) * Real.logb 2 ε⁻¹ := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos hε, Real.logb_inv]; ring
  have h2 : Real.logb 2 ((1 / 2) * ε ^ (2 * ξ * (Q + 3))) =
      -1 - 2 * ξ * (Q + 3) * Real.logb 2 ε⁻¹ := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_rpow_eq_mul_logb_of_pos hε,
      Real.logb_inv, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [h1, h2]
  congr 1
  have hc : 0 ≤ 2 * (Q + 3) - min (Q - 3) (2 * (Q - 3)) := by
    have := min_le_left (Q - 3) (2 * (Q - 3)); linarith
  have : 0 ≤ ξ * (2 * (Q + 3) - min (Q - 3) (2 * (Q - 3))) * Real.logb 2 ε⁻¹ + 2 := by
    have := mul_nonneg (mul_nonneg hξ.le hc) hl
    linarith
  rw [max_eq_right (by nlinarith)]
  ring

theorem mBox_pos {ξ Q ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hξ : 0 < ξ) (hQ : 0 < Q) :
    0 < mBox ξ Q ε := by
  rw [mBox_eq hε hε1 hξ hQ]
  have h8 : 0 ≤ Real.logb 8 ε⁻¹ :=
    Real.logb_nonneg (by norm_num) ((one_le_inv₀ hε).mpr hε1)
  have h2 : 0 ≤ Real.logb 2 ε⁻¹ :=
    Real.logb_nonneg (by norm_num) ((one_le_inv₀ hε).mpr hε1)
  have hm := min_le_left (Q - 3) (2 * (Q - 3))
  have hc : 0 < 2 * (Q + 3) - min (Q - 3) (2 * (Q - 3)) := by linarith
  positivity

 
theorem fiber_bound_eventually {ξ Q η : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) (hη : 0 < η)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ ε : ℝ, 0 < ε → x₀ ≤ ε⁻¹ →
      A * (ε⁻¹) ^ (1 / 2 : ℝ) ≤ ((nLev η ε : ℝ) + 1) / mBox ξ Q ε - 1 := by
  set c' := ξ * (2 * (Q + 3) - min (Q - 3) (2 * (Q - 3))) with hc'
  have hc'0 : 0 < c' := by
    have hm := min_le_left (Q - 3) (2 * (Q - 3))
    have : 0 < 2 * (Q + 3) - min (Q - 3) (2 * (Q - 3)) := by linarith
    exact mul_pos hξ this
  set C₁ := 3 * (2 * c' + 2) with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set δ := η / (88 * C₁ * (A + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).def hδ0
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨max (max x₁ (Real.exp 1)) (max (88 / η) 1), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro ε hε hx
  set x := ε⁻¹ with hxdef
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxη : 88 / η ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hε1 : ε ≤ 1 := (one_le_inv₀ hε).mp hx1
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
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
  have hb8n : 0 ≤ Real.logb 8 x := Real.logb_nonneg (by norm_num) hx1
  have hb2n : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hmB : mBox ξ Q ε ≤ C₁ * L ^ 2 := by
    rw [mBox_eq hε hε1 hξ hQ, ← hxdef, ← hc']
    have h1 : Real.logb 8 x + 2 ≤ 3 * L := by linarith
    have h2 : c' * Real.logb 2 x + 2 ≤ (2 * c' + 2) * L := by nlinarith
    calc (Real.logb 8 x + 2) * (c' * Real.logb 2 x + 2)
        ≤ (3 * L) * ((2 * c' + 2) * L) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C₁ * L ^ 2 := by rw [hC₁]; ring
  have hmBpos := mBox_pos hε hε1 hξ hQ
  
  have hlev : (η / 44) * x - 1 ≤ (nLev η ε : ℝ) + 1 := by
    have h := nLev_add_one_ge (η := η) (ε := ε)
    have heq : (η / 4 - 8 * ε) / (11 * ε) = (η / 44) * x - 8 / 11 := by
      rw [hxdef]; field_simp; ring
    linarith
  
  have hsq : L ^ 2 ≤ δ * x ^ (1 / 2 : ℝ) := by
    have h := hx₁ x hxx₁
    have hLn : 0 ≤ L := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hLn _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at h
    rwa [show L ^ (2 : ℝ) = L ^ 2 by norm_cast] at h
  have hs1 : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hss : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hkey : (A * x ^ (1 / 2 : ℝ) + 1) * (C₁ * L ^ 2) ≤ (η / 44) * x - 1 := by
    have h1 : (A * x ^ (1 / 2 : ℝ) + 1) * (C₁ * L ^ 2) ≤
        ((A + 1) * x ^ (1 / 2 : ℝ)) * (C₁ * (δ * x ^ (1 / 2 : ℝ))) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · nlinarith
      · exact mul_le_mul_of_nonneg_left hsq hC₁0.le
    have h2 : ((A + 1) * x ^ (1 / 2 : ℝ)) * (C₁ * (δ * x ^ (1 / 2 : ℝ))) = (η / 88) * x := by
      rw [show ((A + 1) * x ^ (1 / 2 : ℝ)) * (C₁ * (δ * x ^ (1 / 2 : ℝ))) =
        (A + 1) * C₁ * δ * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) by ring, hss, hδ]
      field_simp
    have h3 : (η / 88) * x ≤ (η / 44) * x - 1 := by
      have := (div_le_iff₀ hη).mp hxη
      nlinarith
    linarith
  rw [le_sub_iff_add_le, le_div_iff₀ hmBpos]
  have hnum : 0 ≤ (η / 44) * x - 1 := by
    have := (div_le_iff₀ hη).mp hxη
    nlinarith
  calc (A * x ^ (1 / 2 : ℝ) + 1) * mBox ξ Q ε
      ≤ (A * x ^ (1 / 2 : ℝ) + 1) * (C₁ * L ^ 2) := by
        apply mul_le_mul_of_nonneg_left hmB (by positivity)
    _ ≤ (η / 44) * x - 1 := hkey
    _ ≤ (nLev η ε : ℝ) + 1 := hlev


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CorrectedChoices
