import Mathlib.Analysis.MeanInequalities

/-! Finite weighted interpolation in the exact raw-sum normalization of
the mesh-only Nash inequality. -/

open scoped BigOperators Classical

namespace BouRabeeGwynne.MeshOnlySobolev

/-- Weighted Cauchy--Schwarz retains only the volume of nonzero vertices. -/
theorem weighted_l1_sq_le_support_l2 {V : Type*} [Fintype V]
    (m u : V → ℝ) (hm : ∀ v, 0 ≤ m v) :
    (∑ v, m v * |u v|) ^ 2 ≤
      (∑ v, if u v ≠ 0 then m v else 0) * (∑ v, m v * u v ^ 2) := by
  classical
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro v _
    split_ifs
    · exact hm v
    · exact le_rfl
  · intro v _
    exact mul_nonneg (hm v) (sq_nonneg _)
  · intro v _
    by_cases hu : u v = 0
    · simp [hu]
    · simp only [if_pos hu, mul_pow, sq_abs]
      nlinarith only []

theorem sum_geometric_le {V : Type*} [Fintype V] (A B : V → ℝ)
    (hA : ∀ v, 0 ≤ A v) (hB : ∀ v, 0 ≤ B v)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hsum : α + β = 1) :
    (∑ v, A v ^ α * B v ^ β) ≤ (∑ v, A v) ^ α * (∑ v, B v) ^ β := by
  have hholder : Real.HolderConjugate α⁻¹ β⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · apply (one_lt_inv₀ hα).mpr
      linarith
    · simpa using hsum
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun v => A v ^ α) (g := fun v => B v ^ β) hholder
    (fun v _ => Real.rpow_nonneg (hA v) α)
    (fun v _ => Real.rpow_nonneg (hB v) β)
  have hAr (v : V) : (A v ^ α) ^ α⁻¹ = A v := by
    rw [← Real.rpow_mul (hA v), mul_inv_cancel₀ hα.ne', Real.rpow_one]
  have hBr (v : V) : (B v ^ β) ^ β⁻¹ = B v := by
    rw [← Real.rpow_mul (hB v), mul_inv_cancel₀ hβ.ne', Real.rpow_one]
  simp_rw [hAr, hBr] at h
  simpa only [one_div, inv_inv] using h

/-- Interpolating the tile-weighted L² mass between L¹ and the BV Sobolev
exponent. This is the squared form used directly by the Nash estimate. -/
theorem weighted_nash_interpolation {V : Type*} [Fintype V]
    (m u : V → ℝ) (hm : ∀ v, 0 < m v) {d : ℝ} (hd : 1 < d) :
    (∑ v, m v * u v ^ 2) ^ (2 + 2 / d) ≤
      (∑ v, m v * |u v|) ^ (4 / d) *
        (∑ v, m v * |u v| ^ (2 * d / (d - 1))) ^ (2 * (d - 1) / d) := by
  let α : ℝ := 2 / (d + 1)
  let β : ℝ := (d - 1) / (d + 1)
  let q : ℝ := 2 * d / (d - 1)
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d + 1 := by linarith
  have hdm1 : 0 < d - 1 := by linarith
  have hα : 0 < α := div_pos (by norm_num) hd1
  have hβ : 0 < β := div_pos hdm1 hd1
  have hq : 0 < q := div_pos (mul_pos (by norm_num) hd0) hdm1
  have hab : α + β = 1 := by dsimp [α, β]; field_simp [hd1.ne'] <;> ring
  have haq : α + q * β = 2 := by
    dsimp [α, β, q]
    field_simp [hd1.ne', hdm1.ne'] <;> ring
  have hpoint (v : V) :
      (m v * |u v|) ^ α * (m v * |u v| ^ q) ^ β = m v * u v ^ 2 := by
    by_cases hu : u v = 0
    · simp [hu, Real.zero_rpow hα.ne', Real.zero_rpow hq.ne', Real.zero_rpow hβ.ne']
    · have ha : 0 < |u v| := abs_pos.mpr hu
      rw [Real.mul_rpow (hm v).le ha.le,
        Real.mul_rpow (hm v).le (Real.rpow_nonneg ha.le q), ← Real.rpow_mul ha.le]
      calc
        _ = (m v ^ α * m v ^ β) * (|u v| ^ α * |u v| ^ (q * β)) := by ring
        _ = m v ^ (α + β) * |u v| ^ (α + q * β) := by
          rw [Real.rpow_add (hm v), Real.rpow_add ha]
        _ = _ := by rw [hab, haq, Real.rpow_one, Real.rpow_two, sq_abs]
  have h := sum_geometric_le (fun v => m v * |u v|)
    (fun v => m v * |u v| ^ q)
    (fun v => mul_nonneg (hm v).le (abs_nonneg _))
    (fun v => mul_nonneg (hm v).le (Real.rpow_nonneg (abs_nonneg _) q)) hα hβ hab
  simp_rw [hpoint] at h
  have hr : 0 ≤ 2 + 2 / d := by positivity
  have hX : 0 ≤ ∑ v, m v * u v ^ 2 :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hm v).le (sq_nonneg _)
  have hA : 0 ≤ ∑ v, m v * |u v| :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hm v).le (abs_nonneg _)
  have hB : 0 ≤ ∑ v, m v * |u v| ^ q :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hm v).le (Real.rpow_nonneg (abs_nonneg _) _)
  have hpow := Real.rpow_le_rpow hX h hr
  rw [Real.mul_rpow (Real.rpow_nonneg hA α) (Real.rpow_nonneg hB β),
    ← Real.rpow_mul hA, ← Real.rpow_mul hB] at hpow
  have heα : α * (2 + 2 / d) = 4 / d := by
    dsimp [α]
    field_simp [hd1.ne', hd0.ne'] <;> ring
  have heβ : β * (2 + 2 / d) = 2 * (d - 1) / d := by
    dsimp [β]
    field_simp [hd1.ne', hd0.ne'] <;> ring
  rw [heα, heβ] at hpow
  exact hpow

end BouRabeeGwynne.MeshOnlySobolev
