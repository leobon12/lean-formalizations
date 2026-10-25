import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.ScaleNumerics




 






set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 

theorem finite_cost_gain_to_ratio
    (C A Xj Xi Y : ℝ≥0∞) (n : ℕ)
    (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hXj : Xj ≠ ∞) (hXi : Xi ≠ ∞) (hY : Y ≠ ∞)
    (hA : A ≤ Xj) (houter : Xi ≤ C * Y)
    (hgrowth : (1 / C.toReal) * (1 + 1 / C.toReal) ^ n * Xj.toReal ≤ Xi.toReal) :
    A.toReal ≤
      (C.toReal ^ 2 / (1 + 1 / C.toReal) ^ n) * Y.toReal := by
  have hAfin : A ≠ ∞ := by
    intro htop
    exact hXj (top_unique (by simpa only [htop] using hA))
  have hCYfin : C * Y ≠ ∞ := ENNReal.mul_ne_top hCtop hY
  have hAre : A.toReal ≤ Xj.toReal :=
    (ENNReal.toReal_le_toReal hAfin hXj).2 hA
  have hOuterRe : Xi.toReal ≤ C.toReal * Y.toReal := by
    have h := (ENNReal.toReal_le_toReal hXi hCYfin).2 houter
    rwa [ENNReal.toReal_mul] at h
  have hc : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  let p : ℝ := (1 + 1 / C.toReal) ^ n
  have hp : 0 < p := by dsimp [p]; positivity
  have hgain : (1 / C.toReal) * p * A.toReal ≤ C.toReal * Y.toReal := by
    calc
      (1 / C.toReal) * p * A.toReal ≤
          (1 / C.toReal) * p * Xj.toReal := by gcongr
      _ ≤ Xi.toReal := hgrowth
      _ ≤ C.toReal * Y.toReal := hOuterRe
  have hgainpos : 0 < (1 / C.toReal) * p := mul_pos (one_div_pos.mpr hc) hp
  have hdiv : A.toReal ≤ (C.toReal * Y.toReal) / ((1 / C.toReal) * p) :=
    (le_div_iff₀ hgainpos).2 (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hgain)
  calc
    A.toReal ≤ (C.toReal * Y.toReal) / ((1 / C.toReal) * p) := hdiv
    _ = (C.toReal ^ 2 / p) * Y.toReal := by
      field_simp

 

theorem finite_cost_gain_to_scaled_ratio
    {lam α : ℝ} (hlam : 0 < lam) (hα1 : α < 1)
    (C A Xj Xi Y : ℝ≥0∞) (s : ℕ)
    (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsmall : lam ≤ scaleCutoff α C.toReal)
    (hhalf : (scaleCount lam α : ℝ) / 2 ≤ (s : ℝ))
    (hXj : Xj ≠ ∞) (hXi : Xi ≠ ∞)
    (hA : A ≤ Xj) (houter : Xi ≤ C * Y)
    (hgrowth : (1 / C.toReal) * (1 + 1 / C.toReal) ^ (s - 2) *
      Xj.toReal ≤ Xi.toReal) :
    A ≤ ENNReal.ofReal (lam ^ (ratioExponent α C.toReal / 2)) * Y := by
  have hc : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hβ : 0 < lam ^ (ratioExponent α C.toReal / 2) :=
    Real.rpow_pos_of_pos hlam _
  have hcoeff : ENNReal.ofReal (lam ^ (ratioExponent α C.toReal / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ).ne'
  by_cases hY : Y = ∞
  · rw [hY, ENNReal.mul_top hcoeff]
    exact le_top
  have hAfin : A ≠ ∞ := by
    intro htop
    exact hXj (top_unique (by simpa only [htop] using hA))
  have hreal := finite_cost_gain_to_ratio C A Xj Xi Y (s - 2)
    hC0 hCtop hXj hXi hY hA houter hgrowth
  have hcoef := ratio_coefficient_le_pow hα1 hc hlam hsmall hhalf
  have hbound : A.toReal ≤
      lam ^ (ratioExponent α C.toReal / 2) * Y.toReal := by
    calc
      A.toReal ≤
          (C.toReal ^ 2 / (1 + 1 / C.toReal) ^ (s - 2)) * Y.toReal := hreal
      _ ≤ lam ^ (ratioExponent α C.toReal / 2) * Y.toReal :=
        mul_le_mul_of_nonneg_right hcoef (ENNReal.toReal_nonneg)
  calc
    A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAfin).symm
    _ ≤ ENNReal.ofReal (lam ^ (ratioExponent α C.toReal / 2) * Y.toReal) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (lam ^ (ratioExponent α C.toReal / 2)) * Y := by
      rw [ENNReal.ofReal_mul hβ.le, ENNReal.ofReal_toReal hY]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
