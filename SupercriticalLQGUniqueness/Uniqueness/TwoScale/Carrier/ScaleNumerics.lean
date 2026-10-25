import Mathlib




 





set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 
def scaleCount (lam α : ℝ) : ℕ :=
  ⌊((1 - α) * (-Real.log lam)) / (2 * Real.log 10)⌋₊

theorem scaleCount_cast_bounds {lam α : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hα1 : α < 1) :
    (scaleCount lam α : ℝ) ≤
        ((1 - α) * (-Real.log lam)) / (2 * Real.log 10) ∧
      ((1 - α) * (-Real.log lam)) / (2 * Real.log 10) <
        (scaleCount lam α : ℝ) + 1 := by
  have hloglam : Real.log lam < 0 := Real.log_neg hlam hlam1
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have ht : 0 ≤ ((1 - α) * (-Real.log lam)) / (2 * Real.log 10) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  exact ⟨Nat.floor_le ht, Nat.lt_floor_add_one _⟩

 

theorem ten_pow_scaleCount_le_rpow {lam α : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hα1 : α < 1) :
    (10 : ℝ) ^ scaleCount lam α ≤ lam ^ (α - 1) := by
  have hloglam : Real.log lam < 0 := Real.log_neg hlam hlam1
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hfloor := (scaleCount_cast_bounds hlam hlam1 hα1).1
  have hp : 0 ≤ (1 - α) * (-Real.log lam) :=
    mul_nonneg (by linarith) (by linarith)
  have hmul : (scaleCount lam α : ℝ) * Real.log 10 ≤
      (1 - α) * (-Real.log lam) / 2 := by
    have h := mul_le_mul_of_nonneg_right hfloor hlog10.le
    have heq : (((1 - α) * (-Real.log lam)) / (2 * Real.log 10)) *
        Real.log 10 = (1 - α) * (-Real.log lam) / 2 := by
      field_simp
    exact h.trans_eq heq
  have hlog : Real.log 10 * (scaleCount lam α : ℝ) ≤
      Real.log lam * (α - 1) := by
    nlinarith [hmul, hp]
  calc
    (10 : ℝ) ^ scaleCount lam α =
        Real.exp (Real.log 10 * (scaleCount lam α : ℝ)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log lam * (α - 1)) := Real.exp_le_exp.mpr hlog
    _ = lam ^ (α - 1) := (Real.rpow_def_of_pos hlam _).symm

 
def scaleBase (lam R α : ℝ) (hlam : 0 < lam) (hR : 0 < R) : Ioi (0 : ℝ) :=
  ⟨2 * lam * R * (10 : ℝ) ^ scaleCount lam α, by
    change 0 < 2 * lam * R * (10 : ℝ) ^ scaleCount lam α
    positivity⟩

theorem scaleBase_last (lam R α : ℝ) :
    ((2 * lam * R * (10 : ℝ) ^ scaleCount lam α) *
      (1 / 10 : ℝ) ^ scaleCount lam α) = 2 * lam * R := by
  calc
    2 * lam * R * (10 : ℝ) ^ scaleCount lam α *
        (1 / 10 : ℝ) ^ scaleCount lam α =
        2 * lam * R * ((10 : ℝ) ^ scaleCount lam α *
          (1 / 10 : ℝ) ^ scaleCount lam α) := by ring
    _ = 2 * lam * R * ((10 : ℝ) * (1 / 10 : ℝ)) ^ scaleCount lam α := by
          rw [mul_pow]
    _ = 2 * lam * R := by norm_num

theorem scaleBase_first (lam R α : ℝ) :
    (2 * lam * R * (10 : ℝ) ^ scaleCount lam α) * (1 / 10 : ℝ) =
      (lam * R * (10 : ℝ) ^ scaleCount lam α) / 5 := by
  ring_nf

 
theorem scaleBase_outer_margin {lam R α : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R)
    (hα1 : α < 1) :
    2 * ((scaleBase lam R α hlam hR : ℝ) * (1 / 10 : ℝ)) + lam * R / 2 ≤
      lam ^ α * R := by
  have hpow := ten_pow_scaleCount_le_rpow hlam hlam1 hα1
  have hla : lam ≤ lam ^ α := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hlam hlam1.le (by linarith : α ≤ 1))
  have heq : lam * lam ^ (α - 1) = lam ^ α := by
    calc
      lam * lam ^ (α - 1) = lam ^ (1 : ℝ) * lam ^ (α - 1) := by rw [Real.rpow_one]
      _ = lam ^ ((1 : ℝ) + (α - 1)) := (Real.rpow_add hlam 1 (α - 1)).symm
      _ = lam ^ α := by ring
  have hmul : lam * (10 : ℝ) ^ scaleCount lam α ≤ lam ^ α := by
    calc
      _ ≤ lam * lam ^ (α - 1) := mul_le_mul_of_nonneg_left hpow hlam.le
      _ = lam ^ α := heq
  have hmulR := mul_le_mul_of_nonneg_right hmul hR.le
  have hlaR := mul_le_mul_of_nonneg_right hla hR.le
  rw [show (scaleBase lam R α hlam hR : ℝ) * (1 / 10 : ℝ) =
    lam * R * (10 : ℝ) ^ scaleCount lam α / 5 by
      exact scaleBase_first lam R α]
  calc
    2 * (lam * R * (10 : ℝ) ^ scaleCount lam α / 5) + lam * R / 2 =
        (2 / 5 : ℝ) * ((lam * (10 : ℝ) ^ scaleCount lam α) * R) +
          (1 / 2 : ℝ) * (lam * R) := by ring
    _ ≤ (2 / 5 : ℝ) * (lam ^ α * R) + (1 / 2 : ℝ) * (lam ^ α * R) := by
      gcongr
    _ ≤ lam ^ α * R := by nlinarith [mul_nonneg (Real.rpow_nonneg hlam.le α) hR.le]

 
def countRate (α : ℝ) : ℝ := 12 * Real.log 10 / (1 - α)

theorem countRate_pos {α : ℝ} (hα1 : α < 1) : 0 < countRate α := by
  unfold countRate
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) (by linarith)

 
theorem exp_count_tail_le_pow_six {lam α : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hα1 : α < 1) :
    Real.exp (-countRate α * (scaleCount lam α : ℝ)) ≤
      Real.exp (countRate α) * lam ^ (6 : ℕ) := by
  have ht := (scaleCount_cast_bounds hlam hlam1 hα1).2
  have ha : 0 < countRate α := countRate_pos hα1
  have hlog10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hα : 1 - α ≠ 0 := (by linarith : 0 < 1 - α).ne'
  have heq : countRate α *
      (((1 - α) * (-Real.log lam)) / (2 * Real.log 10)) =
        -6 * Real.log lam := by
    unfold countRate
    field_simp
    ring
  have hExp : -countRate α * (scaleCount lam α : ℝ) ≤
      countRate α + 6 * Real.log lam := by
    have h := mul_lt_mul_of_pos_left ht ha
    rw [heq] at h
    linarith
  calc
    Real.exp (-countRate α * (scaleCount lam α : ℝ)) ≤
        Real.exp (countRate α + 6 * Real.log lam) := Real.exp_le_exp.mpr hExp
    _ = Real.exp (countRate α) * lam ^ (6 : ℕ) := by
      rw [Real.exp_add]
      congr 1
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlam]
      congr 1
      ring

 
theorem mesh_count_tail_le_pow_four {lam α c : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hα1 : α < 1) (hc : 0 ≤ c) :
    (27 / lam) ^ 2 * (c * Real.exp (-countRate α * (scaleCount lam α : ℝ))) ≤
      (729 * c * Real.exp (countRate α)) * lam ^ (4 : ℕ) := by
  have ht := exp_count_tail_le_pow_six hlam hlam1 hα1
  calc
    (27 / lam) ^ 2 * (c * Real.exp (-countRate α * (scaleCount lam α : ℝ))) ≤
        (27 / lam) ^ 2 * (c * (Real.exp (countRate α) * lam ^ (6 : ℕ))) := by
          gcongr
    _ = (729 * c * Real.exp (countRate α)) * lam ^ (4 : ℕ) := by
      field_simp
      ring

 
def ratioExponent (α c : ℝ) : ℝ :=
  (1 - α) * Real.log (1 + 1 / c) / (16 * Real.log 10)

theorem ratioExponent_pos {α c : ℝ} (hα1 : α < 1) (hc : 0 < c) :
    0 < ratioExponent α c := by
  unfold ratioExponent
  have hb : 1 < 1 + 1 / c := by have := one_div_pos.mpr hc; linarith
  exact div_pos (mul_pos (by linarith) (Real.log_pos hb))
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

 

theorem selected_card_exponent {lam α : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hα1 : α < 1)
    (hlarge : (8 : ℝ) ≤ ((1 - α) * (-Real.log lam)) / (2 * Real.log 10))
    {s : ℕ} (hs : (scaleCount lam α : ℝ) / 2 ≤ (s : ℝ)) :
    ((1 - α) * (-Real.log lam)) / (16 * Real.log 10) ≤
      ((s - 2 : ℕ) : ℝ) := by
  have hN8 : 8 ≤ scaleCount lam α := Nat.le_floor hlarge
  have hN8r : (8 : ℝ) ≤ (scaleCount lam α : ℝ) := by exact_mod_cast hN8
  have hs4r : (4 : ℝ) ≤ (s : ℝ) := by linarith
  have hs4 : 4 ≤ s := by exact_mod_cast hs4r
  have hfloor := (scaleCount_cast_bounds hlam hlam1 hα1).2
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hden : 0 < 16 * Real.log 10 := by positivity
  have hfrac : ((1 - α) * (-Real.log lam)) / (16 * Real.log 10) =
      (((1 - α) * (-Real.log lam)) / (2 * Real.log 10)) / 8 := by
    field_simp
    ring
  rw [hfrac]
  rw [Nat.cast_sub (by omega : 2 ≤ s)]
  norm_num
  simp only [mul_neg] at hfloor ⊢
  linarith only [hfloor, hs, hs4r]

 
theorem gain_pow_lower {lam α c : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hα1 : α < 1) (hc : 0 < c)
    (hlarge : (8 : ℝ) ≤ ((1 - α) * (-Real.log lam)) / (2 * Real.log 10))
    {s : ℕ} (hs : (scaleCount lam α : ℝ) / 2 ≤ (s : ℝ)) :
    lam ^ (-ratioExponent α c) ≤
      (1 + 1 / c) ^ (s - 2 : ℕ) := by
  have hb : 1 < 1 + 1 / c := by have := one_div_pos.mpr hc; linarith
  have hlevel := selected_card_exponent hlam hlam1 hα1 hlarge hs
  have hlog10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hα : 1 - α ≠ 0 := (by linarith : 0 < 1 - α).ne'
  have heq : (1 + 1 / c) ^
      (((1 - α) * (-Real.log lam)) / (16 * Real.log 10)) =
      lam ^ (-ratioExponent α c) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + 1 / c),
      Real.rpow_def_of_pos hlam]
    congr 1
    unfold ratioExponent
    field_simp
  rw [← heq, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hb.le hlevel

 

def scaleCutoff (α c : ℝ) : ℝ :=
  Real.exp (-(max (16 * Real.log 10 / (1 - α))
    (4 * Real.log (c + 1) / ratioExponent α c)))

theorem scaleCutoff_properties {α c lam : ℝ}
    (hα1 : α < 1) (hc : 0 < c) (hlam : 0 < lam)
    (hsmall : lam ≤ scaleCutoff α c) :
    lam < 1 ∧
    (8 : ℝ) ≤ ((1 - α) * (-Real.log lam)) / (2 * Real.log 10) ∧
    c ^ (2 : ℕ) * lam ^ (ratioExponent α c / 2) ≤ 1 := by
  let γ := ratioExponent α c
  have hγ : 0 < γ := ratioExponent_pos hα1 hc
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hα : 0 < 1 - α := by linarith
  have hc1 : 1 < c + 1 := by linarith
  have hlogc : 0 < Real.log (c + 1) := Real.log_pos hc1
  let L := max (16 * Real.log 10 / (1 - α)) (4 * Real.log (c + 1) / γ)
  have hL0 : 0 < L := lt_of_lt_of_le
    (div_pos (mul_pos (by norm_num) hlog10) hα) (le_max_left _ _)
  have hsmall' : lam ≤ Real.exp (-L) := hsmall
  have hlam1 : lam < 1 := lt_of_le_of_lt hsmall'
    (by simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr (neg_neg_of_pos hL0)))
  have hloglam : Real.log lam ≤ -L := by
    have h := Real.log_le_log hlam hsmall'
    simpa only [Real.log_exp] using h
  have hL1 : 16 * Real.log 10 / (1 - α) ≤ -Real.log lam :=
    (le_max_left _ _).trans (by linarith)
  have hlarge : (8 : ℝ) ≤ ((1 - α) * (-Real.log lam)) / (2 * Real.log 10) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 10)).2
    have h := mul_le_mul_of_nonneg_left hL1 hα.le
    have heq : (16 * Real.log 10 / (1 - α)) * (1 - α) =
        16 * Real.log 10 := by field_simp
    rw [mul_comm (1 - α), heq] at h
    linarith only [h]
  have hL2 : 4 * Real.log (c + 1) / γ ≤ -Real.log lam :=
    (le_max_right _ _).trans (by linarith)
  have hexp : 2 * Real.log (c + 1) + (γ / 2) * Real.log lam ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ γ / 2 by positivity)
    have heq : (γ / 2) * (4 * Real.log (c + 1) / γ) =
        2 * Real.log (c + 1) := by field_simp; ring
    rw [heq] at h
    linarith
  have hprod : (c + 1) ^ (2 : ℕ) * lam ^ (γ / 2) ≤ 1 := by
    have heq : (c + 1) ^ (2 : ℕ) * lam ^ (γ / 2) =
        Real.exp (2 * Real.log (c + 1) + (γ / 2) * Real.log lam) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hlam]
      have hpow : Real.exp (2 * Real.log (c + 1)) = (c + 1) ^ (2 : ℕ) := by
        rw [show (2 : ℝ) * Real.log (c + 1) = Real.log (c + 1) * (2 : ℕ) by ring,
          ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith : 0 < c + 1)]
      rw [hpow, mul_comm (Real.log lam) (γ / 2)]
    rw [heq]
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hexp)
  have hsq : c ^ (2 : ℕ) ≤ (c + 1) ^ (2 : ℕ) := by nlinarith
  refine ⟨hlam1, hlarge, ?_⟩
  calc
    c ^ (2 : ℕ) * lam ^ (γ / 2) ≤
        (c + 1) ^ (2 : ℕ) * lam ^ (γ / 2) :=
          mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hlam.le _)
    _ ≤ 1 := hprod

 

theorem ratio_coefficient_le_pow {lam α c : ℝ} {s : ℕ}
    (hα1 : α < 1) (hc : 0 < c) (hlam : 0 < lam)
    (hsmall : lam ≤ scaleCutoff α c)
    (hs : (scaleCount lam α : ℝ) / 2 ≤ (s : ℝ)) :
    c ^ (2 : ℕ) / (1 + 1 / c) ^ (s - 2 : ℕ) ≤
      lam ^ (ratioExponent α c / 2) := by
  obtain ⟨hlam1, hlarge, habsorb⟩ :=
    scaleCutoff_properties hα1 hc hlam hsmall
  let γ := ratioExponent α c
  let β := γ / 2
  let p := (1 + 1 / c) ^ (s - 2 : ℕ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hgain : lam ^ (-γ) ≤ p :=
    gain_pow_lower hlam hlam1 hα1 hc hlarge hs
  have hγpow : 0 ≤ lam ^ γ := Real.rpow_nonneg hlam.le _
  have hprod : (lam ^ (-γ)) * lam ^ γ = 1 := by
    rw [← Real.rpow_add hlam, neg_add_cancel, Real.rpow_zero]
  have hpmul : 1 ≤ p * lam ^ γ := by
    calc
      1 = lam ^ (-γ) * lam ^ γ := hprod.symm
      _ ≤ p * lam ^ γ := mul_le_mul_of_nonneg_right hgain hγpow
  have hcoef : c ^ (2 : ℕ) / p ≤ c ^ (2 : ℕ) * lam ^ γ := by
    apply (div_le_iff₀ hp).2
    calc
      c ^ (2 : ℕ) = c ^ (2 : ℕ) * 1 := by ring
      _ ≤ c ^ (2 : ℕ) * (p * lam ^ γ) :=
        mul_le_mul_of_nonneg_left hpmul (sq_nonneg c)
      _ = c ^ (2 : ℕ) * lam ^ γ * p := by ring
  have hpow : lam ^ γ = lam ^ β * lam ^ β := by
    calc
      lam ^ γ = lam ^ (β + β) := by dsimp [β]; congr 1; ring
      _ = lam ^ β * lam ^ β := Real.rpow_add hlam β β
  calc
    c ^ (2 : ℕ) / p ≤ c ^ (2 : ℕ) * lam ^ γ := hcoef
    _ = (c ^ (2 : ℕ) * lam ^ β) * lam ^ β := by rw [hpow]; ring
    _ ≤ 1 * lam ^ β :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hlam.le _)
    _ = lam ^ β := one_mul _


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
