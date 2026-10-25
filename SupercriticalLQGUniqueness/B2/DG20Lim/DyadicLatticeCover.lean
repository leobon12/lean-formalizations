import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeRound

 

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def dyadicRoundCenter (K : ℕ) (z : ℂ) : ℤ × ℤ :=
  (dyadicRoundCoord K z.re, dyadicRoundCoord K z.im)

theorem dyadicRoundCenter_mem_box (R K : ℕ) (z : ℂ)
    (hz : ‖z‖ < (R : ℝ)) :
    dyadicRoundCenter K z ∈ dyadicLatticeBox (R + 1) K := by
  have hre : |z.re| < (R : ℝ) := (Complex.abs_re_le_norm z).trans_lt hz
  have him : |z.im| < (R : ℝ) := (Complex.abs_im_le_norm z).trans_lt hz
  have hre' := dyadicRoundCoord_mem_box R K z.re hre
  have him' := dyadicRoundCoord_mem_box R K z.im him
  change (dyadicRoundCoord K z.re, dyadicRoundCoord K z.im) ∈
    (Finset.Icc (-(((R + 1) * 2 ^ (K + 4) : ℕ) : ℤ))
      (((R + 1) * 2 ^ (K + 4) : ℕ) : ℤ)) ×ˢ
    (Finset.Icc (-(((R + 1) * 2 ^ (K + 4) : ℕ) : ℤ))
      (((R + 1) * 2 ^ (K + 4) : ℕ) : ℤ))
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr hre', Finset.mem_Icc.mpr him'⟩

theorem dyadicRoundCenter_dist_lt (K : ℕ) (z : ℂ) :
    dist z (Complex.mk
      ((dyadicLatticeCenter K (dyadicRoundCenter K z)).1 : ℝ)
      ((dyadicLatticeCenter K (dyadicRoundCenter K z)).2 : ℝ)) <
        2 / (2 : ℝ) ^ (K + 4) := by
  let v := dyadicRoundCenter K z
  let c := Complex.mk ((dyadicLatticeCenter K v).1 : ℝ)
    ((dyadicLatticeCenter K v).2 : ℝ)
  have hre := dyadicRoundCoord_close K z.re
  have him := dyadicRoundCoord_close K z.im
  have hre' : 0 ≤ (z - c).re ∧ (z - c).re < 1 / (2 : ℝ) ^ (K + 4) := by
    simpa [c, v, dyadicLatticeCenter, dyadicRoundCenter] using hre
  have him' : 0 ≤ (z - c).im ∧ (z - c).im < 1 / (2 : ℝ) ^ (K + 4) := by
    simpa [c, v, dyadicLatticeCenter, dyadicRoundCenter] using him
  calc
    dist z c = ‖z - c‖ := dist_eq_norm _ _
    _ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < 2 / (2 : ℝ) ^ (K + 4) := by
      rw [abs_of_nonneg hre'.1, abs_of_nonneg him'.1]
      calc
        (z - c).re + (z - c).im <
            1 / (2 : ℝ) ^ (K + 4) + 1 / (2 : ℝ) ^ (K + 4) :=
          add_lt_add hre'.2 him'.2
        _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Lim
