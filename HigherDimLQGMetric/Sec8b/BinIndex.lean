import Mathlib.Analysis.SpecialFunctions.Log.Base
import HigherDimLQGMetric.ScaleBin.Lemma81

/-! A finite dyadic index set for one scale-bin interval. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

/-- The finite dyadic bins meeting `[lo,hi]`; the extra endpoint bins make
later bounds insensitive to equality at the endpoints. -/
def s7b_binIndices (lo hi : ℝ) : Finset ℤ :=
  Finset.Icc (Int.floor (Real.logb 2 lo) - 1)
    (Int.floor (Real.logb 2 hi) + 1)

/-- Every positive number in `[lo,hi]` lies in a bin whose index belongs to
`s7b_binIndices lo hi`. -/
theorem s7b_exists_bin {lo hi t : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (ht : lo ≤ t ∧ t ≤ hi) :
    ∃ i ∈ s7b_binIndices lo hi,
      0 < (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ t ∧ t ≤ 2 * (2 : ℝ) ^ i := by
  have htpos : 0 < t := lt_of_lt_of_le hlo ht.1
  let i : ℤ := Int.floor (Real.logb 2 t)
  have hloglo : Real.logb 2 lo ≤ Real.logb 2 t :=
    (Real.logb_le_logb (by norm_num) hlo htpos).mpr ht.1
  have hloghi : Real.logb 2 t ≤ Real.logb 2 hi :=
    (Real.logb_le_logb (by norm_num) htpos hhi).mpr ht.2
  have himem : i ∈ s7b_binIndices lo hi := by
    simp only [s7b_binIndices, Finset.mem_Icc]
    constructor
    · have hfloor := Int.floor_mono hloglo
      dsimp [i]
      omega
    · have hfloor := Int.floor_mono hloghi
      dsimp [i]
      omega
  have hlow : (2 : ℝ) ^ i ≤ t := by
    have hlog : (i : ℝ) ≤ Real.logb 2 t := Int.floor_le _
    rw [← Real.rpow_intCast]
    exact (Real.le_logb_iff_rpow_le (by norm_num) htpos).mp hlog
  have hupp : t ≤ 2 * (2 : ℝ) ^ i := by
    have hlog : Real.logb 2 t ≤ (i : ℝ) + 1 :=
      (Int.lt_floor_add_one _).le
    have hpow := (Real.logb_le_iff_le_rpow (by norm_num) htpos).mp hlog
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast,
      Real.rpow_one, mul_comm] at hpow
    exact hpow
  exact ⟨i, himem, zpow_pos (by norm_num) i, hlow, hupp⟩

end HigherDimLQGMetric
