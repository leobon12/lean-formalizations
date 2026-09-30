import QuantumZipper.Proofs.Zipper.AreaVarFlat
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# W-A-var (2): window densities, the scale partition, and the squeeze in `ℝ≥0∞`

Tools for the sandwich proof of Sheffield–Wang, arXiv:1605.06171, Cor. 3.2 (p. 11) from the
sup/inf window measures of the proof of their Theorem 1.1 (p. 9):

* `winLo N j = 2^{-(j+2)/N}`, `winHi N j = 2^{-j/N}` and the **window densities**
  `supWin γ x N j w = sup_{ρ ∈ [winLo, winHi]} ρ^{γ²/2} e^{γ h_ρ(w)}` and `infWin` (in `ℝ≥0∞`).
  SW's windows `[2^{-(k+1)/N}, 2^{-k/N}]` have one lattice step; ours have two (so that a scale
  function oscillating by less than a factor `2^{1/N}` on a patch stays inside one window for
  every `k`); SW's proof on p. 9 applies verbatim (with `C(N)` built from the supremum of
  `e^{γ B_t − γ² t/2}` over `t ∈ [0, 2 log 2 / N]`).
* `exists_scale_partition`: a finite continuous partition of unity on a compact `K ⊆ U` whose
  pieces are supported where `s ∈ [2^{-m/N}, 2^{-(m-2)/N}]` (mathlib
  `PartitionOfUnity.exists_isSubordinate`).
* `ev_lt_of_upper`, `ev_gt_of_lower`: the squeeze with constants `c N → 1` (SW p. 9, "both `C(N)`
  and `C̲(N)` converge to 1 … The desired result thus follows").

Own elementary bookkeeping (the partition-of-unity localization is the standard way to make
SW's "Using a similar argument" (p. 11) precise).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-- Lower end of the `j`-th window: `2^{-(j+2)/N}`. -/
def winLo (N j : ℕ) : ℝ := (2 : ℝ) ^ (-((j : ℝ) + 2) / N)

/-- Upper end of the `j`-th window: `2^{-j/N}`. -/
def winHi (N j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ) / N)

/-- The supremum of the circle-average area density over the radii of the `j`-th window. -/
def supWin (γ : ℝ) (x : FieldSample) (N j : ℕ) (w : ℂ) : ℝ≥0∞ :=
  ⨆ ρ ∈ Icc (winLo N j) (winHi N j), ENNReal.ofReal (areaDens γ x ρ w)

/-- The infimum of the circle-average area density over the radii of the `j`-th window. -/
def infWin (γ : ℝ) (x : FieldSample) (N j : ℕ) (w : ℂ) : ℝ≥0∞ :=
  ⨅ ρ ∈ Icc (winLo N j) (winHi N j), ENNReal.ofReal (areaDens γ x ρ w)

/-- `radius k * 2^{a} = 2^{a - k}`. -/
theorem radius_mul_rpow (k : ℕ) (a : ℝ) :
    radius k * (2 : ℝ) ^ a = (2 : ℝ) ^ (a - k) := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, radius, inv_pow]
  field_simp

/-- If `s w ∈ [2^{-m/N}, 2^{-(m-2)/N}]` and `kN + m − 2 = j`, then `2^{-k} s w` lies in the `j`-th
window. -/
theorem mem_win_of_scale {N : ℕ} (hN : 1 ≤ N) {m : ℤ} {k j : ℕ}
    (hj : (j : ℤ) = k * N + m - 2) {v : ℝ} (hv : (2 : ℝ) ^ (-(m : ℝ) / N) ≤ v ∧
      v ≤ (2 : ℝ) ^ (-((m : ℝ) - 2) / N)) :
    radius k * v ∈ Icc (winLo N j) (winHi N j) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hjR : (j : ℝ) = k * N + m - 2 := by exact_mod_cast hj
  have hr := radius_pos k
  constructor
  · have e : winLo N j = radius k * (2 : ℝ) ^ (-(m : ℝ) / N) := by
      rw [radius_mul_rpow, winLo, hjR]
      congr 1
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hv.1 hr.le
  · have e : winHi N j = radius k * (2 : ℝ) ^ (-((m : ℝ) - 2) / N) := by
      rw [radius_mul_rpow, winHi, hjR]
      congr 1
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hv.2 hr.le

/-! ### The squeeze in `ℝ≥0∞` -/

end QuantumZipper.E6
