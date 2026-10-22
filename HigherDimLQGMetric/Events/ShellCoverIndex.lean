import HigherDimLQGMetric.Events.ShellCoverGeom
import HigherDimLQGMetric.ShellDec.Tail

/-!
# Decreasing enumeration of a finite set of shell scales
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)
open MeasureTheory
open scoped ENNReal

def shellCoverIndex (T : Finset ℤ) (hT : T.Nonempty) (i : ℕ) : ℤ :=
  if hi : i < T.card then
    T.orderEmbOfFin rfl ⟨T.card - 1 - i, by omega⟩
  else T.min' hT - ((i - T.card + 1 : ℕ) : ℤ)

theorem shellCoverIndex_mem (T : Finset ℤ) (hT : T.Nonempty)
    {i : ℕ} (hi : i < T.card) : shellCoverIndex T hT i ∈ T := by
  simp only [shellCoverIndex, dite_eq_left hi]
  exact T.orderEmbOfFin_mem rfl _

theorem shellCoverIndex_step (T : Finset ℤ) (hT : T.Nonempty)
    (i : ℕ) : shellCoverIndex T hT (i + 1) + 1 ≤ shellCoverIndex T hT i := by
  by_cases hnext : i + 1 < T.card
  · have hi : i < T.card := by omega
    have hlt : (⟨T.card - 1 - (i + 1), by omega⟩ : Fin T.card) <
        ⟨T.card - 1 - i, by omega⟩ := by simp only [Fin.lt_def]; omega
    have hstrict := (T.orderEmbOfFin rfl).strictMono hlt
    simp only [shellCoverIndex, dite_eq_left hi, dite_eq_left hnext]
    omega
  · by_cases hi : i < T.card
    · have heq : i + 1 = T.card := by omega
      have hmem := shellCoverIndex_mem T hT hi
      have hmin : T.min' hT ≤ shellCoverIndex T hT i := Finset.min'_le T _ hmem
      simp only [shellCoverIndex, dite_eq_left hi] at hmin
      simp only [shellCoverIndex, dite_eq_right hnext, dite_eq_left hi]
      omega
    · simp only [shellCoverIndex, dite_eq_right hi, dite_eq_right hnext]
      omega

theorem shellCoverIndex_zpow_step (T : Finset ℤ) (hT : T.Nonempty)
    (i : ℕ) : (64 : ℝ) ^ shellCoverIndex T hT (i + 1) ≤
      (1 / 64 : ℝ) * (64 : ℝ) ^ shellCoverIndex T hT i := by
  have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 64)
    (shellCoverIndex_step T hT i)
  calc
    (64 : ℝ) ^ shellCoverIndex T hT (i + 1) =
        (1 / 64 : ℝ) * (64 : ℝ) ^ (shellCoverIndex T hT (i + 1) + 1) := by
          rw [zpow_add_one₀ (by norm_num : (64 : ℝ) ≠ 0)]
          ring
    _ ≤ (1 / 64 : ℝ) * (64 : ℝ) ^ shellCoverIndex T hT i :=
      mul_le_mul_of_nonneg_left h (by norm_num)

end HigherDimLQGMetric
