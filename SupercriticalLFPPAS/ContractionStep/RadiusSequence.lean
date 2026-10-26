import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Iteration.Radii
import Mathlib

/-! A decreasing, geometrically padded enumeration of a selected finite set of bands. -/

set_option autoImplicit false

namespace SupercriticalLFPPAS.ContractionStep

open SupercriticalLFPPAS.Core

/-- The selected exponents in decreasing order. -/
def orderedExponents (Sε : Finset ℤ) : List ℤ := Sε.sort (· ≥ ·)

/-- After the finite list ends, continue by subtracting one exponent at each step. -/
def paddedExponent (Sε : Finset ℤ) (i : ℕ) : ℤ :=
  if i < Sε.card then
    (orderedExponents Sε).getD i 0
  else
    (orderedExponents Sε).getD (Sε.card - 1) 0 - ((i - Sε.card + 1 : ℕ) : ℤ)

theorem orderedExponents_length (Sε : Finset ℤ) :
    (orderedExponents Sε).length = Sε.card := by
  simp [orderedExponents]

theorem paddedExponent_eq_get {Sε : Finset ℤ} {i : ℕ} (hi : i < Sε.card) :
    paddedExponent Sε i =
      (orderedExponents Sε)[i]'(by rw [orderedExponents_length]; exact hi) := by
  unfold paddedExponent
  rw [if_pos hi]
  exact List.getD_eq_getElem _ _ (by rw [orderedExponents_length]; exact hi)

theorem paddedExponent_mem {Sε : Finset ℤ} {i : ℕ} (hi : i < Sε.card) :
    paddedExponent Sε i ∈ Sε := by
  rw [paddedExponent_eq_get hi]
  have hlen : i < (orderedExponents Sε).length := by rw [orderedExponents_length]; exact hi
  have hmem : (orderedExponents Sε)[i]'hlen ∈ orderedExponents Sε :=
    List.getElem_mem hlen
  simpa [orderedExponents] using
    (Finset.mem_sort (s := Sε) (· ≥ ·)).mp hmem

theorem paddedExponent_succ_lt {Sε : Finset ℤ} (i : ℕ) :
    paddedExponent Sε (i + 1) < paddedExponent Sε i := by
  let l := orderedExponents Sε
  have hlen : l.length = Sε.card := orderedExponents_length Sε
  have htail : ∀ j, Sε.card ≤ j →
      paddedExponent Sε j =
        (orderedExponents Sε).getD (Sε.card - 1) 0 - ((j - Sε.card + 1 : ℕ) : ℤ) := by
    intro j hj
    unfold paddedExponent
    rw [if_neg (not_lt.mpr hj)]
  by_cases hi : i + 1 < Sε.card
  · have hi' : i < Sε.card := by omega
    rw [paddedExponent_eq_get hi, paddedExponent_eq_get hi']
    have hsort : l.SortedGT := by
      simpa [l, orderedExponents] using Finset.sortedGT_sort Sε
    exact hsort.getElem_gt_getElem_of_lt (i := i + 1) (j := i) (by omega)
  · by_cases hi' : i < Sε.card
    · have hlast : i + 1 = Sε.card := by omega
      have hlast' : i = Sε.card - 1 := by omega
      have hcurr : paddedExponent Sε i =
          (orderedExponents Sε).getD (Sε.card - 1) 0 := by
        rw [paddedExponent_eq_get hi']
        have hiLen : i < (orderedExponents Sε).length := by rw [orderedExponents_length]; exact hi'
        rw [← List.getD_eq_getElem (orderedExponents Sε) 0 hiLen, hlast']
      have hnext : paddedExponent Sε (i + 1) =
          (orderedExponents Sε).getD (Sε.card - 1) 0 - 1 := by
        rw [hlast, htail _ (by omega)]
        simp
      rw [hcurr, hnext]
      omega
    · have hi1 : i + 1 ≥ Sε.card := by omega
      rw [htail i (by omega), htail (i + 1) hi1]
      have hnat : (i + 1) - Sε.card + 1 = (i - Sε.card + 1) + 1 := by omega
      rw [hnat]
      simp only [Nat.cast_add, Nat.cast_one]
      omega

/-- The positive radii corresponding to the selected exponents, padded geometrically below the
selected range. Index one is the largest selected radius. -/
noncomputable def paddedRadius (Sε : Finset ℤ) (k : ℕ) : ℝ :=
  (bandRad (paddedExponent Sε (k - 1)) : ℝ)

theorem paddedRadius_pos (Sε : Finset ℤ) (k : ℕ) (_hk : 1 ≤ k) :
    0 < paddedRadius Sε k := by
  simp only [paddedRadius]
  exact (bandRad (paddedExponent Sε (k - 1))).property

theorem paddedRadius_ratio_le (Sε : Finset ℤ) {k : ℕ} (hk : 1 ≤ k) :
    paddedRadius Sε (k + 1) / paddedRadius Sε k ≤ 1 / Iteration.annulusBase := by
  have hstep := paddedExponent_succ_lt (Sε := Sε) (k - 1)
  rw [Nat.sub_add_cancel hk] at hstep
  have hdiff : paddedExponent Sε k - paddedExponent Sε (k - 1) ≤ -1 := by omega
  have hbase : 1 < Iteration.annulusBase := by norm_num [Iteration.annulusBase]
  have hpower := (zpow_right_strictMono₀ hbase).monotone hdiff
  change Iteration.annulusBase ^ paddedExponent Sε k /
      Iteration.annulusBase ^ paddedExponent Sε (k - 1) ≤ _
  rw [← zpow_sub₀ (by norm_num [Iteration.annulusBase] : Iteration.annulusBase ≠ 0)]
  simpa [Iteration.annulusBase] using hpower

theorem paddedRadius_antitone (Sε : Finset ℤ) :
    Antitone (paddedRadius Sε) := by
  have hpad : Antitone (paddedExponent Sε) :=
    antitone_nat_of_succ_le (fun i => (paddedExponent_succ_lt (Sε := Sε) i).le)
  intro j k hjk
  change Iteration.annulusBase ^ paddedExponent Sε (k - 1) ≤
    Iteration.annulusBase ^ paddedExponent Sε (j - 1)
  apply (zpow_right_strictMono₀
    (show 1 < Iteration.annulusBase by norm_num [Iteration.annulusBase])).monotone
  exact hpad (Nat.sub_le_sub_right hjk 1)

end SupercriticalLFPPAS.ContractionStep
