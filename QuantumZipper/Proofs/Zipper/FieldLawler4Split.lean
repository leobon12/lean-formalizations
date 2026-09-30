import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 4: splitting the crosscut sum by the sign of the feet

`fl4_split_sum`: the sum in `FLImageSumBoundStmt` over crosscuts with feet on one side of `0`
(flux into the opposite half-line `{x | x a ≤ 0}`) splits into the positive-feet part (flux into
`(−∞, 0]`) and the negative-feet part (flux into `[0, ∞)`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

theorem fl4_split_sum (S : Set ℕ) (a : ℕ → ℝ) (f : ℕ → Set ℝ → ℝ≥0∞)
    (ha : ∀ j ∈ S, a j ≠ 0) :
    ∑' j, S.indicator (fun j => f j {x : ℝ | x * a j ≤ 0}) j =
      ∑' j, {j | j ∈ S ∧ 0 < a j}.indicator (fun j => f j (Iic 0)) j +
      ∑' j, {j | j ∈ S ∧ a j < 0}.indicator (fun j => f j (Ici 0)) j := by
  rw [← ENNReal.tsum_add]
  congr 1
  funext j
  by_cases hj : j ∈ S
  · rw [indicator_of_mem hj]
    rcases lt_or_gt_of_ne (ha j hj) with h | h
    · rw [indicator_of_notMem (fun h' => absurd h'.2 (not_lt.2 h.le)),
        indicator_of_mem (show j ∈ {j | j ∈ S ∧ a j < 0} from ⟨hj, h⟩), zero_add]
      congr 1
      ext x; simp only [mem_setOf_eq, mem_Ici]
      constructor
      · intro hx; by_contra hc; push_neg at hc; nlinarith
      · intro hx; nlinarith
    · rw [indicator_of_mem (show j ∈ {j | j ∈ S ∧ 0 < a j} from ⟨hj, h⟩), indicator_of_notMem (fun h' => absurd h'.2 (not_lt.2 h.le)),
        add_zero]
      congr 1
      ext x; simp only [mem_setOf_eq, mem_Iic]
      constructor
      · intro hx; by_contra hc; push_neg at hc; nlinarith
      · intro hx; nlinarith
  · rw [indicator_of_notMem hj, indicator_of_notMem (fun h' => hj h'.1),
      indicator_of_notMem (fun h' => hj h'.1), add_zero]

end FieldLawler
end QuantumZipper
