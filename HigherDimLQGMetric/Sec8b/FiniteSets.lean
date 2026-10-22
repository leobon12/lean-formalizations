import HigherDimLQGMetric.Count.ImageOut

/-!
# Section 8: finite families of labeled sets

The last step of Lemma 8.5 counts favorable sets by embedding them in the
powerset of the labels at very good centres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical

/-- A family whose members are all subsets of one finite set has at most
`2^m` members, where `m` is that set's cardinality. -/
theorem s7b_few_sets_of_good_labels {α : Type*} [DecidableEq α]
    (good : Finset α) (family : Finset (Finset α))
    (hgood : ∀ Z ∈ family, Z ⊆ good) :
    family.card ≤ 2 ^ good.card := by
  have hsubset : family ⊆ good.powerset := by
    intro Z hZ
    exact Finset.mem_powerset.mpr (hgood Z hZ)
  calc
    family.card ≤ good.powerset.card := Finset.card_le_card hsubset
    _ = 2 ^ good.card := Finset.card_powerset good

/-- If the very good centres carry at most `J` labels each, `K k` centres
give a bound `K₀^k` with `K₀ = 2^(J K)`. -/
theorem s7b_few_sets_pow {α : Type*} [DecidableEq α]
    (good : Finset α) (family : Finset (Finset α))
    (hgood : ∀ Z ∈ family, Z ⊆ good)
    {J K k : ℕ} (hcard : good.card ≤ J * K * k) :
    family.card ≤ (2 ^ (J * K)) ^ k := by
  calc
    family.card ≤ 2 ^ good.card := s7b_few_sets_of_good_labels good family hgood
    _ ≤ 2 ^ (J * K * k) := Nat.pow_le_pow_right (by omega) hcard
    _ = (2 ^ (J * K)) ^ k := by rw [pow_mul]

end HigherDimLQGMetric
