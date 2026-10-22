import HigherDimLQGMetric.Sec8b.FiniteSets

/-! Count labels after the number of very-good centres is bounded. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical

/-- At most `J` labels can be attached to each centre. -/
theorem s7b_good_labels_card_le {α : Type*} [DecidableEq α]
    (J : ℕ) (good : Finset (α × ℕ))
    (hJ : ∀ site ∈ good, site.2 < J) :
    good.card ≤ (good.image Prod.fst).card * J := by
  have hsub : good ⊆ (good.image Prod.fst).product (Finset.range J) := by
    intro site hsite
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨site, hsite, rfl⟩,
        Finset.mem_range.mpr (hJ site hsite)⟩
  have hcard := Finset.card_le_card hsub
  change good.card ≤ ((good.image Prod.fst) ×ˢ Finset.range J).card at hcard
  simpa only [Finset.card_product, Finset.card_range] using hcard

/-- The corrected `K₀ = 2^(J K)` count, once the geometric argument has
bounded the number of very-good centres by `Kk`. -/
theorem s7b_few_shifted_sets_of_centers {α : Type*} [DecidableEq α]
    (J K k : ℕ) (good : Finset (α × ℕ))
    (family : Finset (Finset (α × ℕ)))
    (hJ : ∀ site ∈ good, site.2 < J)
    (hcenters : (good.image Prod.fst).card ≤ K * k)
    (hgood : ∀ Z ∈ family, Z ⊆ good) :
    family.card ≤ (2 ^ (J * K)) ^ k := by
  have hcard : good.card ≤ J * K * k := by
    calc
      good.card ≤ (good.image Prod.fst).card * J :=
        s7b_good_labels_card_le J good hJ
      _ ≤ (K * k) * J := Nat.mul_le_mul_right J hcenters
      _ = J * K * k := by ac_rfl
  exact s7b_few_sets_pow good family hgood hcard

end HigherDimLQGMetric
