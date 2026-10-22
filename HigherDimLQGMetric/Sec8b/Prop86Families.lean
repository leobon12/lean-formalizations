import HigherDimLQGMetric.Sec8b.Prop86ClassCM
import HigherDimLQGMetric.Sec8b.Lemma85Universe
import HigherDimLQGMetric.Sec8b.Lemma84Final

/-! Finite candidate families for the Proposition 8.6 union bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical
open HigherDimLFPP (Rd)

variable {d : ℕ}

def s7b_candidateFamily (d J : ℕ) (r R : ℝ)
    (x y : Rd d) (colour : Fin d → ℤ) (k : ℕ) :
    Finset (Finset (Rd d × ℕ)) :=
  (s7b_siteUniverse d J r R).powerset.filter fun Z =>
    IsSec8LabeledSet d J r R x y colour Z ∧
      1 ≤ Z.card ∧ Z.card ≤ k

theorem s7b_candidate_valid (d J : ℕ) (r R : ℝ)
    (x y : Rd d) (colour : Fin d → ℤ) (k : ℕ)
    {Z : Finset (Rd d × ℕ)}
    (hZ : Z ∈ s7b_candidateFamily d J r R x y colour k) :
    IsSec8LabeledSet d J r R x y colour Z ∧
      1 ≤ Z.card ∧ Z.card ≤ k :=
  (Finset.mem_filter.mp hZ).2

theorem s7b_candidate_mem (d J : ℕ)
    (hd : 1 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (x y : Rd d) (colour : Fin d → ℤ) (k : ℕ)
    {Z : Finset (Rd d × ℕ)}
    (hZ : IsSec8LabeledSet d J r R x y colour Z)
    (hpos : 1 ≤ Z.card) (hk : Z.card ≤ k) :
    Z ∈ s7b_candidateFamily d J r R x y colour k := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr
    (s7b_labeled_subset_universe hd hr hR hZ), ⟨hZ, hpos, hk⟩⟩

theorem s7b_candidate_card_le (d J : ℕ)
    (hd : 1 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (x y : Rd d) (colour : Fin d → ℤ) (k : ℕ) :
    (s7b_candidateFamily d J r R x y colour k).card ≤
      (k + 1) * ((s7b_siteUniverse d J r R).card + 1) ^ k := by
  exact s7b_labeled_family_card_le hd hr hR x y colour k _
    (fun Z hz => ⟨(s7b_candidate_valid d J r R x y colour k hz).1,
      (s7b_candidate_valid d J r R x y colour k hz).2.2⟩)

end HigherDimLQGMetric
