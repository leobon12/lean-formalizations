import HigherDimLQGContinuity.Improve.PairCatalogueUnion
import HigherDimLQGContinuity.Improve.NetPower
import HigherDimLQGContinuity.Improve.ProbCount

/-!
# The complete net-pair and catalogue union probability
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- With `μ=Dnet+3`, summing the forcing estimate over every net pair and
catalogue leaves the probability `Δ^μ`. -/
theorem q11_catalogue_union_prob {d : ℕ} (hd : 1 ≤ d)
    (N : Finset (Rd d)) {Z : Type*} (C : Finset Z)
    (μlaw : Measure (DistRd d))
    {t Δ T γ Dnet : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hT : 0 < T) (htlower : T * Δ ^ γ ≤ t)
    (hconstant : (9 * Real.sqrt d / T) ^ (2 * d) ≤ Δ⁻¹)
    (hDnet : Dnet = 2 * (d : ℝ) * γ + 1)
    (hN : (N.card : ℝ) ≤ (8 * Real.sqrt d / t + 1) ^ d)
    (hC : (C.card : ℝ) ≤ Δ ^ (-(1 : ℝ)))
    (B : Rd d → Rd d → Z → Set (DistRd d))
    (hB : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ∀ z ∈ C,
      μlaw (B x y z) ≤ ENNReal.ofReal (Δ ^ (2 * (Dnet + 3) + 2))) :
    μlaw (⋃ x ∈ N, ⋃ y ∈ N, ⋃ z ∈ C,
      {H | x ≠ y ∧ H ∈ B x y z}) ≤
      ENNReal.ofReal (Δ ^ (Dnet + 3)) := by
  have hpair : ((N.card * N.card : ℕ) : ℝ) ≤ Δ ^ (-Dnet) := by
    simpa only [hDnet] using
      q11_net_pair_power hd ht ht1 hΔ hT htlower hconstant N hN
  have hnum : ((N.card * N.card * C.card : ℕ) : ℝ) *
      Δ ^ (2 * (Dnet + 3) + 2) ≤ Δ ^ (Dnet + 3) := by
    have hcast : ((N.card * N.card * C.card : ℕ) : ℝ) =
        ((N.card * N.card : ℕ) : ℝ) * C.card := by push_cast; ring
    rw [hcast]
    exact q11_probability_count hΔ hΔ1 (Nat.cast_nonneg _) hpair hC
  exact q11_pair_catalogue_probability μlaw N C
    (fun x y => x ≠ y) (fun x => by simp)
    B hB hnum

end HigherDimLQGContinuity
