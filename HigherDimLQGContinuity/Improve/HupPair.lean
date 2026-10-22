import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Witness.Subdiv

/-!
# Extracting the separated bad pair from the upper witness event
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A field in `Hup` with the pair references gives the separated pair that
the finite net rounds. The small gain `gΔ/16` leaves the `gΔ/8` margin. -/
theorem q11_hup_separated_pair {d : ℕ}
    {D E : DistRd d → ContMetric d} {g : DistRd d}
    {H0 σ0 β0 m M w c gΔ : ℝ}
    (hD : (rho D g).IsLength) (hE : (rho E g).IsLength)
    (hH0 : 0 < H0) (hσ0 : 0 < σ0) (hβ0 : 0 < β0) (hm : 0 < m)
    (hrefs : g ∈ PairRefs D E H0 σ0 β0 m M)
    (hw : 0 < w) (hwsub : w ≤ subdivW H0 σ0 β0 m M)
    (hgΔ : 0 < gΔ) (hc : 0 ≤ c - gΔ / 16)
    (hup : g ∈ Hup D E (c - gΔ / 16)) :
    ∃ x ∈ closedBall (0 : Rd d) 2, ∃ y ∈ closedBall (0 : Rd d) 2,
      3 / 4 * w ≤ ‖x - y‖ ∧
        (c - gΔ / 8) * (rho D g).1 (x, y) < (rho E g).1 (x, y) := by
  obtain ⟨x, hx, y, hy, hsep, -, -, hbad⟩ :=
    exists_pair_of_mem_hup hD hE hH0 hσ0 hβ0 hm hrefs hc hup
  have hball : annK d ⊆ closedBall (0 : Rd d) 2 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have hnorm := (mem_annK_iff.mp hz).2
    linarith
  refine ⟨x, hball hx, y, hball hy, ?_, ?_⟩
  · linarith only [hsep, hwsub, hw]
  · have hcoef : c - gΔ / 8 ≤ c - gΔ / 16 := by linarith only [hgΔ]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hcoef ((rho D g).nonneg x y)) hbad

/-- Set-level form of the `Hup` passage. It keeps the two length-metric null
sets explicit, so the subsequent probability bound uses no pointwise length
assumption. -/
theorem q11_hup_subset_separated_pairs {d : ℕ}
    {D E : DistRd d → ContMetric d}
    {H0 σ0 β0 m M w c gΔ : ℝ}
    (hH0 : 0 < H0) (hσ0 : 0 < σ0) (hβ0 : 0 < β0) (hm : 0 < m)
    (hw : 0 < w) (hwsub : w ≤ subdivW H0 σ0 β0 m M)
    (hgΔ : 0 < gΔ) (hc : 0 ≤ c - gΔ / 16) :
    Hup D E (c - gΔ / 16) ⊆
      (PairRefs D E H0 σ0 β0 m M)ᶜ ∪
      {g | ¬ (rho D g).IsLength} ∪
      {g | ¬ (rho E g).IsLength} ∪
      {g | ∃ x ∈ closedBall (0 : Rd d) 2, ∃ y ∈ closedBall (0 : Rd d) 2,
        3 / 4 * w ≤ ‖x - y‖ ∧
          (c - gΔ / 8) * (rho D g).1 (x, y) < (rho E g).1 (x, y)} := by
  intro g hg
  by_cases hr : g ∈ PairRefs D E H0 σ0 β0 m M
  · by_cases hD : (rho D g).IsLength
    · by_cases hE : (rho E g).IsLength
      · exact Or.inr (q11_hup_separated_pair hD hE hH0 hσ0 hβ0 hm
          hr hw hwsub hgΔ hc hg)
      · exact Or.inl (Or.inr hE)
    · exact Or.inl (Or.inl (Or.inr hD))
  · exact Or.inl (Or.inl (Or.inl hr))

end HigherDimLQGContinuity
