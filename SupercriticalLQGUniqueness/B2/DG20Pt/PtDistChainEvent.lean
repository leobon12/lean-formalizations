import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainGeometry

 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_bad_subset_biUnion
    {Ω : Type*} (ξ : ℝ) (φ : Ω → ℂ → ℝ) (U : Set ℂ)
    (p : ℕ → ℂ) (N : ℕ) (A : ℝ≥0∞) :
    {ω | ¬ lfppDOn ξ (φ ω) U (p 0) (p (N + 1)) ≤
      (N + 1 : ℝ≥0∞) * A} ⊆
      ⋃ j ∈ Finset.range (N + 1),
        {ω | ¬ lfppDOn ξ (φ ω) U (p j) (p (j + 1)) ≤ A} := by
  intro ω hω
  by_contra hnone
  have hedge (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      lfppDOn ξ (φ ω) U (p j) (p (j + 1)) ≤ A := by
    by_contra hbad
    exact hnone (mem_biUnion hj hbad)
  have hsum := Finset.sum_le_sum (s := Finset.range (N + 1)) hedge
  have hchain := pt_dist_le_chain_sum ξ (φ ω) U p N
  apply hω
  calc
    lfppDOn ξ (φ ω) U (p 0) (p (N + 1))
        ≤ ∑ j ∈ Finset.range (N + 1), lfppDOn ξ (φ ω) U (p j) (p (j + 1)) := hchain
    _ ≤ ∑ _j ∈ Finset.range (N + 1), A := hsum
    _ = (N + 1 : ℝ≥0∞) * A := by simp

end SupercriticalLQGUniqueness.B2.DG20Pt
