import HigherDimLQGContinuity.Network.Samples

/-! # Connectivity of chamber and gate balls around a covered arc -/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem coveredHit_image_mem_open {d : ℕ} {μ g a b : ℝ}
    (hμ : 0 ≤ μ) (ho : Real.sqrt d / 2 * μ < g)
    (o : Rd d) (Q : Finset (Fin d → ℤ)) (γ : ℝ → Rd d)
    (hQ : CoveredHit μ o Q (γ '' Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    γ t ∈ ballUnionOpen μ o Q g := by
  obtain ⟨k, hk, hcell⟩ := mem_iUnion₂.mp (hQ.1 ⟨t, ht, rfl⟩)
  have hd : dist (γ t) (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ := by
    simpa only [mem_closedBall] using cell_subset_closedBall hμ o k hcell
  exact mem_iUnion₂.mpr ⟨k, hk, mem_ball.mpr (lt_of_le_of_lt hd ho)⟩

/-- A lead tip within the prescribed endpoint tolerance lies in its open
gate. -/
theorem coveredHit_tip_mem_open {d : ℕ} {μ g a b η : ℝ}
    (hμ : 0 ≤ μ) (hwidth : η + Real.sqrt d / 2 * μ < g)
    (o tip : Rd d) (Q : Finset (Fin d → ℤ)) (γ : ℝ → Rd d)
    (hQ : CoveredHit μ o Q (γ '' Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (htip : dist tip (γ t) ≤ η) :
    tip ∈ ballUnionOpen μ o Q g := by
  obtain ⟨k, hk, hcell⟩ := mem_iUnion₂.mp (hQ.1 ⟨t, ht, rfl⟩)
  have hd : dist (γ t) (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ := by
    simpa only [mem_closedBall] using cell_subset_closedBall hμ o k hcell
  have htipc : dist tip (cellCenter μ o k) < g := by
    calc
      dist tip (cellCenter μ o k) ≤ dist tip (γ t) +
          dist (γ t) (cellCenter μ o k) := dist_triangle _ _ _
      _ ≤ η + Real.sqrt d / 2 * μ := add_le_add htip hd
      _ < g := hwidth
  exact mem_iUnion₂.mpr ⟨k, hk, mem_ball.mpr htipc⟩

/-- A finite covered-and-hit cell family gives a connected open-ball union
whenever its target is the image of a continuous interval. -/
theorem connected_ballUnionOpen_of_coveredHit {d : ℕ}
    {μ g a b : ℝ} (hμ : 0 ≤ μ) (ho : Real.sqrt d / 2 * μ < g)
    (o : Rd d) (Q : Finset (Fin d → ℤ)) (γ : ℝ → Rd d)
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hQ : CoveredHit μ o Q (γ '' Icc a b)) :
    IsConnected (ballUnionOpen μ o Q g) := by
  let S : Set (Rd d) := γ '' Icc a b
  have hS : IsConnected S := (isConnected_Icc hab).image γ hγ
  have hcell : ∀ k : Fin d → ℤ, ∀ x ∈ cell μ o k,
      x ∈ ball (cellCenter μ o k) g := by
    intro k x hx
    have hd : dist x (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ := by
      simpa only [mem_closedBall] using cell_subset_closedBall hμ o k hx
    exact mem_ball.mpr (lt_of_le_of_lt hd ho)
  have hcover : S ⊆ ⋃ k ∈ Q, ball (cellCenter μ o k) g := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (hQ.1 hx)
    exact mem_iUnion₂.mpr ⟨k, hk, hcell k x hxk⟩
  have hmeet : ∀ k ∈ Q, (S ∩ ball (cellCenter μ o k) g).Nonempty := by
    intro k hk
    obtain ⟨x, hxS, hxcell⟩ := hQ.2 k hk
    exact ⟨x, hxS, hcell k x hxcell⟩
  exact connected_indexed_ballUnion_of_skeleton Q (cellCenter μ o) g S
    hS hcover (lt_of_le_of_lt (by positivity) ho) hmeet

end HigherDimLQGContinuity
