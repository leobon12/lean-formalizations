import HigherDimLQGContinuity.Labels.Cells

/-!
# Separation of lead tubes from the chamber outside their gate

This is the metric part of Part B's `b:lem-leadchamber`. The lead set need not be
closed: the passage from its closed thickening uses an arbitrarily small radius
enlargement.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

private theorem dist_ge_of_cthickening {d : ℕ} {ω r : ℝ} (hω : 0 < ω)
    (L : Set (Rd d)) {x z : Rd d}
    (hx : x ∈ Metric.cthickening ω L)
    (hsep : ∀ l ∈ L, r ≤ dist l z) : r - ω ≤ dist x z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hnear : x ∈ ⋃ l ∈ L, closedBall l (ω + ε) :=
    (Metric.cthickening_subset_iUnion_closedBall_of_lt L (by linarith) (by linarith)) hx
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.mp hnear
  have hxl' : dist x l ≤ ω + ε := mem_closedBall.mp hxl
  have hlx : dist l x ≤ ω + ε := by
    rw [dist_comm l x]
    exact hxl'
  have htri := dist_triangle l x z
  have hlz := hsep l hl
  linarith

private theorem dist_ge_of_outside_gate {d : ℕ} {μ g : ℝ} (hμ : 0 ≤ μ)
    (o : Rd d) (Q : Finset (Fin d → ℤ)) (S : Set (Rd d))
    (hQ : CoveredHit μ o Q S) {x z : Rd d}
    (hx : x ∉ interior (ballUnion μ o Q g)) (hz : z ∈ S) :
    g - Real.sqrt d / 2 * μ ≤ dist x z := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨k, hkQ, hzcell⟩ := mem_iUnion₂.mp (hQ.1 hz)
  have hzc : dist z (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ :=
    mem_closedBall.mp (cell_subset_closedBall hμ o k hzcell)
  have hxc : dist x (cellCenter μ o k) < g := by
    calc
      dist x (cellCenter μ o k) ≤ dist x z + dist z (cellCenter μ o k) :=
        dist_triangle _ _ _
      _ < g := by linarith
  apply hx
  apply ballUnionOpen_subset_interior μ o Q g
  exact mem_iUnion₂.mpr ⟨k, hkQ, mem_ball.mpr hxc⟩

/-- Part B's lead-versus-chamber separation, outside the initial gate. -/
theorem lead_chamber_sep {d : ℕ} {μ ω g r t₀ : ℝ}
    (hμ : 0 ≤ μ) (hω : 0 < ω) (ht₀ : 0 ≤ t₀)
    (o : Rd d) (γ : ℝ → Rd d) (Qstar Qzero : Finset (Fin d → ℤ))
    (L : Set (Rd d))
    (hstar : CoveredHit μ o Qstar (γ '' Icc 0 1))
    (hzero : CoveredHit μ o Qzero (γ '' Icc 0 (2 * t₀)))
    (hc : Real.sqrt d / 2 * μ ≤ ω)
    (hclear : ∀ l ∈ L, ∀ t ∈ Icc t₀ 1, r ≤ dist l (γ t))
    {x y : Rd d}
    (hx : x ∈ Metric.cthickening ω L \ interior (ballUnion μ o Qzero g))
    (hy : y ∈ ballUnion μ o Qstar ω \ interior (ballUnion μ o Qzero g)) :
    min (r - 3 * ω) (g - Real.sqrt d / 2 * μ - 2 * ω) ≤ dist x y := by
  obtain ⟨k, hkQ, hyball⟩ := mem_iUnion₂.mp hy.1
  obtain ⟨z, hzS, hzcell⟩ := hstar.2 k hkQ
  obtain ⟨t, ht, rfl⟩ := hzS
  have hyc : dist y (cellCenter μ o k) ≤ ω := mem_closedBall.mp hyball
  have hzc : dist (γ t) (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ :=
    mem_closedBall.mp (cell_subset_closedBall hμ o k hzcell)
  have hyz : dist y (γ t) ≤ 2 * ω := by
    calc
      dist y (γ t) ≤ dist y (cellCenter μ o k) +
          dist (cellCenter μ o k) (γ t) := dist_triangle _ _ _
      _ ≤ ω + Real.sqrt d / 2 * μ :=
        add_le_add hyc (by simpa only [dist_comm (cellCenter μ o k) (γ t)] using hzc)
      _ ≤ 2 * ω := by linarith
  by_cases hlate : t₀ ≤ t
  · have hxt : r - ω ≤ dist x (γ t) :=
      dist_ge_of_cthickening hω L hx.1 (fun l hl => hclear l hl t ⟨hlate, ht.2⟩)
    have htri := dist_triangle x y (γ t)
    calc
      min (r - 3 * ω) (g - Real.sqrt d / 2 * μ - 2 * ω) ≤ r - 3 * ω :=
        min_le_left _ _
      _ ≤ dist x y := by linarith
  · have htearly : t ∈ Icc (0 : ℝ) (2 * t₀) := by
      constructor
      · exact ht.1
      · have : t < t₀ := lt_of_not_ge hlate
        linarith
    have hxt : g - Real.sqrt d / 2 * μ ≤ dist x (γ t) :=
      dist_ge_of_outside_gate hμ o Qzero (γ '' Icc 0 (2 * t₀)) hzero hx.2
        ⟨t, htearly, rfl⟩
    have htri := dist_triangle x y (γ t)
    calc
      min (r - 3 * ω) (g - Real.sqrt d / 2 * μ - 2 * ω) ≤
          g - Real.sqrt d / 2 * μ - 2 * ω := min_le_right _ _
      _ ≤ dist x y := by linarith

end HigherDimLQGContinuity
