import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Growth.DyadicCells

/-!
# A finite net inside the source ball

For (4.26), one point is selected from each grid cell meeting the closed ball.
This avoids projecting grid points outside the ball and keeps the grid's
cardinality bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

/-- A net of the closed radius-two ball with no more points than the ambient
box grid. The approximation radius is twice the grid-cell radius. -/
theorem q11_ball_net {d : ℕ} {a : ℝ} (ha : 0 < a) :
    ∃ N : Finset (Rd d),
      (∀ p ∈ N, p ∈ closedBall (0 : Rd d) 2) ∧
      ((N.card : ℝ) ≤ (4 / a + 1) ^ d) ∧
      (∀ x ∈ closedBall (0 : Rd d) 2,
        ∃ p ∈ N, ‖x - p‖ ≤ 2 * Real.sqrt d * a) := by
  classical
  let G : Finset (Rd d) := HigherDimLFPP.Osc.grid 0 2 a
  let cell : Rd d → Rd d := HigherDimLFPP.Osc.gridOf 0 2 a
  let rep : Rd d → Rd d := fun g =>
    if h : ∃ x ∈ closedBall (0 : Rd d) 2, cell x = g then Classical.choose h else 0
  let N : Finset (Rd d) := G.image rep
  have hrep (g : Rd d) (h : ∃ x ∈ closedBall (0 : Rd d) 2, cell x = g) :
      rep g ∈ closedBall (0 : Rd d) 2 ∧ cell (rep g) = g := by
    dsimp [rep]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  have hmem (g : Rd d) (hg : g ∈ G) : rep g ∈ N :=
    Finset.mem_image.mpr ⟨g, hg, rfl⟩
  refine ⟨N, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
    by_cases h : ∃ x ∈ closedBall (0 : Rd d) 2, cell x = g
    · exact (hrep g h).1
    · dsimp [rep]
      rw [dite_eq_right h]
      simp only [mem_closedBall, dist_self]
      norm_num
  · calc
      (N.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ (4 / a + 1) ^ d := by
        simpa only [G, show (2 : ℝ) * 2 = 4 by norm_num] using
          HigherDimLFPP.Osc.card_grid_le (0 : Rd d) (R := 2) (a := a)
            (by norm_num) ha
  · intro x hx
    have hcell : cell x ∈ G :=
      l2a_gridOf_mem (d := d) ha hx
    have hex : ∃ y ∈ closedBall (0 : Rd d) 2, cell y = cell x :=
      ⟨x, hx, rfl⟩
    refine ⟨rep (cell x), hmem (cell x) hcell, ?_⟩
    have hp := hrep (cell x) hex
    have hxg : ‖x - cell x‖ ≤ Real.sqrt d * a :=
      l2a_gridOf_dist_le (d := d) ha hx
    have hpg : ‖rep (cell x) - cell x‖ ≤ Real.sqrt d * a := by
      simpa only [cell, hp.2] using l2a_gridOf_dist_le (d := d) ha hp.1
    have htri : ‖x - rep (cell x)‖ ≤ ‖x - cell x‖ + ‖cell x - rep (cell x)‖ := by
      have he : (x - cell x) + (cell x - rep (cell x)) = x - rep (cell x) := by
        abel
      rw [← he]
      exact norm_add_le _ _
    have htri' : ‖x - rep (cell x)‖ ≤
        ‖x - cell x‖ + ‖rep (cell x) - cell x‖ := by
      simpa only [norm_sub_rev (cell x) (rep (cell x))] using htri
    linarith only [htri', hxg, hpg]

/-- The radius-two net parametrized by its approximation radius. -/
theorem q11_ball_net_of_radius {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    ∃ N : Finset (Rd d),
      (∀ p ∈ N, p ∈ closedBall (0 : Rd d) 2) ∧
      ((N.card : ℝ) ≤ (8 * Real.sqrt d / t + 1) ^ d) ∧
      (∀ x ∈ closedBall (0 : Rd d) 2, ∃ p ∈ N, ‖x - p‖ ≤ t) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  let a : ℝ := t / (2 * Real.sqrt d)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN, hcard, hcover⟩ := q11_ball_net (d := d) ha
  have hmesh : 2 * Real.sqrt d * a = t := by
    dsimp [a]
    field_simp
  have hcardEq : 4 / a + 1 = 8 * Real.sqrt d / t + 1 := by
    dsimp [a]
    field_simp
    ring
  refine ⟨N, hN, ?_, ?_⟩
  · simpa only [hcardEq] using hcard
  · intro x hx
    obtain ⟨p, hp, hdist⟩ := hcover x hx
    exact ⟨p, hp, by simpa only [hmesh] using hdist⟩

end HigherDimLQGContinuity
