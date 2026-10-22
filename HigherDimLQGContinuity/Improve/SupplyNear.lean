import HigherDimLQGContinuity.SiteEvents.Supply

/-!
# Supplied sites remain in the radius-three source ball

The radial level is retained from the supply construction because the
site-unit window needs each centre inside this ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

theorem q11_supplied_sites_near {d : ℕ} (_hd : 2 ≤ d) (P : ℝ → Rd d)
    (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {x y : Rd d} (hP0 : P 0 = x) (hP1 : P 1 = y)
    {w Δ : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hΔ : 0 < Δ)
    (hΔw : Δ ≤ w / 1000)
    (hx : x ∈ closedBall (0 : Rd d) 2) (hy : y ∈ closedBall (0 : Rd d) 2)
    (hxy : w / 2 ≤ ‖x - y‖)
    (T : Finset ℕ) (hT : ∀ k ∈ T, Δ ^ (2 : ℕ) ≤ p4_radius k ∧ p4_radius k ≤ Δ)
    (g : DistRd d) (W : Set (DistRd d))
    (hcover : ∀ q ∈ closedBall (0 : Rd d) 3,
      ∃ k ∈ T, ∃ j : Fin d → ℤ,
        ‖q - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
          p4_radius k / 10 ∧
        recentre 1 (p4_radius k)
          (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∈ W) :
    ∃ (c : Fin (Nat.floor (w / (80 * Δ))) → Rd d)
      (r : Fin (Nat.floor (w / (80 * Δ))) → ℝ)
      (k : Fin (Nat.floor (w / (80 * Δ))) → ℕ)
      (j : Fin (Nat.floor (w / (80 * Δ))) → Fin d → ℤ)
      (t : Fin (Nat.floor (w / (80 * Δ))) → ℝ),
      Function.Injective (fun i => (c i, r i)) ∧
      (∀ i, t i ∈ Icc (0 : ℝ) 1 ∧ P (t i) ∈ ball (c i) (r i / 10) ∧
        r i = p4_radius (k i) ∧ k i ∈ T ∧
        c i = latPt ((1 / (20 * Real.sqrt d)) * r i) (j i) ∧
        recentre 1 (r i) (c i) g ∈ W ∧
        c i ∈ ball (0 : Rd d) 3 ∧
        closedBall (c i) (4 * r i) ⊆ ball (0 : Rd d) 4 ∧
        x ∉ closedBall (c i) (4 * r i) ∧ y ∉ closedBall (c i) (4 * r i)) := by
  classical
  let M : ℕ := Nat.floor (w / (80 * Δ))
  have hradial (i : Fin M) :
      ∃ t ∈ Icc (0 : ℝ) 1, ‖P t - x‖ = w / 8 + 10 * Δ * (i : ℝ) :=
    q10_radial_points P hP hP0 hP1 hw hΔ hxy i.isLt
  let t : Fin M → ℝ := fun i => Classical.choose (hradial i)
  have ht (i : Fin M) : t i ∈ Icc (0 : ℝ) 1 ∧
      ‖P (t i) - x‖ = w / 8 + 10 * Δ * (i : ℝ) :=
    Classical.choose_spec (hradial i)
  let q : Fin M → Rd d := fun i => P (t i)
  have hlevels (i : Fin M) : ‖q i - x‖ = w / 8 + 10 * Δ * (i : ℝ) := (ht i).2
  have hlevelTop (i : Fin M) : ‖q i - x‖ ≤ w / 4 := by
    have hratio : 0 ≤ w / (80 * Δ) := by positivity
    have hi : (i : ℝ) ≤ w / (80 * Δ) :=
      (Nat.cast_le.mpr (Nat.le_of_lt i.isLt)).trans (Nat.floor_le hratio)
    have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 10 * Δ)
    have heq : 10 * Δ * (w / (80 * Δ)) = w / 8 := by field_simp; ring
    rw [heq] at h
    rw [hlevels]
    nlinarith only [h]
  have hq3 (i : Fin M) : q i ∈ closedBall (0 : Rd d) 3 := by
    rw [mem_closedBall, dist_zero_right]
    have hxn : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hqn : ‖q i‖ ≤ ‖q i - x‖ + ‖x‖ := by
      have he : q i = (q i - x) + x := by abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    nlinarith only [hqn, hxn, hlevelTop i, hw1]
  have hgrid (i : Fin M) :
      ∃ k ∈ T, ∃ j : Fin d → ℤ,
        ‖q i - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
          p4_radius k / 10 ∧
        recentre 1 (p4_radius k)
          (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∈ W :=
    hcover (q i) (hq3 i)
  choose k hk j hclose hgood using hgrid
  let r : Fin M → ℝ := fun i => p4_radius (k i)
  let c : Fin M → Rd d := fun i => latPt ((1 / (20 * Real.sqrt d)) * r i) (j i)
  have hr (i : Fin M) : 0 < r i ∧ r i ≤ Δ := by
    have hb := hT (k i) (hk i)
    exact ⟨lt_of_lt_of_le (pow_pos hΔ _) hb.1, hb.2⟩
  have hclose' (i : Fin M) : ‖q i - c i‖ < r i / 10 := hclose i
  have hgeom := q10_site_geometry hw hw1 hΔ hΔw hx hy hxy q c r
    hlevels hlevelTop hr hclose'
  have hc3 (i : Fin M) : c i ∈ ball (0 : Rd d) 3 := by
    rw [mem_ball, dist_zero_right]
    have hxn : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hqn : ‖q i‖ ≤ ‖q i - x‖ + ‖x‖ := by
      have he : q i = (q i - x) + x := by abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    have hcn : ‖c i‖ ≤ ‖c i - q i‖ + ‖q i‖ := by
      have he : c i = (c i - q i) + q i := by abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    have hcloseNorm : ‖c i - q i‖ < r i / 10 := by
      simpa only [norm_sub_rev] using hclose' i
    nlinarith only [hcn, hcloseNorm, hqn, hlevelTop i,
      hxn, hw1, (hr i).2, hΔw]
  refine ⟨c, r, k, j, t, ?_, ?_⟩
  · intro i l heq
    by_contra hil
    have hdisj := hgeom.2 i l hil
    have hri : 0 ≤ 4 * r i := by have := (hr i).1; positivity
    have hrl : 0 ≤ 4 * r l := by have := (hr l).1; positivity
    have hmemi : c i ∈ closedBall (c i) (4 * r i) := mem_closedBall_self hri
    have hmeml : c i ∈ closedBall (c l) (4 * r l) := by
      have hc : c i = c l := congrArg Prod.fst heq
      rw [hc]
      exact mem_closedBall_self hrl
    exact Set.disjoint_left.mp hdisj hmemi hmeml
  · intro i
    exact ⟨(ht i).1, (hgeom.1 i).1, rfl, hk i, rfl, hgood i,
      hc3 i, (hgeom.1 i).2.1, (hgeom.1 i).2.2.1, (hgeom.1 i).2.2.2⟩

end HigherDimLQGContinuity
