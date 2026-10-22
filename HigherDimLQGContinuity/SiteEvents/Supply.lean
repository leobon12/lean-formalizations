import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.SiteEvents.CoverFull

/-! Radial sampling of a stopped geodesic for supplied sites. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Every radial level used in the site count is attained by the source path. -/
theorem q10_radial_points {d : ℕ} (P : ℝ → Rd d)
    (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {x y : Rd d} (hP0 : P 0 = x) (hP1 : P 1 = y)
    {w Δ : ℝ} (hw : 0 < w) (hΔ : 0 < Δ) (hxy : w / 2 ≤ ‖x - y‖)
    {j : ℕ} (hj : j < Nat.floor (w / (80 * Δ))) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖P t - x‖ = w / 8 + 10 * Δ * j := by
  have hratio : 0 ≤ w / (80 * Δ) := by positivity
  have hjbound : (j : ℝ) ≤ w / (80 * Δ) :=
    (Nat.cast_le.mpr (Nat.le_of_lt hj)).trans (Nat.floor_le hratio)
  have hlevel : w / 8 + 10 * Δ * j ≤ w / 4 := by
    have h := mul_le_mul_of_nonneg_left hjbound (by positivity : 0 ≤ 10 * Δ)
    have heq : 10 * Δ * (w / (80 * Δ)) = w / 8 := by field_simp; ring
    rw [heq] at h
    nlinarith only [h]
  have hlevel0 : 0 ≤ w / 8 + 10 * Δ * j := by positivity
  have hcont : ContinuousOn (fun t => ‖P t - x‖) (Icc (0 : ℝ) 1) :=
    (hP.sub continuousOn_const).norm
  have hstart : ‖P 0 - x‖ ≤ w / 8 + 10 * Δ * j := by
    rw [hP0, sub_self, norm_zero]
    exact hlevel0
  have hend : w / 8 + 10 * Δ * j ≤ ‖P 1 - x‖ := by
    rw [hP1, norm_sub_rev]
    linarith
  exact intermediate_value_Icc zero_le_one hcont ⟨hstart, hend⟩

/-- The radial spacing makes the selected inspections disjoint and keeps them off both endpoints. -/
theorem q10_site_geometry {d m : ℕ} {x y : Rd d} {w Δ : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) (hΔ : 0 < Δ) (hΔw : Δ ≤ w / 1000)
    (hx : x ∈ closedBall (0 : Rd d) 2) (hy : y ∈ closedBall (0 : Rd d) 2)
    (hxy : w / 2 ≤ ‖x - y‖)
    (q c : Fin m → Rd d) (r : Fin m → ℝ)
    (hlevels : ∀ i, ‖q i - x‖ = w / 8 + 10 * Δ * (i : ℝ))
    (hlevelTop : ∀ i, ‖q i - x‖ ≤ w / 4)
    (hr : ∀ i, 0 < r i ∧ r i ≤ Δ)
    (hclose : ∀ i, ‖q i - c i‖ < r i / 10) :
    (∀ i, q i ∈ ball (c i) (r i / 10) ∧
      closedBall (c i) (4 * r i) ⊆ ball (0 : Rd d) 4 ∧
      x ∉ closedBall (c i) (4 * r i) ∧ y ∉ closedBall (c i) (4 * r i)) ∧
    (∀ i j, i ≠ j → Disjoint (closedBall (c i) (4 * r i))
      (closedBall (c j) (4 * r j))) := by
  have hΔsmall : Δ ≤ 1 / 1000 := by nlinarith only [hΔw, hw1]
  have hxnorm : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hynorm : ‖y‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hone (i : Fin m) : ‖q i - c i‖ < Δ / 10 :=
    (hclose i).trans_le (div_le_div_of_nonneg_right (hr i).2 (by norm_num))
  have hqnorm (i : Fin m) : ‖q i‖ ≤ ‖q i - x‖ + ‖x‖ := by
    have he : q i = (q i - x) + x := by abel
    conv_lhs => rw [he]
    exact norm_add_le _ _
  constructor
  · intro i
    have hci : ‖c i - q i‖ < Δ / 10 := by simpa only [norm_sub_rev] using hone i
    have hcinorm : ‖c i‖ ≤ ‖c i - q i‖ + ‖q i‖ := by
      have he : c i = (c i - q i) + q i := by abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    have hcx : ‖c i - x‖ + ‖q i - c i‖ ≥ ‖q i - x‖ := by
      have he : q i - x = (q i - c i) + (c i - x) := by abel
      rw [he]
      exact (norm_add_le _ _).trans_eq (add_comm _ _)
    have hcy : ‖c i - y‖ + ‖q i - c i‖ + ‖q i - x‖ ≥ ‖x - y‖ := by
      have h₁ : ‖x - y‖ ≤ ‖x - q i‖ + ‖q i - y‖ := by
        have he : x - y = (x - q i) + (q i - y) := by abel
        rw [he]
        exact norm_add_le _ _
      have h₂ : ‖q i - y‖ ≤ ‖q i - c i‖ + ‖c i - y‖ := by
        have he : q i - y = (q i - c i) + (c i - y) := by abel
        rw [he]
        exact norm_add_le _ _
      rw [norm_sub_rev x (q i)] at h₁
      linarith
    have hcx4 : 4 * r i < ‖c i - x‖ := by
      have hlevelLow : w / 8 ≤ ‖q i - x‖ := by
        rw [hlevels]
        have hi0 : 0 ≤ (i : ℝ) := by positivity
        nlinarith only [mul_nonneg hΔ.le hi0]
      nlinarith only [hcx, hlevelLow, hone i, (hr i).2, hΔw, hw]
    have hcy4 : 4 * r i < ‖c i - y‖ := by
      nlinarith only [hcy, hxy, hlevelTop i, hone i, (hr i).2, hΔw, hw]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      simpa only [norm_sub_rev] using hclose i
    · intro v hv
      rw [mem_ball, dist_zero_right]
      have hvci : ‖v - c i‖ ≤ 4 * r i := by simpa only [mem_closedBall, dist_eq_norm] using hv
      have htri : ‖v‖ ≤ ‖v - c i‖ + ‖c i‖ := by
        have he : v = (v - c i) + c i := by abel
        conv_lhs => rw [he]
        exact norm_add_le _ _
      nlinarith only [htri, hvci, hcinorm, hci, hqnorm i, hlevelTop i,
        hxnorm, (hr i).2, hΔsmall, hw1]
    · rw [mem_closedBall, dist_eq_norm]
      simpa only [norm_sub_rev] using not_le.mpr hcx4
    · rw [mem_closedBall, dist_eq_norm]
      simpa only [norm_sub_rev] using not_le.mpr hcy4
  · intro i j hij
    have hsepq : 10 * Δ ≤ ‖q i - q j‖ := by
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij'
        have hnorm := norm_sub_norm_le (q j - x) (q i - x)
        have he : (q j - x) - (q i - x) = q j - q i := by abel
        rw [he, norm_sub_rev (q j) (q i), hlevels j, hlevels i] at hnorm
        nlinarith only [hnorm, hcast, hΔ]
      · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji'
        have hnorm := norm_sub_norm_le (q i - x) (q j - x)
        have he : (q i - x) - (q j - x) = q i - q j := by abel
        rw [he, hlevels i, hlevels j] at hnorm
        nlinarith only [hnorm, hcast, hΔ]
    have htri : ‖q i - q j‖ ≤ ‖q i - c i‖ + ‖c i - c j‖ + ‖c j - q j‖ := by
      have he : q i - q j = (q i - c i) + (c i - c j) + (c j - q j) := by abel
      rw [he]
      exact le_trans (norm_add_le _ _) (add_le_add_left (norm_add_le _ _) _)
    have hcsep : 4 * r i + 4 * r j < ‖c i - c j‖ := by
      have hjc : ‖c j - q j‖ < Δ / 10 := by simpa only [norm_sub_rev] using hone j
      nlinarith only [hsepq, htri, hone i, hjc, (hr i).2, (hr j).2, hΔ]
    apply closedBall_disjoint_closedBall
    simpa only [dist_eq_norm] using hcsep

/-- A path crossing a macroscopic distance supplies `⌊w/(80Δ)⌋` distinct good sites. -/
theorem supplied_sites {d : ℕ} (_hd : 2 ≤ d) (P : ℝ → Rd d)
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
        ‖q - HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
          p4_radius k / 10 ∧
        recentre 1 (p4_radius k)
          (HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∈ W) :
    ∃ (c : Fin (Nat.floor (w / (80 * Δ))) → Rd d)
      (r : Fin (Nat.floor (w / (80 * Δ))) → ℝ)
      (k : Fin (Nat.floor (w / (80 * Δ))) → ℕ)
      (j : Fin (Nat.floor (w / (80 * Δ))) → Fin d → ℤ)
      (t : Fin (Nat.floor (w / (80 * Δ))) → ℝ),
      Function.Injective (fun i => (c i, r i)) ∧
      (∀ i, t i ∈ Icc (0 : ℝ) 1 ∧ P (t i) ∈ ball (c i) (r i / 10) ∧
        r i = p4_radius (k i) ∧ k i ∈ T ∧
        c i = HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * r i) (j i) ∧
        recentre 1 (r i) (c i) g ∈ W ∧
        closedBall (c i) (4 * r i) ⊆ ball (0 : Rd d) 4 ∧
        x ∉ closedBall (c i) (4 * r i) ∧ y ∉ closedBall (c i) (4 * r i)) ∧
      (∀ i l, i ≠ l → Disjoint (closedBall (c i) (4 * r i))
        (closedBall (c l) (4 * r l))) := by
  classical
  let m : ℕ := Nat.floor (w / (80 * Δ))
  have hradial (i : Fin m) :
      ∃ t ∈ Icc (0 : ℝ) 1, ‖P t - x‖ = w / 8 + 10 * Δ * (i : ℝ) :=
    q10_radial_points P hP hP0 hP1 hw hΔ hxy i.isLt
  let t : Fin m → ℝ := fun i => Classical.choose (hradial i)
  have ht (i : Fin m) : t i ∈ Icc (0 : ℝ) 1 ∧
      ‖P (t i) - x‖ = w / 8 + 10 * Δ * (i : ℝ) :=
    Classical.choose_spec (hradial i)
  let q : Fin m → Rd d := fun i => P (t i)
  have hlevels (i : Fin m) : ‖q i - x‖ = w / 8 + 10 * Δ * (i : ℝ) := (ht i).2
  have hlevelTop (i : Fin m) : ‖q i - x‖ ≤ w / 4 := by
    have hratio : 0 ≤ w / (80 * Δ) := by positivity
    have hi : (i : ℝ) ≤ w / (80 * Δ) :=
      (Nat.cast_le.mpr (Nat.le_of_lt i.isLt)).trans (Nat.floor_le hratio)
    have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 10 * Δ)
    have heq : 10 * Δ * (w / (80 * Δ)) = w / 8 := by field_simp; ring
    rw [heq] at h
    rw [hlevels]
    nlinarith only [h]
  have hq3 (i : Fin m) : q i ∈ closedBall (0 : Rd d) 3 := by
    rw [mem_closedBall, dist_zero_right]
    have hxn : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hqn : ‖q i‖ ≤ ‖q i - x‖ + ‖x‖ := by
      have he : q i = (q i - x) + x := by abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    nlinarith only [hqn, hxn, hlevelTop i, hw1]
  have hgrid (i : Fin m) :
      ∃ k ∈ T, ∃ j : Fin d → ℤ,
        ‖q i - HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ <
          p4_radius k / 10 ∧
        recentre 1 (p4_radius k)
          (HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∈ W :=
    hcover (q i) (hq3 i)
  choose k hk j hclose hgood using hgrid
  let r : Fin m → ℝ := fun i => p4_radius (k i)
  let c : Fin m → Rd d := fun i =>
    HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * r i) (j i)
  have hr (i : Fin m) : 0 < r i ∧ r i ≤ Δ := by
    have hbound := hT (k i) (hk i)
    exact ⟨lt_of_lt_of_le (pow_pos hΔ _) hbound.1, hbound.2⟩
  have hclose' (i : Fin m) : ‖q i - c i‖ < r i / 10 := hclose i
  have hgeom := q10_site_geometry hw hw1 hΔ hΔw hx hy hxy q c r hlevels hlevelTop hr hclose'
  refine ⟨c, r, k, j, t, ?_, ?_, hgeom.2⟩
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
      (hgeom.1 i).2.1, (hgeom.1 i).2.2.1, (hgeom.1 i).2.2.2⟩

end HigherDimLQGContinuity
