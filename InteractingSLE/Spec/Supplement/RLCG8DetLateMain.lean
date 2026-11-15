/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateTransport

/-!
# G8: late-cut geometry from closed restriction separation and boundary order

Packet PROVE-G8-DET. All fields of `LateCutGeometry` except closed-hull
separation and the strict initial order are constructed here. The exact
remaining planar assertion is `LateSeparationOrderNHStatement`; it is not
asserted unconditionally.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.RLC
namespace G8Det.Late

theorem one_notMem_closure_own_before {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hw : Continuous w) (hgen : IsGeneratingTrace w ⊤ α)
    {σ u : ℝ≥0} (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (huσ : u < σ) :
    (1 : ℂ) ∉ closure (ownHull α u) := by
  obtain ⟨v, hv⟩ := hsw.2.1 u ⟨u.coe_nonneg, by exact_mod_cast huσ⟩
  obtain ⟨δ, hδ, hnot⟩ := GB7a.exists_ball_notMem_fwdHull
    (U := fun s : ℝ => w s.toNNReal) (hw.comp continuous_real_toNNReal) u.coe_nonneg hv
  have hsub : ownHull α u ⊆ (ball (1 : ℂ) δ)ᶜ := by
    intro z hz hzb
    apply hnot z (by simpa only [mem_ball, dist_eq_norm, ofReal_one] using hzb)
    rwa [← ownHull_eq_fwdHull hcα hgen]
  exact fun hcl => closure_minimal hsub isOpen_ball.isClosed_compl hcl (mem_ball_self hδ)

theorem seed_limit_of_clearance {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) {a σ r : ℝ≥0} (haσ : a < σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) :
    Tendsto (obstacleMap α β a r) (𝓝[H] (cutDrive w a 0 : ℂ)) (𝓝 (seedMark α β w a r : ℂ)) := by
  have hW : Continuous (cutDrive w a) :=
    hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  have hpos : 0 < (σ : ℝ) - a := sub_pos.2 (by exact_mod_cast haσ)
  have hseed := (Set.disjoint_insert_right.1 (ConformalImageFull.disjoint_insert_of_pos hW hpos hd)).1
  obtain ⟨c, hc⟩ := exists_real_boundary_value (isHPHull_cutObstacle hcα hcβ hα0 hβ0 a r)
    (ConformalImage.isMapOut_mapOut (isHPHull_cutObstacle hcα hcβ hα0 hβ0 a r)) hseed
  have : (𝓝[H] (cutDrive w a 0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    change 0 ≤ (cutDrive w a 0 : ℂ).im
    simp only [ofReal_im, le_refl]
  have he : seedMark α β w a r = c := by
    change (limUnder _ (ConformalImage.mapOut (cutObstacle α β a r))).re = c
    rw [hc.limUnder_eq, ofReal_re]
  rwa [he]

/-- Assemble the original-chart geometry. Separation and initial strict
order are the only additional geometric premises of this local helper. -/
theorem nonempty_lateCutGeometry {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} {q : ℝ} (haσ : a < σ)
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hq : 1 < q) (hασ : α σ = q)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hcut : β r ∈ closure (activeDomain α a β r) ∧
      (∀ z ∈ Restart.prefixSet α a β r, z.im = 0 → z.re < 1) ∧
      (1 : ℂ) ∈ closure (activeDomain α a β r))
    (hfuture : ∀ u ∈ Ioo a σ, α u ∈ H)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a))))
    (horder : hydroMark α β a r (β r) < seedMark α β w a r ∧
      seedMark α β w a r < hydroMark α β a r 1) : Nonempty (LateCutGeometry α β w σ r) := by
  have hcα := hcop.1
  have hcβ := hcop.2.2.2.2.1
  have h1off : (1 : ℂ) ∉ Restart.prefixSet α a β r := by
    intro h
    have := hcut.2.1 1 h (by rfl)
    simp only [one_re, lt_self_iff_false] at this
  obtain ⟨d⟩ := exists_initialChart hcop hα0 hβ0 hβH
    (fun h => hβoff (image_mono (Icc_subset_Icc_right haσ.le) h)) hcut.1 h1off hcut.2.2
  refine ⟨{
    cut := a
    cut_lt := haσ
    seed := seedMark α β w a r
    left := hydroMark α β a r (β r)
    right := hydroMark α β a r 1
    seed_limit := seed_limit_of_clearance hcα hcβ hα0 hβ0 hw haσ hd
    left_lt_seed := horder.1
    seed_lt_right := horder.2
    hull_union := hull_union_of_clearance hcα hcβ hα0 hβ0 hw hw0 hgen hd
    clearance := hd
    left_limit := d.left_limit
    right_limit := d.right_limit
    left_avoids := notMem_closure_image hcα hcβ hw hw0 hgen haσ.le le_rfl hd d d.inv_left
      (beta_notMem_closure_ownHull hcop hα0 hq hασ hNH hβH hβoff)
    right_avoids := ?_
    right_filled := image_collar hcα hcβ hw hw0 hgen haσ.le hd d
      (completed_own_collar hcα hcop.2.2.1 hα0 hq hασ
        (one_notMem_completed_prefix hcα hw hw0 hgen hsw hq hασ))
    tip_limit := fun u hu => tip_limit hcα hcβ hcop.2.1 hw hw0 hgen hu.1.le (hfuture u hu) }⟩
  intro t ht
  let u := ((a : ℝ) + t).toNNReal
  have hue : (u : ℝ) = (a : ℝ) + t := Real.coe_toNNReal _ (add_nonneg a.coe_nonneg ht.1)
  have hau : a ≤ u := by exact_mod_cast (show (a : ℝ) ≤ u by rw [hue]; linarith only [ht.1])
  have huσ : u < σ := by exact_mod_cast (show (u : ℝ) < σ by rw [hue]; linarith only [ht.2])
  have htime : (u : ℝ) - a = t := by rw [hue]; ring
  have hoff := notMem_closure_image hcα hcβ hw hw0 hgen hau huσ.le hd d d.inv_right
    (one_notMem_closure_own_before hcα hw hgen hsw huσ)
  rwa [htime] at hoff

end G8Det.Late

/-- Exact remaining planar input: arbitrarily late cuts with closed
restriction separation and strict order of the three canonical boundary
coordinates. No union identity, inverse chart, collar, flow or driver is
assumed. This proposition remains unproved. -/
def LateSeparationOrderNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q : ℝ),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) → ∀ a₀ < σ, ∃ a ∈ Ioo a₀ σ,
      Disjoint (closure (G8Det.cutObstacle α β a r))
        (closure (fwdHull (G8Det.cutDrive w a) ((σ : ℝ) - a))) ∧
      G8Det.Late.hydroMark α β a r (β r) < G8Det.Late.seedMark α β w a r ∧
      G8Det.Late.seedMark α β w a r < G8Det.Late.hydroMark α β a r 1

theorem lateCutGeometryNHStatement_of_separation_order (hSO : LateSeparationOrderNHStatement) :
    LateCutGeometryNHStatement := by
  intro α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨t₀, ht₀, hact⟩ := G8Det.exists_final_activity_of_nonneg_real hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff (G8Det.nonneg_real_le_of_before hNH hq hασ)
  obtain ⟨a, ha, hd, horder⟩ := hSO α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ
    hβH hβoff hsmall hNH t₀ ht₀
  obtain ⟨_, _, _, hβcl, hreal, h1cl⟩ := hact a ha.1 ha.2
  exact G8Det.Late.nonempty_lateCutGeometry hcop hα0 hβ0 hw hw0 hgen ha.2 hsw hq hασ hβH hβoff hNH
    ⟨hβcl, hreal, h1cl⟩ (fun u hu => (hact u (ha.1.trans hu.1) hu.2).1) hd horder

theorem g8RelativeChartNHStatement_of_separation_order (hSO : LateSeparationOrderNHStatement) :
    G8RelativeChartNHStatement :=
  g8RelativeChartNHStatement_of_lateCutGeometry (lateCutGeometryNHStatement_of_separation_order hSO)

theorem g8DetFrameNHStatement_of_separation_order (hSO : LateSeparationOrderNHStatement) :
    G8DetFrameNHStatement :=
  g8DetFrameNHStatement_of_lateCutGeometry (lateCutGeometryNHStatement_of_separation_order hSO)

theorem g8PositivityStatement_of_separation_order (hW0b : Supp9.W0bStatement.{u})
    (hSO : LateSeparationOrderNHStatement) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_lateCutGeometry hW0b (lateCutGeometryNHStatement_of_separation_order hSO)

end InteractingSLE.RLC
