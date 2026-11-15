/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepOrder

/-!
# G8: both strict boundary inequalities from separation

Packet PROVE-G8-DET. No boundary order is assumed. The right mark's filled
collar and the retained tip's survival determine which side of the relative
driver the retained mark occupies.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull IsForwardSol)

namespace InteractingSLE.RLC.G8Det.Late

/-- Closed restriction separation suffices for the complete initial order.
All mark limits and the completed filled collar are supplied by landed results. -/
theorem boundary_order_of_clearance {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} {q : ℝ} (haσ : a < σ)
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hq : 1 < q) (hασ : α σ = q)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (haH : α a ∈ H) (haD : α a ∈ closure (activeDomain α a β r))
    (hβD : β r ∈ closure (activeDomain α a β r))
    (hreal : ∀ z ∈ Restart.prefixSet α a β r, z.im = 0 → z.re < 1)
    (h1D : (1 : ℂ) ∈ closure (activeDomain α a β r))
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) :
    hydroMark α β a r (β r) < seedMark α β w a r ∧
      seedMark α β w a r < hydroMark α β a r 1 := by
  have hcα := hcop.1
  have hcβ := hcop.2.2.2.2.1
  have h1off : (1 : ℂ) ∉ Restart.prefixSet α a β r := by
    intro h
    have := hreal 1 h (by rfl)
    simp only [one_re, lt_self_iff_false] at this
  obtain ⟨d⟩ := exists_initialChart hcop hα0 hβ0 hβH
    (fun h => hβoff (image_mono (Icc_subset_Icc_right haσ.le) h)) hβD h1off h1D
  have hseed := inv_seed hcop hα0 hβ0 hw hw0 hgen haσ haH haD hd d
  have hright := d.lt_right_of_inv_mem hcα hcβ hcop.2.2.1 hcop.2.2.2.2.2.2.1 hα0 hβ0 hreal
    (y := seedMark α β w a r) (by rw [hseed]; exact Or.inl ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩)
  have hleftRight := d.lt_right_of_inv_mem hcα hcβ hcop.2.2.1 hcop.2.2.2.2.2.2.1 hα0 hβ0 hreal
    (y := hydroMark α β a r (β r)) (by rw [d.inv_left]; exact Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩)
  have hne : hydroMark α β a r (β r) ≠ seedMark α β w a r := by
    intro he
    have hp : β r = α a := by rw [← d.inv_left, he, hseed]
    exact hβoff ⟨a, ⟨zero_le, haσ.le⟩, hp.symm⟩
  have hV : Continuous (cutDrive w a) :=
    hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  have hT : 0 < (σ : ℝ) - a := sub_pos.2 (by exact_mod_cast haσ)
  have hA := isHPHull_cutObstacle hcα hcβ hα0 hβ0 a r
  have hφ := ConformalImage.isMapOut_mapOut hA
  obtain ⟨e⟩ := exists_relativeImage hV hT hA hφ hd
  have he0 : e.driver 0 = seedMark α β w a r :=
    e.driver_zero hV hT.le hA (seed_limit_of_clearance hcα hcβ hα0 hβ0 hw haσ hd) hφ
  have havoid := notMem_closure_image hcα hcβ hw hw0 hgen haσ.le le_rfl hd d d.inv_left
    (beta_notMem_closure_ownHull hcop hα0 hq hασ hNH hβH hβoff)
  have halive : ∃ v, IsForwardSol e.driver (hydroMark α β a r (β r) : ℂ)
      (e.clock ((σ : ℝ) - a)) v := by
    apply alive_of_notMem_closure e.continuous_driver (by rw [he0]; exact hne) (e.clock_pos hT).le
    rw [e.hull_eq _ ⟨hT.le, le_rfl⟩]
    exact havoid
  have hcollar := image_collar hcα hcβ hw hw0 hgen haσ.le hd d
    (completed_own_collar hcα hcop.2.2.1 hα0 hq hασ
      (one_notMem_completed_prefix hcα hw hw0 hgen hsw hq hασ))
  have hdead : ¬ ∃ v, IsForwardSol e.driver (hydroMark α β a r 1 : ℂ)
      (e.clock ((σ : ℝ) - a)) v := by
    apply GB1.not_alive_of_hull e.continuous_driver (e.clock_pos hT).le
    obtain ⟨δ, hδ, hfill⟩ := hcollar
    refine ⟨δ, hδ, fun z hz hdist => ?_⟩
    rw [e.hull_eq _ ⟨hT.le, le_rfl⟩]
    exact hfill z hz hdist
  refine ⟨?_, hright⟩
  rw [← he0]
  exact lt_driver_of_survives e.continuous_driver (e.clock_pos hT).le
    (by rw [he0]; exact hne) hleftRight halive hdead

end InteractingSLE.RLC.G8Det.Late
