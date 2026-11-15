/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetClosedMetric

/-!
# G8: all sufficiently late image hulls are disjoint in the open half-plane

Packet PROVE-G8-DET. The preceding physical pocket proof applies after
one final activity and trace-separation threshold. No closed image-hull
separation, boundary-order or positive-distance premise is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.RLC.G8Det.Closed

/-- After an arbitrarily late threshold, the actual image hulls are
pairwise disjoint as subsets of `H` at every later cut. -/
theorem exists_final_disjoint_images {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r a₀ : ℝ≥0} {q : ℝ} (ha₀ : a₀ < σ)
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hq : 1 < q) (hασ : α σ = q)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) :
    ∃ b ∈ Ioo a₀ σ, ∀ a ∈ Ioo b σ,
      Disjoint (cutObstacle α β a r) (fwdHull (cutDrive w a) ((σ : ℝ) - a)) := by
  obtain ⟨t₀, ht₀, hact⟩ := exists_final_activity_of_nonneg_real hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff (nonneg_real_le_of_before hNH hq hασ)
  obtain ⟨b, hb, hoff⟩ := Late.exists_late_no_new_contact hcop.1 (max_lt ha₀ ht₀) hq hασ hsmall
  have hbt : t₀ < b := (le_max_right _ _).trans_lt hb.1
  refine ⟨b, ⟨(le_max_left _ _).trans_lt hb.1, hb.2⟩, fun a ha => ?_⟩
  exact disjoint_images hcop hα0 hw hw0 hgen ha.2.le hq hασ hNH
    (fun t ht => hoff t ⟨ha.1.trans ht.1, ht.2⟩)
    (fun t ht => (hact t (hbt.trans (ha.1.trans ht.1)) ht.2).2.2.1)

/-- At all those cuts, a common closure point must be real. The statement
quantifies over the full closed hulls, including swallowed pockets. -/
theorem exists_final_real_intersection {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r a₀ : ℝ≥0} {q : ℝ} (ha₀ : a₀ < σ)
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hq : 1 < q) (hασ : α σ = q)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) :
    ∃ b ∈ Ioo a₀ σ, ∀ a ∈ Ioo b σ, ∀ z : ℂ,
      z ∈ closure (cutObstacle α β a r) →
      z ∈ closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)) → z.im = 0 := by
  obtain ⟨b, hb, hd⟩ := exists_final_disjoint_images hcop hα0 hβ0 hw hw0 hgen ha₀ hsw hq hασ
    hβH hβoff hsmall hNH
  refine ⟨b, hb, fun a ha z hzA hzK => ?_⟩
  have hV : Continuous (cutDrive w a) :=
    hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  exact im_eq_zero_of_mem_closures (isHPHull_cutObstacle hcop.1 hcop.2.2.2.2.1 hα0 hβ0 a r)
    (isHPHull_fwdHull hV (sub_nonneg.2 (by exact_mod_cast ha.2.le))) (hd a ha) hzA hzK

end InteractingSLE.RLC.G8Det.Closed
