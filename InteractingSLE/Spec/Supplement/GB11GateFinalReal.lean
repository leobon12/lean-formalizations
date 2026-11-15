/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalBase

/-!
# GB11: real frontier points away from the explored trace

The boundary-set theorem for filled paths shows that an inverse image off the
explored trace is outside the closed hull. Reflection and boundary injectivity
there identify its canonical forward lift, even at original-real contacts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- At a real prime end, a physical image outside the old trace is outside the
closed hull, including when that physical image is real. -/
theorem GateSetup.trMap_real_notMem_closure (d : GateSetup) {x : ℝ}
    (hx : x ∉ oldRealBase d.driver d.γ d.t) :
    trMap d.driver 0 d.t x ∉ closure (fwdHull d.driver d.t) := by
  let η : ℝ → ℂ := fun r => d.γ r.toNNReal
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver η := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hF : YuanCharacterisation.IsBdryExt (fillH (η '' Icc 0 (d.t : ℝ)))
      (fun z => QuantumZipper.fwdMap d.driver d.t z + d.driver d.t)
      (fun w => trMap d.driver 0 d.t (w - d.driver d.t)) :=
    (hη.2.2 (d.t : ℝ) d.t.2) ▸ isBdryExt_uncentered_trMap hη hW hW0 d.t.2
  intro hcl
  have hm : x + d.driver d.t ∈ YuanCharacterisation.bdrySet
      (fillH (η '' Icc 0 (d.t : ℝ)))
      (fun w => trMap d.driver 0 d.t (w - d.driver d.t)) := by
    simpa only [YuanCharacterisation.bdrySet, mem_ofPred_eq, Complex.ofReal_add,
      add_sub_cancel_right, ← hη.2.2 (d.t : ℝ) d.t.2] using hcl
  have hp := hF.bdrySet_subset_pathSet (hη.2.1.mono Icc_subset_Ici_self) hm
  change trMap d.driver 0 d.t x ∉ d.γ '' Icc 0 d.t at hx
  apply hx
  change trMap d.driver 0 d.t (((x + d.driver d.t : ℝ) : ℂ) - d.driver d.t) ∈
    η '' Icc 0 (d.t : ℝ) at hp
  simp only [Complex.ofReal_add, add_sub_cancel_right] at hp
  obtain ⟨r, hr, he⟩ := hp
  exact ⟨r.toNNReal, ⟨zero_le, (Real.toNNReal_le_iff_le_coe).2 hr.2⟩, he⟩

/-- The canonical forward chart inverts the ambient inverse at every real prime
end outside the old trace. The uniqueness step uses the landed boundary-injectivity
theorem off the closed hull. -/
theorem GateSetup.forwardExt_trMap_real (d : GateSetup) {x : ℝ}
    (hx : x ∉ oldRealBase d.driver d.γ d.t) :
    forwardExt d.driver d.t (trMap d.driver 0 d.t x) = (x : ℂ) := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hfree : trMap d.driver 0 d.t x ∈ freeUpper d.driver d.t :=
    ⟨YuanSimpleApprox.trMap_mapsTo_Hbar hη hW hW0 le_rfl d.t.2 (ofReal_mem_Hbar x),
      d.trMap_real_notMem_closure hx⟩
  let β := forwardExt d.driver d.t (trMap d.driver 0 d.t x)
  have hβbar : β ∈ Hbar := forwardExt_mem_Hbar hη hW hW0 d.t.2 hfree
  have hβF : trMap d.driver 0 d.t β = trMap d.driver 0 d.t x :=
    trMap_forwardExt hη hW hW0 d.t.2 hfree
  have hβim : β.im = 0 := by
    refine le_antisymm (not_lt.1 (fun hpos => ?_)) hβbar
    have hno := (YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl d.t.2).2.2.2
      x (by simp)
    exact hno ⟨β, hpos, hβF⟩
  have hβre : (β.re : ℂ) = β := Complex.ext rfl (by simp only [Complex.ofReal_im, hβim])
  have hF := isBdryExt_uncentered_trMap hη hW hW0 d.t.2
  have hxF : trMap d.driver 0 d.t
      ((((x + d.driver d.t : ℝ)) : ℂ) - d.driver d.t) ∉
      closure (fwdHull d.driver d.t) := by
    simpa only [Complex.ofReal_add, add_sub_cancel_right] using d.trMap_real_notMem_closure hx
  have heq : trMap d.driver 0 d.t
      ((((x + d.driver d.t : ℝ)) : ℂ) - d.driver d.t) =
      trMap d.driver 0 d.t ((((β.re + d.driver d.t : ℝ)) : ℂ) - d.driver d.t) := by
    simp only [Complex.ofReal_add, add_sub_cancel_right, hβre]
    exact hβF.symm
  have hre : x = β.re := add_right_cancel (hF.eq_of_eq hxF heq)
  exact hβre.symm.trans (congrArg Complex.ofReal hre.symm)

/-- A real current frontier point outside the old real base maps to the original
pocket frontier. In particular its physical inversion is not the original target. -/
theorem GateSetup.real_frontier_physical (d : GateSetup) {x : ℝ}
    (hx : (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t))
    (hxB : x ∉ oldRealBase d.driver d.γ d.t) :
    -(trMap d.driver 0 d.t x)⁻¹ ∈ frontier d.C ∧ trMap d.driver 0 d.t x ≠ 0 := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hcl := (frontier_ownDomain_image_closure hη hW hW0 d.t.2 hx).2
  have hp0 : trMap d.driver 0 d.t x ≠ 0 := by
    intro he
    apply hxB
    exact ⟨0, ⟨zero_le, zero_le⟩, by simpa [he] using d.generating.1⟩
  have hc : ContinuousAt (fun z : ℂ => -z⁻¹) (trMap d.driver 0 d.t x) :=
    (continuousAt_id.inv₀ hp0).neg
  have hclC : -(trMap d.driver 0 d.t x)⁻¹ ∈ closure d.C :=
    closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hz)
      (hc.continuousWithinAt.mem_closure_image hcl)
  have hF := isBdryExt_uncentered_trMap hη hW hW0 d.t.2
  have hoff : trMap d.driver 0 d.t
      ((((x + d.driver d.t : ℝ)) : ℂ) - d.driver d.t) ∉
      closure (fwdHull d.driver d.t) := by
    simpa only [Complex.ofReal_add, add_sub_cancel_right] using d.trMap_real_notMem_closure hxB
  have him := hF.im_eq_zero hoff
  change (trMap d.driver 0 d.t
    ((((x + d.driver d.t : ℝ)) : ℂ) - d.driver d.t)).im = 0 at him
  simp only [Complex.ofReal_add, add_sub_cancel_right] at him
  have hinv : (-(trMap d.driver 0 d.t x)⁻¹).im = 0 := by
    rw [Complex.neg_im, Complex.inv_im, him, neg_zero, zero_div, neg_zero]
  refine ⟨⟨hclC, fun hi => ?_⟩, hp0⟩
  have hpos := subset_H_of_mem_betweenComponents d.component (interior_subset hi)
  change 0 < (-(trMap d.driver 0 d.t x)⁻¹).im at hpos
  exact (ne_of_gt hpos) hinv

/-- The selected arms cover the entire real current frontier outside the old
real base. Thus the remaining real incidence question concerns only old trace images. -/
theorem SelectedGateArms.real_frontier_off_base {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (hR : IsWallVisitCut d.γ d.αR d.t cutR)
    (hL : IsWallVisitCut d.γ d.αL d.t cutL) {x : ℝ}
    (hx : (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t))
    (hxB : x ∉ oldRealBase d.driver d.γ d.t) :
    mu x ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 := by
  obtain ⟨hp, hp0⟩ := d.real_frontier_physical hx hxB
  have key : ∀ (α : ℝ≥0 → ℂ) (cut : ℝ≥0∞), α 0 = 0 → IsWallVisitCut d.γ α d.t cut →
      ∀ r : ℝ≥0, α r = -(trMap d.driver 0 d.t x)⁻¹ → 0 < r ∧ (r : ℝ≥0∞) < cut ∧
        mu (forwardExt d.driver d.t (-(α r)⁻¹)) = mu x := by
    intro α cut hα0 hcut r hr
    have he : -(α r)⁻¹ = trMap d.driver 0 d.t x := by rw [hr, negInv_negInv']
    have hr0 : 0 < r := pos_iff_ne_zero.2 (fun hzero => hp0 (by
      rw [← he, hzero, hα0, inv_zero, neg_zero]))
    refine ⟨hr0, lt_of_not_ge (fun hle => ?_), ?_⟩
    · have hv := (mem_wallHitParameters_iff
        (Sec5.continuous_of_isGeneratingTrace_top d.generating)).1 ((hcut.2 r).2 hle)
      have hm := negInv_mem_image_of_firstVisit_le
        (Sec5.continuous_of_isGeneratingTrace_top d.generating)
        (lt_of_le_of_lt hv ENNReal.coe_lt_top) hv
      apply hxB
      change trMap d.driver 0 d.t x ∈ d.γ '' Icc 0 d.t
      exact he ▸ hm
    · rw [he, d.forwardExt_trMap_real hxB]
  rcases d.shape.frontier_subset hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
  · obtain ⟨hr0, hlt, he'⟩ := key d.αR cutR d.barrier.1.2.2.1 hR r he
    exact Or.inl (he' ▸ a.cover_right r hr0 hr.1 hlt)
  · obtain ⟨hr0, hlt, he'⟩ := key d.αL cutL d.barrier.2.1.2.2.1 hL r he
    exact Or.inr (he' ▸ a.cover_left r hr0 hr.1 hlt)

end InteractingSLE.Theorem14.GB11Chart
