/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalZero

/-! # GB11: contacts of the two exact current prefixes -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- Unvisited common contacts of the selected prefixes are their common exit.
For a bounded pocket its entry has already been visited; for an unbounded pocket
Janiszewski's landed contact theorem excludes every other common contact. -/
theorem GateSetup.unvisited_prefix_contact (d : GateSetup) {cutR cutL : ℝ≥0∞}
    (hR : IsWallVisitCut d.γ d.αR d.t cutR) (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    {r s : ℝ≥0} (hr : d.s₁ ≤ r) (hs : d.t₁ ≤ s)
    (hrcut : (r : ℝ≥0∞) < cutR) (hscut : (s : ℝ≥0∞) < cutL)
    (he : d.αR r = d.αL s) : r = d.s₁ := by
  obtain ⟨y, hy, -, -, hCy⟩ := d.component
  have hyC : y ∈ d.C := hCy ▸ mem_connectedComponentIn hy
  have hCc : IsPreconnected d.C := hCy ▸ isPreconnected_connectedComponentIn
  have hCF : ∀ z ∈ d.C, z ∉ range d.αR ∪ range d.αL := by
    intro z hz
    exact ((hCy ▸ connectedComponentIn_subset _ _ : d.C ⊆ H \ (range d.αR ∪ range d.αL)) hz).2
  have hCo : IsOpen d.C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component
  by_cases htop : d.s₂ = ⊤
  · have hinter := inter_subset_of_unboundedPocket d.barrier.1 d.barrier.2.1 d.barrier.2.2.1
      d.shape.contact hCo hCc (subset_H_of_mem_betweenComponents d.component)
      (d.shape.unbounded htop) hyC hCF d.shape.frontier_subset_Ici d.shape.mem_closure_exit
    exact d.barrier.1.2.1 (hinter ⟨⟨r, hr, rfl⟩, ⟨s, hs, he.symm⟩⟩)
  · have htTop : d.t₂ ≠ ⊤ := fun he => htop (d.shape.top_iff.2 he)
    have hγc := Sec5.continuous_of_isGeneratingTrace_top d.generating
    have hentryR : GB11.firstVisit d.γ (d.αR d.s₂.toNNReal) ≤ (d.t : ℝ≥0∞) :=
      (entryTime_spec hγc d.barrier d.shape htop).1 ▸ ENNReal.coe_le_coe.2 d.entry_le
    have hentryL : GB11.firstVisit d.γ (d.αL d.t₂.toNNReal) ≤ (d.t : ℝ≥0∞) := by
      rw [← (d.shape.entry htop).1]
      exact hentryR
    have hcutR : cutR ≤ d.s₂.toNNReal :=
      (hR.2 _).1 ((mem_wallHitParameters_iff hγc).2 hentryR)
    have hcutL : cutL ≤ d.t₂.toNNReal :=
      (hL.2 _).1 ((mem_wallHitParameters_iff hγc).2 hentryL)
    have hr2 : r < d.s₂.toNNReal := ENNReal.coe_lt_coe.1 (hrcut.trans_le hcutR)
    have hs2 : s < d.t₂.toNNReal := ENNReal.coe_lt_coe.1 (hscut.trans_le hcutL)
    have hfr : frontier d.C ⊆ d.αR '' Icc d.s₁ d.s₂.toNNReal ∪
        d.αL '' Icc d.t₁ d.t₂.toNNReal := by
      refine d.shape.frontier_subset.trans (union_subset_union (image_mono ?_) (image_mono ?_))
      · intro v hv
        exact ⟨hv.1, ENNReal.coe_le_coe.1 (hv.2.trans_eq (ENNReal.coe_toNNReal htop).symm)⟩
      · intro v hv
        exact ⟨hv.1, ENNReal.coe_le_coe.1 (hv.2.trans_eq (ENNReal.coe_toNNReal htTop).symm)⟩
    obtain ⟨hentry, hentryCl, hbounded⟩ := d.shape.entry htop
    have hinter := inter_subset_of_boundedPocket d.barrier.1 d.barrier.2.1 d.barrier.2.2.1
      d.shape.contact hentry hCo hCc hbounded hyC hCF hfr d.shape.mem_closure_exit hentryCl
    rcases hinter ⟨⟨r, ⟨hr, hr2.le⟩, rfl⟩, ⟨s, ⟨hs, hs2.le⟩, he.symm⟩⟩ with hexit | hentry
    · exact d.barrier.1.2.1 hexit
    · exact False.elim (hr2.ne (d.barrier.1.2.1 hentry))

/-- Both intrinsic exit images agree, including the original target. -/
theorem GateSetup.prefixJunction_eq (d : GateSetup) :
    prefixJunction d d.αR d.s₁ = prefixJunction d d.αL d.t₁ := by
  have hz : d.s₁ = 0 ↔ d.t₁ = 0 := by
    constructor
    · intro he
      apply d.barrier.2.1.2.1
      rw [← d.shape.contact, he, d.barrier.1.2.2.1, d.barrier.2.1.2.2.1]
    · intro he
      apply d.barrier.1.2.1
      rw [d.shape.contact, he, d.barrier.2.1.2.2.1, d.barrier.1.2.2.1]
  unfold prefixJunction
  by_cases hs : d.s₁ = 0
  · simp only [hs, hz.1 hs, ite_eq_left]
  · rw [ite_eq_right hs, ite_eq_right (fun ht => hs (hz.2 ht)), d.shape.contact]

/-- The compactification point occurs on an exact arm precisely for an exit at
zero. In particular no finite prime-end lift is confused with infinity. -/
theorem CompactifiedPrefixArc.zero_mem_image_iff {d : GateSetup} {α : ℝ≥0 → ℂ}
    {exit : ℝ≥0} {cut : ℝ≥0∞} (a : CompactifiedPrefixArc d α exit cut)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    (hcut : IsWallVisitCut d.γ α d.t cut) : (0 : ℂ) ∈ a.wall '' Icc 0 1 ↔ exit = 0 := by
  rw [a.image, selectedPrefixImage]
  constructor
  · rintro ((he | ⟨r, hr, he⟩) | he)
    · exact False.elim ((mu_ne_zero_of_mem_Hbar (ofReal_mem_Hbar a.q)) he.symm)
    · have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
      have hW0 : d.driver 0 = 0 := by
        simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
      exact False.elim ((mu_ne_zero_of_mem_Hbar (forwardExt_mem_Hbar
        (isLoewnerTrace_of_isGeneratingTrace d.generating) hW hW0 d.t.2
        (negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero d.generating
          hα hrev hcut.2 hr.1 hr.2.2))) he)
    · by_contra hne
      simp only [ite_eq_right hne, notMem_empty] at he
  · intro he
    exact Or.inr (by simp only [he, ite_eq_left, mem_singleton_iff])

/-- The exact compactified arms have only their common exit and possibly their
common gate in common. The finite-cut entry is excluded by first-visit order. -/
theorem CompactifiedPrefixArc.wall_inter {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (hR : IsWallVisitCut d.γ d.αR d.t cutR) (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    (aR : CompactifiedPrefixArc d d.αR d.s₁ cutR)
    (aL : CompactifiedPrefixArc d d.αL d.t₁ cutL) :
    aR.wall '' Icc 0 1 ∩ aL.wall '' Icc 0 1 ⊆ {aR.wall 0, prefixJunction d d.αR d.s₁} := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver (fun r => d.γ r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace d.generating
  have hval : ∀ (α : ℝ≥0 → ℂ), GB11.IsCompleteSimpleFlow α →
      (∀ r r' : ℝ≥0, 0 < r → r < r' → GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r)) →
      ∀ (cut : ℝ≥0∞), IsWallVisitCut d.γ α d.t cut → ∀ r : ℝ≥0,
      0 < r → (r : ℝ≥0∞) < cut →
      trMap d.driver 0 d.t (forwardExt d.driver d.t (-(α r)⁻¹)) = -(α r)⁻¹ := by
    intro α hα hrev cut hc r hr0 hrc
    exact trMap_forwardExt hη hW hW0 d.t.2
      (negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero d.generating
        hα hrev hc.2 hr0 hrc)
  rintro z ⟨⟨u, hu, rfl⟩, ⟨v, hv, he⟩⟩
  by_cases hzero : aR.wall u = 0
  · have hexit := (aR.zero_mem_image_iff d.barrier.1 d.barrier.2.2.2.2.2.1 hR).1
      ⟨u, hu, hzero⟩
    exact Or.inr (by rw [mem_singleton_iff, hzero, prefixJunction, ite_eq_left hexit])
  · have hzeroL : aL.wall v ≠ 0 := he ▸ hzero
    rcases aR.mem_cases hu hzero with hgate | ⟨r, hr0, hr, hrc, her⟩
    · exact Or.inl (hgate.trans aR.zero.symm)
    · have hFr := hval d.αR d.barrier.1 d.barrier.2.2.2.2.2.1 cutR hR r hr0 hrc
      rcases aL.mem_cases hv hzeroL with hgateL | ⟨s, hs0, hs, hsc, hes⟩
      · have hq : forwardExt d.driver d.t (-(d.αR r)⁻¹) = (aL.q : ℂ) :=
          mu_injective (her.symm.trans (he.symm.trans hgateL))
        have hOld := aL.gate_old hL
        change trMap d.driver 0 d.t aL.q ∈ d.γ '' Icc 0 d.t at hOld
        rw [← hq, hFr] at hOld
        exact False.elim (negInv_notMem_trace_of_lt_cut d.barrier.1 hR hr0 hrc hOld)
      · have hFs := hval d.αL d.barrier.2.1 d.barrier.2.2.2.2.2.2 cutL hL s hs0 hsc
        have hb : forwardExt d.driver d.t (-(d.αR r)⁻¹) =
            forwardExt d.driver d.t (-(d.αL s)⁻¹) :=
          mu_injective (her.symm.trans (he.symm.trans hes))
        have hphys : d.αR r = d.αL s := negInv_injective
          (hFr.symm.trans ((congrArg (trMap d.driver 0 d.t) hb).trans hFs))
        have hrexit := d.unvisited_prefix_contact hR hL hr hs hrc hsc hphys
        have hexit : d.s₁ ≠ 0 := hrexit ▸ hr0.ne'
        exact Or.inr (by rw [mem_singleton_iff, her, prefixJunction, ite_eq_right hexit, hrexit])

end InteractingSLE.Theorem14.GB11Chart
