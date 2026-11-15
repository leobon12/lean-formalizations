/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalArc

/-! # GB11: exact prefix images imply the physical gate conditions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- A nonzero point of an exact prefix image is either the gate or an actual
positive unvisited wall parameter. -/
theorem CompactifiedPrefixArc.mem_cases {d : GateSetup} {α : ℝ≥0 → ℂ}
    {exit : ℝ≥0} {cut : ℝ≥0∞} (a : CompactifiedPrefixArc d α exit cut)
    {u : ℝ} (hu : u ∈ Icc 0 1) (hne : a.wall u ≠ 0) :
    a.wall u = mu a.q ∨ ∃ r : ℝ≥0, 0 < r ∧ exit ≤ r ∧ (r : ℝ≥0∞) < cut ∧
      a.wall u = mu (forwardExt d.driver d.t (-(α r)⁻¹)) := by
  have hm := a.image ▸ mem_image_of_mem a.wall hu
  rcases hm with (h | ⟨r, hr, he⟩) | h
  · exact Or.inl h
  · exact Or.inr ⟨r, hr.1, hr.2.1, hr.2.2, he.symm⟩
  · by_cases h0 : exit = 0
    · exact False.elim (hne (by simpa only [h0, ite_eq_left, mem_singleton_iff] using h))
    · simp only [h0, ↓reduceIte, notMem_empty] at h

/-- The real gate belongs to the old real trace base, whether its cut is finite
or at infinity. -/
theorem CompactifiedPrefixArc.gate_old {d : GateSetup} {α : ℝ≥0 → ℂ}
    {exit : ℝ≥0} {cut : ℝ≥0∞} (a : CompactifiedPrefixArc d α exit cut)
    (hcut : IsWallVisitCut d.γ α d.t cut) : a.q ∈ oldRealBase d.driver d.γ d.t := by
  change trMap d.driver 0 d.t a.q ∈ d.γ '' Icc 0 d.t
  rw [a.gate_value]
  by_cases htop : cut = ⊤
  · rw [ite_eq_left htop]
    exact ⟨0, ⟨le_rfl, zero_le⟩, d.generating.1⟩
  · rw [ite_eq_right htop]
    have hv := (mem_wallHitParameters_iff
      (Sec5.continuous_of_isGeneratingTrace_top d.generating)).1
      ((hcut.2 cut.toNNReal).2 (ENNReal.coe_toNNReal htop).ge)
    exact negInv_mem_image_of_firstVisit_le
      (Sec5.continuous_of_isGeneratingTrace_top d.generating)
      (lt_of_le_of_lt hv ENNReal.coe_lt_top) hv

/-- Positive parameters of an exact simple prefix avoid the old trace. -/
theorem CompactifiedPrefixArc.free {d : GateSetup} {α : ℝ≥0 → ℂ}
    {exit : ℝ≥0} {cut : ℝ≥0∞} (a : CompactifiedPrefixArc d α exit cut)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    (hcut : IsWallVisitCut d.γ α d.t cut) :
    ∀ u ∈ Ioc (0 : ℝ) 1, a.wall u ≠ 0 →
      trMap d.driver 0 d.t (muInv (a.wall u)) ∉ d.γ '' Icc 0 d.t := by
  intro u hu hne
  rcases a.mem_cases ⟨hu.1.le, hu.2⟩ hne with he | ⟨r, hr0, -, hrcut, he⟩
  · exact False.elim (hu.1.ne' (a.injective ⟨hu.1.le, hu.2⟩
      ⟨le_rfl, zero_le_one⟩ (he.trans a.zero.symm)))
  · have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
    have hW0 : d.driver 0 = 0 := by
      simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
    have hfree := negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero
      d.generating hα hrev hcut.2 hr0 hrcut
    have hval : trMap d.driver 0 d.t (forwardExt d.driver d.t (-(α r)⁻¹)) = -(α r)⁻¹ :=
      trMap_forwardExt (isLoewnerTrace_of_isGeneratingTrace d.generating) hW hW0 d.t.2 hfree
    rw [he, muInv_mu]
    intro hm
    rw [hval] at hm
    have hrhit : r ∈ wallHitParameters d.γ α d.t := by
      obtain ⟨v, hv, heq⟩ := hm
      refine ⟨v, hv, ?_⟩
      rw [heq]
      have hα0 : α r ≠ 0 := fun he0 => hr0.ne'
        (hα.2.1 (he0.trans hα.2.2.1.symm))
      field_simp
    exact (not_le.2 hrcut) ((hcut.2 r).1 hrhit)

/-- The exact wall images lie outside the physical pocket. This applies to the
real gate too, using its retained finite-cut/seed value. -/
theorem CompactifiedPrefixArc.physical_outside {d : GateSetup} {α : ℝ≥0 → ℂ}
    {exit : ℝ≥0} {cut : ℝ≥0∞} (a : CompactifiedPrefixArc d α exit cut)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    (hcut : IsWallVisitCut d.γ α d.t cut) (hout : ∀ r : ℝ≥0, α r ∉ d.C) :
    ∀ u ∈ Icc (0 : ℝ) 1, a.wall u ≠ 0 →
      trMap d.driver 0 d.t (muInv (a.wall u)) ∉ relDom d.C := by
  have hneg : ∀ r : ℝ≥0, -(α r)⁻¹ ∉ relDom d.C := by
    intro r hr
    apply hout r
    change -(-(α r)⁻¹)⁻¹ ∈ d.C at hr
    rwa [negInv_negInv'] at hr
  intro u hu hne
  rcases a.mem_cases hu hne with he | ⟨r, hr0, -, hrcut, he⟩
  · rw [he, muInv_mu, a.gate_value]
    by_cases htop : cut = ⊤
    · rw [ite_eq_left htop]
      intro hr
      have h0C : (0 : ℂ) ∈ d.C := by
        simpa only [relDom, mem_preimage, inv_zero, neg_zero] using hr
      exact lt_irrefl (0 : ℝ) (subset_H_of_mem_betweenComponents d.component h0C)
    · rw [ite_eq_right htop]
      exact hneg _
  · have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
    have hW0 : d.driver 0 = 0 := by
      simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
    have hfree := negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero
      d.generating hα hrev hcut.2 hr0 hrcut
    have hval : trMap d.driver 0 d.t (forwardExt d.driver d.t (-(α r)⁻¹)) = -(α r)⁻¹ :=
      trMap_forwardExt (isLoewnerTrace_of_isGeneratingTrace d.generating) hW hW0 d.t.2 hfree
    rw [he, muInv_mu, hval]
    exact hneg r

end InteractingSLE.Theorem14.GB11Chart
