/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalPair

/-! # GB11: sorting the two actual arms constructs the current face -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- An old-base point on either selected arm is a gate. This uses only the
proved freeness of the positive part of each arm. -/
theorem UnorderedGateArms.oldBase_mem_arms_iff {d : GateSetup}
    (a : UnorderedGateArms d) {x : ℝ}
    (hx : x ∈ oldRealBase d.driver d.γ d.t) :
    mu x ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 ↔ x = a.qR ∨ x = a.qL := by
  have key : ∀ (b : ℝ → ℂ) (q : ℝ), b 0 = mu q →
      (∀ u ∈ Ioc (0 : ℝ) 1, b u ≠ 0 →
        trMap d.driver 0 d.t (muInv (b u)) ∉ d.γ '' Icc 0 d.t) →
      mu x ∈ b '' Icc 0 1 → x = q := by
    intro b q hb0 hfree hmem
    obtain ⟨u, hu, he⟩ := hmem
    have hu0 : u = 0 := by
      by_contra hne
      have hp : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hne)
      have hnonzero : b u ≠ 0 := he.symm ▸ mu_ne_zero_of_mem_Hbar (ofReal_mem_Hbar x)
      have hval : muInv (b u) = (x : ℂ) := by rw [he, muInv_mu]
      exact hfree u ⟨hp, hu.2⟩ hnonzero (hval.symm ▸ hx)
    exact Complex.ofReal_injective (mu_injective (he.symm.trans (hu0 ▸ hb0)))
  constructor
  · rintro (h | h)
    · exact Or.inl (key _ _ a.right_zero a.right_free h)
    · exact Or.inr (key _ _ a.left_zero a.left_free h)
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, a.right_zero⟩
    · exact Or.inr ⟨0, ⟨le_rfl, zero_le_one⟩, a.left_zero⟩

/-- Every adherent old-base point lies between the selected gates. An extreme
point outside the gates would have an open real collar in the compact set of
adherent old-base points, contradicting extremality. -/
theorem UnorderedGateArms.oldBase_frontier_interval {d : GateSetup}
    (a : UnorderedGateArms d) (horder : a.qR ≤ a.qL) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (ownDomain d.driver d.C d.t))
    (hxB : x ∈ oldRealBase d.driver d.γ d.t) : x ∈ Icc a.qR a.qL := by
  classical
  let O := ownDomain d.driver d.C d.t
  let J := a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1
  let D := oldRealBase d.driver d.γ d.t ∩ Complex.ofReal ⁻¹' closure O
  have hDc : IsCompact D := d.isCompact_oldRealBase.inter_right
    (isClosed_closure.preimage Complex.continuous_ofReal)
  have hxc : x ∈ D := ⟨hxB, hx⟩
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hOo : IsOpen O := isOpen_ownDomain (isLoewnerTrace_of_isGeneratingTrace d.generating)
    hW hW0 d.t.2 (isOpen_of_mem_betweenComponents
      (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
      (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component)
    (subset_H_of_mem_betweenComponents d.component)
  have hOH : O ⊆ H := fun _ hz => hz.1
  have hJc : IsClosed J := ((isCompact_Icc.image_of_continuousOn a.right_continuous).union
    (isCompact_Icc.image_of_continuousOn a.left_continuous)).isClosed
  have hcollar : ∀ z ∈ D, z ≠ a.qR → z ≠ a.qL →
      ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - z| < ε → y ∈ D := by
    intro z hz hqR hqL
    have hzJ : mu z ∉ J := fun h => (a.oldBase_mem_arms_iff hz.1).1 h |>.elim hqR hqL
    obtain ⟨ε, hε, hnear⟩ := real_frontier_collar hOo hOH hJc
      (fun w hw hwH => a.cover_upper w hw hwH) hz.2 hzJ
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨hycl, hyJ⟩ := hnear y hy
    refine ⟨?_, hycl⟩
    by_contra hyB
    have hyfr : (y : ℂ) ∈ frontier O := ⟨hycl, fun hi =>
      lt_irrefl (0 : ℝ) (hOH (interior_subset hi))⟩
    exact hyJ (a.cover_real_off_base y hyfr hyB)
  obtain ⟨m, hm⟩ := hDc.exists_isLeast ⟨x, hxc⟩
  have hm_gate : m = a.qR ∨ m = a.qL := by
    by_contra he
    obtain ⟨ε, hε, hnear⟩ := hcollar m hm.1 (fun h => he (Or.inl h))
      (fun h => he (Or.inr h))
    have hdist : |m - ε / 2 - m| < ε := by
      rw [show m - ε / 2 - m = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have hle := hm.2 (hnear (m - ε / 2) hdist)
    linarith
  obtain ⟨M, hM⟩ := hDc.exists_isGreatest ⟨x, hxc⟩
  have hM_gate : M = a.qR ∨ M = a.qL := by
    by_contra he
    obtain ⟨ε, hε, hnear⟩ := hcollar M hM.1 (fun h => he (Or.inl h))
      (fun h => he (Or.inr h))
    have hdist : |M + ε / 2 - M| < ε := by
      rw [show M + ε / 2 - M = ε / 2 by ring, abs_of_pos (half_pos hε)]
      linarith
    have hle := hM.2 (hnear (M + ε / 2) hdist)
    linarith
  constructor
  · rcases hm_gate with rfl | rfl
    · exact hm.2 hxc
    · exact horder.trans (hm.2 hxc)
  · rcases hM_gate with rfl | rfl
    · exact (hM.2 hxc).trans horder
    · exact hM.2 hxc

/-- Sorting is the only ordering needed for the current face. The original
wall labels and their finite/infinite parametrizations have already been retained
in the exact prefix arcs used to construct this pair. -/
def UnorderedGateArms.currentGateBoundary_of_le {d : GateSetup}
    (a : UnorderedGateArms d) (horder : a.qR ≤ a.qL) : CurrentGateBoundary d.driver d.C d.t := by
  have hbase := gb11OldRealBaseStatement d.W' d.γ d.continuous_driver d.driver_zero d.generating d.t
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver (fun r => d.γ r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace d.generating
  have hOo := isOpen_ownDomain hη hW hW0 d.t.2 (isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component)
    (subset_H_of_mem_betweenComponents d.component)
  refine {
    qR := a.qR, qL := a.qL, junction := a.junction,
    rightWall := a.rightWall, leftWall := a.leftWall, gates_le := horder,
    right_continuous := a.right_continuous, left_continuous := a.left_continuous,
    right_injective := a.right_injective, left_injective := a.left_injective,
    right_zero := a.right_zero, left_zero := a.left_zero,
    right_one := a.right_one, left_one := a.left_one, wall_inter := a.wall_inter,
    right_base := wall_inter_gateBase_subset
      (mapsTo_gate_interval_oldTrace hbase a.right_gate_old a.left_gate_old) a.right_free,
    left_base := wall_inter_gateBase_subset
      (mapsTo_gate_interval_oldTrace hbase a.right_gate_old a.left_gate_old) a.left_free,
    right_outside := wall_disjoint_ownDomain a.right_physical_outside,
    left_outside := wall_disjoint_ownDomain a.left_physical_outside,
    frontier_subset := ?_ }
  intro ζ hζ
  rcases frontier_mu_image_subset hOo (fun _ hw => hw.1) hζ with ⟨w, hw, rfl⟩ | he
  · by_cases hwH : w ∈ H
    · exact Or.inl (a.cover_upper w hw hwH)
    · have hwbar := (frontier_ownDomain_image_closure hη hW hW0 d.t.2 hw).1
      have him : w.im = 0 := le_antisymm (not_lt.1 hwH) hwbar
      have hre : (w.re : ℂ) = w := Complex.ext rfl (by simp only [Complex.ofReal_im, him])
      rw [← hre] at hw ⊢
      by_cases hxB : w.re ∈ oldRealBase d.driver d.γ d.t
      · exact Or.inr ⟨(w.re : ℂ), ⟨w.re, a.oldBase_frontier_interval horder hw.1 hxB, rfl⟩, rfl⟩
      · exact Or.inl (a.cover_real_off_base w.re hw hxB)
  · rw [mem_singleton_iff] at he
    subst ζ
    exact Or.inl (a.cover_zero hζ)

/-- Every unordered exact pair gives a current gate boundary, by exchanging the
two arms if their gates occur in the opposite order. -/
theorem UnorderedGateArms.nonempty_currentGateBoundary {d : GateSetup} (a : UnorderedGateArms d) :
    Nonempty (CurrentGateBoundary d.driver d.C d.t) := by
  rcases le_total a.qR a.qL with h | h
  · exact ⟨a.currentGateBoundary_of_le h⟩
  · exact ⟨a.swap.currentGateBoundary_of_le h⟩

end InteractingSLE.Theorem14.GB11Chart
