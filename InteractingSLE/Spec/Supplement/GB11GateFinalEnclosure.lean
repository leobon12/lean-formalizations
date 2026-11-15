/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalReal

/-! # GB11: compact old-base extrema enclose the real frontier -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The real preimage of the explored trace is compact. -/
theorem GateSetup.isCompact_oldRealBase (d : GateSetup) :
    IsCompact (oldRealBase d.driver d.γ d.t) := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hAc : IsCompact (d.γ '' Icc 0 d.t) := isCompact_Icc.image
    (Sec5.continuous_of_isGeneratingTrace_top d.generating)
  have hFc : Continuous (fun x : ℝ => trMap d.driver 0 d.t x) :=
    (YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl d.t.2).comp_continuous
      Complex.continuous_ofReal (fun x => ofReal_mem_Hbar x)
  have hclosed : IsClosed (oldRealBase d.driver d.γ d.t) := hAc.isClosed.preimage hFc
  obtain ⟨R, hR⟩ := hAc.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 d.t.2
  apply isCompact_of_isClosed_isBounded hclosed
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R + M, fun x hx => ?_⟩
  have h1 := hM x (ofReal_mem_Hbar x)
  change ‖extendFrom H (QuantumZipper.fwdMapInv d.driver d.t) x - x‖ ≤ M at h1
  rw [← YuanSimpleApprox.trMap_zero_left hW0 (d.t : ℝ)] at h1
  have h2 := hR _ hx
  have hn : ‖(x : ℂ)‖ ≤ ‖trMap d.driver 0 d.t x‖ +
      ‖trMap d.driver 0 d.t x - x‖ := by
    calc ‖(x : ℂ)‖ = ‖trMap d.driver 0 d.t x - (trMap d.driver 0 d.t x - x)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  linarith

/-- An old-base point on either selected arm is a gate. This uses only the
proved freeness of the positive part of each arm. -/
theorem SelectedGateArms.oldBase_mem_arms_iff {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) {x : ℝ}
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

/-- Away from a closed set covering the upper frontier, an adherent real point
has a full upper half-ball in the domain, and an interval of real adherence.
The proof is the connectedness of an upper half-ball and the open/closed split. -/
theorem real_frontier_collar {O J : Set ℂ} (hOo : IsOpen O) (hOH : O ⊆ H)
    (hJc : IsClosed J) (hfront : ∀ z ∈ frontier O, z ∈ H → mu z ∈ J)
    {x : ℝ} (hx : (x : ℂ) ∈ closure O) (hxJ : mu x ∉ J) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x| < ε →
      (y : ℂ) ∈ closure O ∧ mu y ∉ J := by
  have hμc : ContinuousAt mu (x : ℂ) := continuousAt_mu
    (fun he => neg_I_notMem_Hbar (he ▸ ofReal_mem_Hbar x))
  obtain ⟨ε, hε, havoid⟩ := Metric.mem_nhds_iff.1
    (hμc.preimage_mem_nhds (hJc.isOpen_compl.mem_nhds hxJ))
  have hball : ball (x : ℂ) ε ∩ H ⊆ O := by
    apply (HalfPlaneSep.isPreconnected_ball_inter_H (x : ℂ) ε).subset_left_of_subset_union
      hOo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure))
    · intro z hz
      by_cases hzO : z ∈ O
      · exact Or.inl hzO
      · exact Or.inr (fun hzcl => havoid hz.1
          (hfront z ⟨hzcl, by rwa [hOo.interior_eq]⟩ hz.2))
    · obtain ⟨z, hzO, hzx⟩ := Metric.mem_closure_iff.1 hx ε hε
      exact ⟨z, ⟨by simpa only [mem_ball, dist_comm] using hzx, hOH hzO⟩, hzO⟩
  refine ⟨ε, hε, fun y hy => ⟨closure_mono hball
    (ofReal_mem_closure_ball_inter_H hy), ?_⟩⟩
  apply havoid
  simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using hy

/-- Every adherent old-base point lies between the selected gates. An extreme
point outside the gates would have an open real collar in the compact set of
adherent old-base points, contradicting extremality. -/
theorem SelectedGateArms.oldBase_frontier_interval {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (hR : IsWallVisitCut d.γ d.αR d.t cutR)
    (hL : IsWallVisitCut d.γ d.αL d.t cutL) {x : ℝ}
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
      (fun w hw hwH => a.frontier_inter_H_subset hR hL hw hwH) hz.2 hzJ
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨hycl, hyJ⟩ := hnear y hy
    refine ⟨?_, hycl⟩
    by_contra hyB
    have hyfr : (y : ℂ) ∈ frontier O := ⟨hycl, fun hi =>
      lt_irrefl (0 : ℝ) (hOH (interior_subset hi))⟩
    exact hyJ (a.real_frontier_off_base hR hL hyfr hyB)
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
    · exact a.gates_le.trans (hm.2 hxc)
  · rcases hM_gate with rfl | rfl
    · exact (hM.2 hxc).trans a.gates_le
    · exact hM.2 hxc

/-- The selected arms and their incident old-base interval cover the real
current frontier. No new planar enclosure hypothesis remains. -/
theorem gb11GateRealEnclosureStatement : GB11GateRealEnclosureStatement := by
  intro d cutR cutL hR hL a x hx
  by_cases hxB : x ∈ oldRealBase d.driver d.γ d.t
  · exact Or.inr ⟨(x : ℂ), ⟨x, a.oldBase_frontier_interval hR hL hx.1 hxB, rfl⟩, rfl⟩
  · exact Or.inl (a.real_frontier_off_base hR hL hx hxB)

end InteractingSLE.Theorem14.GB11Chart
