/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalIntersection

/-! # GB11: the unordered pair of actual incoming walls -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- The geometric arm data needed by the current face, with both gate orders
allowed. The source face construction is invariant under exchanging its arms. -/
structure UnorderedGateArms (d : GateSetup) where
  qR : ℝ
  qL : ℝ
  junction : ℂ
  rightWall : ℝ → ℂ
  leftWall : ℝ → ℂ
  right_continuous : ContinuousOn rightWall (Icc 0 1)
  left_continuous : ContinuousOn leftWall (Icc 0 1)
  right_injective : InjOn rightWall (Icc 0 1)
  left_injective : InjOn leftWall (Icc 0 1)
  right_zero : rightWall 0 = mu qR
  left_zero : leftWall 0 = mu qL
  right_one : rightWall 1 = junction
  left_one : leftWall 1 = junction
  wall_inter : rightWall '' Icc 0 1 ∩ leftWall '' Icc 0 1 ⊆ {rightWall 0, junction}
  wall_inter_swap : leftWall '' Icc 0 1 ∩ rightWall '' Icc 0 1 ⊆ {leftWall 0, junction}
  right_gate_old : qR ∈ oldRealBase d.driver d.γ d.t
  left_gate_old : qL ∈ oldRealBase d.driver d.γ d.t
  right_free : ∀ u ∈ Ioc (0 : ℝ) 1, rightWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (rightWall u)) ∉ d.γ '' Icc 0 d.t
  left_free : ∀ u ∈ Ioc (0 : ℝ) 1, leftWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (leftWall u)) ∉ d.γ '' Icc 0 d.t
  right_physical_outside : ∀ u ∈ Icc (0 : ℝ) 1, rightWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (rightWall u)) ∉ relDom d.C
  left_physical_outside : ∀ u ∈ Icc (0 : ℝ) 1, leftWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (leftWall u)) ∉ relDom d.C
  cover_upper : ∀ w ∈ frontier (ownDomain d.driver d.C d.t), w ∈ H →
    mu w ∈ rightWall '' Icc 0 1 ∪ leftWall '' Icc 0 1
  cover_real_off_base : ∀ x : ℝ, (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t) →
    x ∉ oldRealBase d.driver d.γ d.t → mu x ∈ rightWall '' Icc 0 1 ∪ leftWall '' Icc 0 1
  cover_zero : (0 : ℂ) ∈ frontier (mu '' ownDomain d.driver d.C d.t) →
    (0 : ℂ) ∈ rightWall '' Icc 0 1 ∪ leftWall '' Icc 0 1

/-- Exchanging the two arms preserves all of their face geometry. -/
def UnorderedGateArms.swap {d : GateSetup} (a : UnorderedGateArms d) : UnorderedGateArms d where
  qR := a.qL
  qL := a.qR
  junction := a.junction
  rightWall := a.leftWall
  leftWall := a.rightWall
  right_continuous := a.left_continuous
  left_continuous := a.right_continuous
  right_injective := a.left_injective
  left_injective := a.right_injective
  right_zero := a.left_zero
  left_zero := a.right_zero
  right_one := a.left_one
  left_one := a.right_one
  wall_inter := a.wall_inter_swap
  wall_inter_swap := a.wall_inter
  right_gate_old := a.left_gate_old
  left_gate_old := a.right_gate_old
  right_free := a.left_free
  left_free := a.right_free
  right_physical_outside := a.left_physical_outside
  left_physical_outside := a.right_physical_outside
  cover_upper := fun w hw hH => Or.symm (a.cover_upper w hw hH)
  cover_real_off_base := fun x hx hB => Or.symm (a.cover_real_off_base x hx hB)
  cover_zero := fun h0 => Or.symm (a.cover_zero h0)

/-- Exact prefix images cover any current inverse image of an unvisited
physical pocket-frontier point. -/
theorem cover_of_physical_frontier {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (hR : IsWallVisitCut d.γ d.αR d.t cutR) (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    (aR : CompactifiedPrefixArc d d.αR d.s₁ cutR)
    (aL : CompactifiedPrefixArc d d.αL d.t₁ cutL) {w : ℂ}
    (hp : -(trMap d.driver 0 d.t w)⁻¹ ∈ frontier d.C)
    (hp0 : trMap d.driver 0 d.t w ≠ 0)
    (htrace : trMap d.driver 0 d.t w ∉ d.γ '' Icc 0 d.t)
    (hcan : forwardExt d.driver d.t (trMap d.driver 0 d.t w) = w) :
    mu w ∈ aR.wall '' Icc 0 1 ∪ aL.wall '' Icc 0 1 := by
  have key : ∀ (α : ℝ≥0 → ℂ) (cut : ℝ≥0∞) (exit : ℝ≥0)
      (a : CompactifiedPrefixArc d α exit cut), α 0 = 0 → IsWallVisitCut d.γ α d.t cut →
      ∀ r : ℝ≥0, exit ≤ r → α r = -(trMap d.driver 0 d.t w)⁻¹ → mu w ∈ a.wall '' Icc 0 1 := by
    intro α cut exit a hα0 hc r hr he
    have hinv : -(α r)⁻¹ = trMap d.driver 0 d.t w := by rw [he, negInv_negInv']
    have hr0 : 0 < r := pos_iff_ne_zero.2 (fun hrzero => hp0 (by
      rw [← hinv, hrzero, hα0, inv_zero, neg_zero]))
    have hrc : (r : ℝ≥0∞) < cut := lt_of_not_ge (fun hle => by
      have hv := (mem_wallHitParameters_iff
        (Sec5.continuous_of_isGeneratingTrace_top d.generating)).1 ((hc.2 r).2 hle)
      have hm := negInv_mem_image_of_firstVisit_le
        (Sec5.continuous_of_isGeneratingTrace_top d.generating)
        (lt_of_le_of_lt hv ENNReal.coe_lt_top) hv
      exact htrace (hinv ▸ hm))
    rw [a.image, selectedPrefixImage]
    apply Or.inl
    apply Or.inr
    refine ⟨r, ⟨hr0, hr, hrc⟩, ?_⟩
    change mu (forwardExt d.driver d.t (-(α r)⁻¹)) = mu w
    rw [hinv, hcan]
  rcases d.shape.frontier_subset hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
  · exact Or.inl (key d.αR cutR d.s₁ aR d.barrier.1.2.2.1 hR r hr.1 he)
  · exact Or.inr (key d.αL cutL d.t₁ aL d.barrier.2.1.2.2.1 hL r hr.1 he)

/-- Construct the unordered actual pair from exact individual prefixes. -/
def unorderedGateArms {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (hR : IsWallVisitCut d.γ d.αR d.t cutR) (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    (aR : CompactifiedPrefixArc d d.αR d.s₁ cutR)
    (aL : CompactifiedPrefixArc d d.αL d.t₁ cutL) : UnorderedGateArms d := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver (fun r => d.γ r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace d.generating
  have hCo : IsOpen d.C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component
  have hCH : d.C ⊆ H := subset_H_of_mem_betweenComponents d.component
  have hCF : ∀ z ∈ d.C, z ∉ range d.αR ∪ range d.αL := by
    obtain ⟨y, hy, -, -, hCy⟩ := d.component
    intro z hz
    exact ((hCy ▸ connectedComponentIn_subset _ _ : d.C ⊆ H \ (range d.αR ∪ range d.αL)) hz).2
  have hLfree := aL.free d.barrier.2.1 d.barrier.2.2.2.2.2.2 hL
  have hRold := aR.gate_old hR
  have hinter := CompactifiedPrefixArc.wall_inter hR hL aR aL
  refine {
    qR := aR.q, qL := aL.q, junction := prefixJunction d d.αR d.s₁,
    rightWall := aR.wall, leftWall := aL.wall,
    right_continuous := aR.continuous, left_continuous := aL.continuous,
    right_injective := aR.injective, left_injective := aL.injective,
    right_zero := aR.zero, left_zero := aL.zero,
    right_one := aR.one, left_one := aL.one.trans d.prefixJunction_eq.symm,
    wall_inter := hinter, wall_inter_swap := ?_,
    right_gate_old := hRold, left_gate_old := aL.gate_old hL,
    right_free := aR.free d.barrier.1 d.barrier.2.2.2.2.2.1 hR, left_free := hLfree,
    right_physical_outside := aR.physical_outside d.barrier.1 d.barrier.2.2.2.2.2.1 hR
      (fun r hr => hCF _ hr (Or.inl ⟨r, rfl⟩)),
    left_physical_outside := aL.physical_outside d.barrier.2.1 d.barrier.2.2.2.2.2.2 hL
      (fun r hr => hCF _ hr (Or.inr ⟨r, rfl⟩)),
    cover_upper := ?_, cover_real_off_base := ?_, cover_zero := ?_ }
  · rintro z ⟨hzL, hzR⟩
    rcases hinter ⟨hzR, hzL⟩ with hgate | hj
    · obtain ⟨u, hu, he⟩ := hzL
      have hu0 : u = 0 := by
        by_contra hne
        have hz0 : aL.wall u ≠ 0 := by
          rw [he, hgate, aR.zero]
          exact mu_ne_zero_of_mem_Hbar (ofReal_mem_Hbar aR.q)
        have hp : muInv (aL.wall u) = (aR.q : ℂ) := by rw [he, hgate, aR.zero, muInv_mu]
        exact hLfree u ⟨lt_of_le_of_ne hu.1 (Ne.symm hne), hu.2⟩ hz0 (hp.symm ▸ hRold)
      exact Or.inl (by rw [← he, hu0])
    · exact Or.inr hj
  · intro w hw hwH
    have hz := frontier_ownDomain_inter_H hη hW hW0 hCo hCH d.t.2 hw hwH
    have hp0 : trMap d.driver 0 d.t w ≠ 0 := by
      intro he
      have hi : 0 < (trMap d.driver 0 d.t w).im := hz.2.1
      rw [he, Complex.zero_im] at hi
      exact lt_irrefl _ hi
    have hcan : forwardExt d.driver d.t (trMap d.driver 0 d.t w) = w := by
      have heq : EqOn (forwardExt d.driver d.t) (fwdMap d.driver d.t)
          (H \ fwdHull d.driver d.t) := extendFrom_extends
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW d.t.2).continuousOn
      exact (heq hz.2).trans (Sec6.fwdMap_trMap_zero hW hW0 d.t.2 hwH)
    exact cover_of_physical_frontier hR hL aR aL
      (negInv_mem_frontier_of_mem_frontier_relDom hCo hCH hz.1 hp0) hp0
      (fun hm => (trace_image_disjoint_domain d.generating d.t).le_bot ⟨hm, hz.2⟩) hcan
  · intro x hx hxB
    obtain ⟨hp, hp0⟩ := d.real_frontier_physical hx hxB
    exact cover_of_physical_frontier hR hL aR aL hp hp0 hxB (d.forwardExt_trMap_real hxB)
  · intro h0
    by_cases hs : d.s₁ = 0
    · exact Or.inl ((aR.zero_mem_image_iff d.barrier.1 d.barrier.2.2.2.2.2.1 hR).2 hs)
    · have hC0 : (0 : ℂ) ∉ closure d.C := fun hc => hs (d.exit_eq_zero_of_zero_mem_closure hc)
      have hb := isBounded_ownDomain_of_isBounded_relDom hη hW hW0 d.t.2
        (isBounded_relDom_of_zero_notMem_closure hC0)
      exact False.elim ((zero_notMem_closure_mu_ownDomain_of_isBounded hb) h0.1)

end InteractingSLE.Theorem14.GB11Chart
