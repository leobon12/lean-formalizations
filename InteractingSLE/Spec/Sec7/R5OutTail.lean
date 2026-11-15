/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCollarInf

/-!
# Source rational incident collars for outer pockets

A current nonterminal frontier point in the pocket lies on an earlier
ambient prefix. An interior rational visit sufficiently near the left stop
then has an incident half-disc disjoint from the terminal ambient trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketMarks PocketCoord PocketJordan PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopSide PocketStopMarked
  PocketStopMarked.Outer PocketStopWallsFin R5Phase R5Ref

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {A : Set Ω} {ω : Ω}

/-- The source rational incident collar, retaining its terminal trace-avoidance ball. -/
theorem exists_visit_collar_tail (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStop R L r η ψ q ω))
    (hNotExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCap R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∧
      (s : ℝ) < leftStop R L r η ψ q ω ∧
      (∃ ρ > 0, Disjoint (η ω '' Icc (s : ℝ) (leftStop R L r η ψ q ω))
        (closedBall (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ)) ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
        (relChart c (travAll R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  have hP := hcfg.toPocket hψ
  have hγ := hP.driven
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hT0 : 0 < leftStop R L r η ψ q ω :=
    hP.erase.nonneg.trans_lt (lt_ambTime0 hP (NNReal.coe_pos.2 hq0) hq')
  obtain ⟨-, -, hFrontier⟩ := current_landing hcfg hψ hc hdom heq hq ξ
  have hNowDom := current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hq hγ hc hdom heq hP.subset_H hψ.2.2.2.1
  have hTrace : frontier ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ∩
      cfPocket (R ω) (L ω) r ⊆ η ω '' Icc 0 (leftStop R L r η ψ q ω) := by
    rw [hNowDom]
    exact frontier_relDomain_subset_trace hP hq
  obtain ⟨a, ha0, haT, hHull⟩ := exists_old_interval_mem_fillH hT0 hP.subset_H
    (fun hp => hTrace ⟨hFrontier, hp⟩) hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ :=
    exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ := exists_rat_visit_lt_ambTime0 hP (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  have hTail := hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ : (visitCap R L r η ψ ω s).toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2
    (relCap_lt_of_lt_ambTime0 hP q.coe_nonneg hq' ⟨hsv.1.1.le, hsv.1.2⟩ hsT).le
  obtain ⟨-, hOld, hOldSub⟩ := visit_chart_subset hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hIncl := relChart_dom_antitone (c := c) (γ := travAll R L r η ψ) hc hγ hq hQ
  have hpHull : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ fwdHull (W ω) s := by
    rw [hcfg.trace.2.2 s hs0]
    exact hHull s (has₁.trans hs₁s)
  have hBoundary : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom :=
    fun h => (hOldSub h).2.2 (hpHull (hOldSub h).1)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_access hcfg hψ hc hdom heq hq hs0 hQ hsv.2 hBoundary hNotExit
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  obtain ⟨ε, hε, hCur⟩ := exists_old_halfDisc_in_current_component hOld hIncl hOldLanding hIncident hρ
    (disjoint_frontier_inter_old_of_trace hcfg.trace hs0 hTrace hOldSub hTail)
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩


/-- The source rational incident collar, retaining its terminal trace-avoidance ball. -/
theorem exists_visit_collarInf_tail (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStopInf R L r η ψ q ω)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCapInf R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∧
      (s : ℝ) < leftStopInf R L r η ψ q ω ∧
      (∃ ρ > 0, Disjoint (η ω '' Icc (s : ℝ) (leftStopInf R L r η ψ q ω))
        (closedBall (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ)) ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω)
        (relChart c (travAllInf R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  have hP := hcfg.toPocketInf hψ
  have hγ := hP.driven
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travAllInf R L r η ψ ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hT0 : 0 < leftStopInf R L r η ψ q ω :=
    hP.erase.nonneg.trans_lt (lt_ambTime0Inf hP (NNReal.coe_pos.2 hq0) hq')
  obtain ⟨-, -, hFrontier⟩ := current_landingInf hcfg hψ hc hdom heq hq ξ
  have hNowDom := current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hq hγ hc hdom heq hP.subset_H hψ.2.2.2.1
  have hTrace : frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∩
      cfPocket (R ω) (L ω) r ⊆ η ω '' Icc 0 (leftStopInf R L r η ψ q ω) := by
    rw [hNowDom]
    exact frontier_relDomainInf_subset_trace hP hq
  obtain ⟨a, ha0, haT, hHull⟩ := exists_old_interval_mem_fillH hT0 hP.subset_H
    (fun hp => hTrace ⟨hFrontier, hp⟩) hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ :=
    exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ := exists_rat_visitInf_lt_ambTime0Inf hP (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  have hTail := hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ : (visitCapInf R L r η ψ ω s).toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2
    (relCapInf_lt_of_lt_ambTime0Inf hP q.coe_nonneg hq' hsv.1.le hsT).le
  obtain ⟨-, hOld, hOldSub⟩ := visit_chart_subsetInf hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hIncl := relChart_dom_antitone (c := c) (γ := travAllInf R L r η ψ) hc hγ hq hQ
  have hpHull : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ fwdHull (W ω) s := by
    rw [hcfg.trace.2.2 s hs0]
    exact hHull s (has₁.trans hs₁s)
  have hBoundary : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom :=
    fun h => (hOldSub h).2.2 (hpHull (hOldSub h).1)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_accessInf hcfg hψ hc hdom heq hq hs0 hQ hsv.2 hBoundary
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  obtain ⟨ε, hε, hCur⟩ := exists_old_halfDisc_in_current_component hOld hIncl hOldLanding hIncident hρ
    (disjoint_frontier_inter_old_of_trace hcfg.trace hs0 hTrace hOldSub hTail)
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩


end InteractingSLE.Sec7.R5Out
