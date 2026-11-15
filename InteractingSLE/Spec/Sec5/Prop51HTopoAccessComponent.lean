/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessBoundary
import InteractingSLE.WangWu.PlanarDescent
import QuantumZipper.Proofs.Complex.TopoEilenberg

/-!
# The bounded component obstructing a free positive gate

If the free gate is filled, its upper half-ball belongs to one actual bounded
component outside the closed excursion set. Its physical realization is on the
right of the proper flow arc, and its upper frontier consists of actual visible
flow points. These facts require no western-end or selected-arm assumption.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- There are no additional closed-excursion points strictly above the real
line: the visible proper arc is relatively closed in the chart half-plane. -/
theorem mem_chartFlowSet_of_mem_closure (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {z : ℂ} (hz : z ∈ closure (chartFlowSet η w s)) (hzH : z ∈ H) :
    z ∈ chartFlowSet η w s := by
  have hAH : chartFlowSet η w s ⊆ H := by
    rintro _ ⟨p, hp, rfl⟩
    exact revChart_mem_H hw hs hp.2
  have hFP : MapsTo (revChartInv w s) (chartFlowSet η w s) (arcRange η) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [revChartInv_revChart hw hw0 hs hp.2]
    exact hp.1
  have hF : ContinuousWithinAt (revChartInv w s) (chartFlowSet η w s) z :=
    ((continuousOn_revChartInv hw hw0 hs) z hzH).mono hAH
  have hzP : revChartInv w s z ∈ arcRange η := by
    have hc := hF.mem_closure hz hFP
    rwa [hη.isClosed_arcRange.closure_eq] at hc
  exact ⟨revChartInv w s z, ⟨hzP, revChartInv_mem hw hw0 hs hzH⟩,
    revChart_revChartInv hw hw0 hs hzH⟩

/-- The upper frontier of every chart complementary component is actual flow
range, not just an unspecified limiting barrier. -/
theorem frontier_chartComponent_inter_H_subset (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) (p : ℂ) :
    frontier (connectedComponentIn (H \ closure (chartFlowSet η w s)) p) ∩ H ⊆
      chartFlowSet η w s := by
  have hclosed : IsClosed (Hᶜ ∪ closure (chartFlowSet η w s)) :=
    QuantumZipper.isOpen_H.isClosed_compl.union isClosed_closure
  have heq : (Hᶜ ∪ closure (chartFlowSet η w s))ᶜ =
      H \ closure (chartFlowSet η w s) := by ext z; simp
  intro z hz
  have hm := QuantumZipper.CA.Topo.frontier_connectedComponentIn_compl_subset
    hclosed p (heq ▸ hz.1)
  exact mem_chartFlowSet_of_mem_closure hη hw hw0 hs
    (hm.resolve_left (fun hn => hn hz.2)) hz.2

/-- Exact bounded component data produced by a filled positive gate. Its
domain, connectedness, boundary coverage and physical side are all derived. -/
structure PositiveGateComponent (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) where
  gate : PositiveBoundaryGate η w s
  point : ℂ
  point_mem : point ∈ ball (gate.source : ℂ) gate.radius ∩ H
  point_avoid : point ∉ closure (chartFlowSet η w s)
  bounded : IsBounded (connectedComponentIn (H \ closure (chartFlowSet η w s)) point)
  halfBall : ball (gate.source : ℂ) gate.radius ∩ H ⊆
    connectedComponentIn (H \ closure (chartFlowSet η w s)) point

/-- Every filled free gate produces such a bounded component, rather than
assuming a selected face or an additional frontier certificate. -/
theorem PositiveBoundaryGate.exists_boundedComponent (g : PositiveBoundaryGate η w s)
    (hfilled : ball (g.source : ℂ) g.radius ∩ H ⊆ fillH (chartFlowSet η w s)) :
    ∃ c : PositiveGateComponent η w s, c.gate = g := by
  let p : ℂ := (g.source : ℂ) + (g.radius / 2 : ℝ) * I
  have hpH : p ∈ H := by
    show 0 < p.im
    simpa [p] using half_pos g.radius_pos
  have hpb : p ∈ ball (g.source : ℂ) g.radius := by
    rw [mem_ball, dist_eq_norm]
    simp only [p, add_sub_cancel_left, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs, abs_of_pos (half_pos g.radius_pos)]
    linarith [g.radius_pos]
  have hsub : ball (g.source : ℂ) g.radius ∩ H ⊆ H \ closure (chartFlowSet η w s) := by
    intro z hz
    refine ⟨hz.2, fun hzA => ?_⟩
    have hm : z ∈ ball (g.source : ℂ) g.radius ∩ closure (chartFlowSet η w s) :=
      ⟨hz.1, hzA⟩
    rwa [g.avoids] at hm
  have hpA := (hsub ⟨hpb, hpH⟩).2
  have hbound := (hfilled ⟨hpb, hpH⟩).2.resolve_left hpA
  have hpc : IsPreconnected (ball (g.source : ℂ) g.radius ∩ H) :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  exact ⟨⟨g, p, ⟨hpb, hpH⟩, hpA, hbound,
    hpc.subset_connectedComponentIn ⟨hpb, hpH⟩ hsub⟩, rfl⟩

/-- The actual chart domain of the component certificate. -/
def PositiveGateComponent.domain (c : PositiveGateComponent η w s) : Set ℂ :=
  connectedComponentIn (H \ closure (chartFlowSet η w s)) c.point

theorem PositiveGateComponent.domain_subset (c : PositiveGateComponent η w s) :
    c.domain ⊆ H \ closure (chartFlowSet η w s) := connectedComponentIn_subset _ _

theorem PositiveGateComponent.isOpen_domain (c : PositiveGateComponent η w s) :
    IsOpen c.domain := (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn

theorem PositiveGateComponent.mem_closure_domain (c : PositiveGateComponent η w s) :
    (c.gate.source : ℂ) ∈ closure c.domain :=
  closure_mono c.halfBall
    (Prop411Q.ofReal_mem_closure_ball_inter_H c.gate.source c.gate.radius_pos)

/-- A positive-gate component has its physical boundary at the actual positive
original-real point supplied by the gate. -/
theorem PositiveGateComponent.physical_access (c : PositiveGateComponent η w s) :
    (c.gate.target : ℂ) ∈ closure (revChartInv w s '' c.domain) := by
  have : (𝓝[H] (c.gate.source : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1
      (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  have he : ∀ᶠ z in 𝓝[H] (c.gate.source : ℂ),
      revChartInv w s z ∈ revChartInv w s '' c.domain := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ c.gate.radius_pos)] with z hz
    exact ⟨z, c.halfBall ⟨hz.2, hz.1⟩, rfl⟩
  exact mem_closure_of_tendsto (c.gate.boundary_limit.mono_right nhdsWithin_le_nhds) he

/-- The physical realization of a bounded gate component avoids the entire
proper arc, just as the previously constructed physical outer face does. -/
theorem PositiveGateComponent.physical_subset (c : PositiveGateComponent η w s)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    revChartInv w s '' c.domain ⊆ H \ arcRange η := by
  rintro _ ⟨z, hz, rfl⟩
  have hzD := c.domain_subset hz
  have hm := revChartInv_mem hw hw0 hs hzD.1
  refine ⟨hm.1, fun hzP => hzD.2 (subset_closure ?_)⟩
  exact ⟨revChartInv w s z, ⟨hzP, hm⟩, revChart_revChartInv hw hw0 hs hzD.1⟩

/-- Its physical realization is on the right, with no assumed side label:
the genuine positive original-real gate supplies the side, and connectedness
propagates it through the actual bounded component. -/
theorem PositiveGateComponent.physical_subset_rightSideOf (c : PositiveGateComponent η w s)
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    revChartInv w s '' c.domain ⊆ rightSideOf (arcRange η) := by
  have hsub := c.physical_subset hw hw0 hs
  have hpc : IsPreconnected (revChartInv w s '' c.domain) :=
    isPreconnected_connectedComponentIn.image _
      ((continuousOn_revChartInv hw hw0 hs).mono (fun _ hz => (c.domain_subset hz).1))
  have : (𝓝[revChartInv w s '' c.domain] (c.gate.target : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 c.physical_access
  have hmono : 𝓝[revChartInv w s '' c.domain] (c.gate.target : ℂ) ≤
      𝓝[H] (c.gate.target : ℂ) := nhdsWithin_mono _ (fun _ hz => (hsub hz).1)
  have hself : ∀ᶠ z in 𝓝[revChartInv w s '' c.domain] (c.gate.target : ℂ),
      z ∈ revChartInv w s '' c.domain := self_mem_nhdsWithin
  obtain ⟨z, hz, hzR⟩ := (hself.and
    ((Prop411Q.eventually_mem_rightSideOf hη c.gate.target_pos).filter_mono hmono)).exists
  exact Descent.subset_rightSide_of hη hpc (fun _ hv => (hsub hv).1)
    (disjoint_left.2 fun _ hv => (hsub hv).2) hz hzR

end InteractingSLE.Sec5.Prop51HTopo
