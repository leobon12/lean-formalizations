/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceHeights
import InteractingSLE.Spec.Supplement.GW2aContArc

/-!
# GW4: height bounds on closed connector intervals and terminal rays

The restart rule and the original one-sided exit height control every point
of the new connector outside the original jump set, including its initial
endpoint. The restart endpoint itself belongs to the jump set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkExit
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

theorem connector_right_height_closed {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState}
    (hbad : BadOutwardHeight κ b true s) (hC : (GW1W.restartSet κ b J s).Nonempty)
    {x : ℝ} (hx : x ∈ Icc (stPt s) ((GW1W.restartSet κ b J s).min' hC))
    (hxJ : x ∉ J) : b x + stAngle s * chiC κ ≤ -sleLambda κ := by
  classical
  by_cases hq : stPt s = x
  · subst x
    change rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ at hbad
    rwa [rightLim_eq_of_notMem hb hxJ] at hbad
  have hxw : x < (GW1W.restartSet κ b J s).min' hC := by
    refine lt_of_le_of_ne hx.2 ?_
    intro he
    have hm := Finset.mem_filter.1 ((GW1W.restartSet κ b J s).min'_mem hC)
    exact hxJ (he ▸ (Finset.mem_filter.1 hm.1).1)
  exact GW1W.add_le_neg_of_connector hb hbad (fun z hz hqz hzw => by
    by_contra hhigh
    have hz' : z ∈ GW1W.restartSet κ b J s :=
      Finset.mem_filter.2 ⟨hz, hqz, lt_of_not_ge hhigh⟩
    exact (not_le.2 hzw) ((GW1W.restartSet κ b J s).min'_le z hz'))
    (lt_of_le_of_ne hx.1 hq) hxw hxJ

theorem connector_right_height_ray {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState}
    (hbad : BadOutwardHeight κ b true s) (hC : ¬(GW1W.restartSet κ b J s).Nonempty)
    {x : ℝ} (hx : x ∈ Ici (stPt s)) (hxJ : x ∉ J) :
    b x + stAngle s * chiC κ ≤ -sleLambda κ := by
  classical
  by_cases hq : stPt s = x
  · subst x
    change rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ at hbad
    rwa [rightLim_eq_of_notMem hb hxJ] at hbad
  exact GW1W.add_le_neg_of_connector (w := x + 1) hb hbad (fun z hz hqz _ => by
    by_contra hhigh
    exact hC ⟨z, Finset.mem_filter.2 ⟨hz, hqz, lt_of_not_ge hhigh⟩⟩)
    (lt_of_le_of_ne hx hq) (by linarith only) hxJ

theorem connector_left_height_closed {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState}
    (hbad : BadOutwardHeight κ b false s) (hC : (GW1W.restartSetL κ b J s).Nonempty)
    {x : ℝ} (hx : x ∈ Icc ((GW1W.restartSetL κ b J s).max' hC) (stPt s))
    (hxJ : x ∉ J) : sleLambda κ ≤ b x + stAngle s * chiC κ := by
  classical
  by_cases hq : x = stPt s
  · subst x
    change sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ at hbad
    rwa [leftLim_eq_of_notMem hb hxJ] at hbad
  have hwx : (GW1W.restartSetL κ b J s).max' hC < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro he
    have hm := Finset.mem_filter.1 ((GW1W.restartSetL κ b J s).max'_mem hC)
    exact hxJ (he ▸ (Finset.mem_filter.1 hm.1).1)
  exact GW1W.le_add_of_connector hb hbad (fun z hz hwz hzq => by
    by_contra hlow
    have hz' : z ∈ GW1W.restartSetL κ b J s :=
      Finset.mem_filter.2 ⟨hz, hzq, lt_of_not_ge hlow⟩
    exact (not_le.2 hwz) ((GW1W.restartSetL κ b J s).le_max' z hz'))
    hwx (lt_of_le_of_ne hx.2 hq) hxJ

theorem connector_left_height_ray {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState}
    (hbad : BadOutwardHeight κ b false s) (hC : ¬(GW1W.restartSetL κ b J s).Nonempty)
    {x : ℝ} (hx : x ∈ Iic (stPt s)) (hxJ : x ∉ J) :
    sleLambda κ ≤ b x + stAngle s * chiC κ := by
  classical
  by_cases hq : x = stPt s
  · subst x
    change sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ at hbad
    rwa [leftLim_eq_of_notMem hb hxJ] at hbad
  exact GW1W.le_add_of_connector (w := x - 1) hb hbad (fun z hz _ hzq => by
    by_contra hlow
    exact hC ⟨z, Finset.mem_filter.2 ⟨hz, hzq, lt_of_not_ge hlow⟩⟩)
    (by linarith only) (lt_of_le_of_ne hx hq) hxJ

/-- The height invariant on the connector list, with the angle of this walk. -/
def ConnectorShiftBounds (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (right : Bool)
    (s : ExplState) : Prop :=
  ∀ a ∈ s.2.1, ∀ x ∈ a, x ∉ J →
    if right then b x + θ * chiC κ ≤ -sleLambda κ else sleLambda κ ≤ b x + θ * chiC κ

theorem connectorShiftBounds_append {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {right : Bool} {s t : ExplState} {a : Set ℝ}
    (hs : ConnectorShiftBounds κ θ b J right s) (he : t.2.1 = s.2.1 ++ [a])
    (ha : ∀ x ∈ a, x ∉ J → if right then b x + θ * chiC κ ≤ -sleLambda κ
      else sleLambda κ ≤ b x + θ * chiC κ) : ConnectorShiftBounds κ θ b J right t := by
  intro c hc x hx hxJ
  rw [he, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hs c hc x hx hxJ
  · exact ha x hx hxJ

/-- The actual continuation preserves the low/high height invariant. -/
theorem connectorShiftBounds_contStep {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {right : Bool} {s : ExplState}
    (hs : ConnectorShiftBounds κ θ b J right s) (hout : OutwardThreshold κ b right s)
    (hbad : BadOutwardHeight κ b right s) (hang : stAngle s = θ) :
    ConnectorShiftBounds κ θ b J right (ExplState.contStep κ b J s none right) := by
  classical
  cases right
  · have he : ExplState.contStep κ b J s none false =
        if hC : (GW1W.restartSetL κ b J s).Nonempty then
          ExplState.moveAlong s false ((GW1W.restartSetL κ b J s).max' hC) true
        else ExplState.moveToEnd s false := by
      rcases hout with h | ⟨h, hR, hL⟩
      · exact GW1W.contStep_thr_false b J s h false
      · exact GW1W.contStep_thr_none_left b J s h hR hL
    rw [he]
    split_ifs with hC
    · refine connectorShiftBounds_append hs rfl ?_
      intro x hx hxJ
      rw [← hang]
      exact connector_left_height_closed hb hbad hC hx hxJ
    · refine connectorShiftBounds_append hs rfl ?_
      intro x hx hxJ
      rw [← hang]
      exact connector_left_height_ray hb hbad hC hx hxJ
  · have he : ExplState.contStep κ b J s none true =
        if hC : (GW1W.restartSet κ b J s).Nonempty then
          ExplState.moveAlong s true ((GW1W.restartSet κ b J s).min' hC) true
        else ExplState.moveToEnd s true := by
      rcases hout with h | ⟨h, hR⟩
      · exact GW1W.contStep_thr_true' b J s h
      · exact GW1W.contStep_thr_none_right b J s h hR
    rw [he]
    split_ifs with hC
    · refine connectorShiftBounds_append hs rfl ?_
      intro x hx hxJ
      rw [← hang]
      exact connector_right_height_closed hb hbad hC hx hxJ
    · refine connectorShiftBounds_append hs rfl ?_
      intro x hx hxJ
      rw [← hang]
      exact connector_right_height_ray hb hbad hC hx hxJ

end InteractingSLE.Theorem14.GW4Fix
