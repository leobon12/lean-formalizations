/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSeedOpen

/-!
# The left-frontier fact: the right wall avoids the left side of `β` because the counterflow does

Packet PROVE-STRIPSYS23, item 5 (the inputs of `IsChangeConfigInc.isFlowChartOriented_of_leftFrontier`). Specification
§7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L476, p. 412): "The selected second arc has a nonempty
portion before `r` on the complete left frontier `β`. Both selected arcs are contained in the full counterflow range.
Its exterior left side is connected to the original domain boundary and is disjoint from those arcs".

PROVE-STRIPSYS20 proved the flow-chart orientation from `IsSimpleProper β`, `L r = β r` and
`Disjoint (range R) (leftSideOf (range β))`. This file reduces the last input to the visit of the right wall by the
counterflow (the field `visR` of `IsCfPocketConfig`, Lemma 5.7) and the **avoidance of the open left side of `β` by the
counterflow at rational times**, read in `ℍ` (`m(η)`, `m(z) = −1/z`) — the shape of the non-boundary duality statement
`Sec5.Cond44Ref.Prop51QStatement` (`cfPts p.2 s ∉ leftSideOf (range (η p.1))` for rational `s`):

* a point of the right wall at a positive time is `m(η s)` for some counterflow time `s` (`visR`), and its seed `0` is
  not in `ℍ`;
* the counterflow in `ℍ` is continuous where it is in `ℍ` and the left side is open, so avoidance at rational times
  gives avoidance at all times (`cfAvoid_of_rat`).

## Main results

* `notMem_leftSideOf_of_notMem_H`, `cfAvoid_of_rat`, `disjoint_range_of_isWallVisited`;
* **`isFlowChartOriented_of_cfAvoid`**: the flow-chart orientation from `IsSimpleProper β`, `L r = β r`, the visit of
  the right wall and the rational-time avoidance;
* `isCfPocketConfig_of_cfAvoid`, `isCfPocketConfigInf_of_cfAvoid`: the pocket configurations with the field `oriented`
  replaced by these inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketLeftFrontier

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketOrientFact PocketWordAssembly PocketSeedOpen

variable {R L β : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- The left side of a set lies in `ℍ`. -/
theorem notMem_leftSideOf_of_notMem_H {A : Set ℂ} {z : ℂ} (hz : z ∉ H) : z ∉ leftSideOf A := fun h => hz h.1.1

/-- **Avoidance at rational times gives avoidance at all times**: the counterflow read in `ℍ`, `m(η)`, is continuous
at every time where it is in `ℍ`, and the left side is open. -/
theorem cfAvoid_of_rat {A : Set ℂ} (hA : IsOpen (leftSideOf A)) (hη : ContinuousOn η (Ici 0))
    (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf A) {t : ℝ} (ht : 0 ≤ t) :
    negInv (η t) ∉ leftSideOf A := by
  intro hmem
  have hH : negInv (η t) ∈ H := hmem.1.1
  have hne : η t ≠ 0 := fun h0 => by
    rw [h0, (negInv_eq_zero_iff).2 rfl] at hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
  have hc : ContinuousWithinAt (fun s => negInv (η s)) (Ici 0) t :=
    (continuousAt_negInv hne).comp_continuousWithinAt (hη t ht)
  have hU : (fun s => negInv (η s)) ⁻¹' leftSideOf A ∈ 𝓝[Ici 0] t :=
    hc.preimage_mem_nhdsWithin (hA.mem_nhds hmem)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hU
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + ε by linarith)
  refine hq q (ht.trans hq1.le) (hball ⟨?_, ht.trans hq1.le⟩)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The right wall misses the left side of `β`** when every point of it after the seed is visited by the
counterflow (in the counterflow chart) and the counterflow, read in `ℍ`, never enters that side. -/
theorem disjoint_range_of_isWallVisited (hvis : IsWallVisited R η) (hR0 : R 0 = 0)
    (hav : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range β)) : Disjoint (range R) (leftSideOf (range β)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨a, rfl⟩ ha
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ a) with h0 | hpos
  · rw [← h0, hR0] at ha
    exact notMem_leftSideOf_of_notMem_H (fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)) ha
  · obtain ⟨t, s, hs, hηs⟩ := hvis a hpos
    have hRa : R a = negInv (η s) := by rw [hηs, WangWu.negInv_negInv]
    exact hav s hs.1 (hRa ▸ ha)

/-- **The flow-chart orientation from the left frontier and the counterflow** (Aux. lemma 130, p. 412): the left
wall's change point is the point at time `r` of a simple proper path `β`, every point of the right wall is visited by
the counterflow, and the counterflow, read in `ℍ`, avoids the open left side of `β` at rational times. -/
theorem isFlowChartOriented_of_cfAvoid (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hvis : IsWallVisited R η) (hη : ContinuousOn η (Ici 0))
    (hav : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf (range β)) : IsFlowChartOriented R L r := by
  have hopen := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange hβ.isProperArc
  rw [arcRange_realPath] at hopen
  exact h.isFlowChartOriented_of_leftFrontier hβ hLβ
    (disjoint_range_of_isWallVisited hvis h.right.2.2.1 fun t ht => cfAvoid_of_rat hopen hη hav ht)

/-- **The bounded pocket configuration with the orientation from the left frontier.** -/
theorem isCfPocketConfig_of_cfAvoid {W : ℝ → ℝ} (conf : IsChangeConfigInc R L r) (bounded : 0 < rightLo R L r)
    (trace : IsLoewnerTrace W η) (continuous_W : Continuous W) (W_zero : W 0 = 0)
    (revR : IsWallReverseVisit R η) (revL : IsWallReverseVisit L η) (visR : IsWallVisited R η)
    (attach : Sec6.AttachmentConstancy η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hav : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf (range β)) : IsCfPocketConfig R L r W η :=
  ⟨conf, bounded, isFlowChartOriented_of_cfAvoid conf hβ hLβ visR trace.2.1 hav, trace, continuous_W, W_zero, revR,
    revL, visR, attach⟩

/-- **The pocket configuration opening at the flow seed with the orientation from the left frontier.** -/
theorem isCfPocketConfigInf_of_cfAvoid {W : ℝ → ℝ} (conf : IsChangeConfigInc R L r) (seed : rightLo R L r = 0)
    (trace : IsLoewnerTrace W η) (continuous_W : Continuous W) (W_zero : W 0 = 0)
    (transient : Tendsto (fun t => ‖η t‖) atTop atTop)
    (revR : IsWallReverseVisit R η) (revL : IsWallReverseVisit L η) (visR : IsWallVisited R η)
    (visL : IsWallVisited L η)
    (attach : Sec6.AttachmentConstancyInf η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)))
    (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hav : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf (range β)) : IsCfPocketConfigInf R L r W η :=
  ⟨conf, seed, isFlowChartOriented_of_cfAvoid conf hβ hLβ visR trace.2.1 hav, trace, continuous_W, W_zero,
    transient, revR, revL, visR, visL, attach⟩

end InteractingSLE.Sec7.PocketLeftFrontier
