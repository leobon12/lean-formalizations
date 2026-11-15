/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeEarlier

/-!
# The earlier proper arm from either contained wall

PROVE-R7-GAPEQ. The existing `cfBeta` (or its left counterpart) supplies the proper earlier
arm. Its being unvisited follows from reverse visits of that wall and target freshness.
Thus neither reverse visits of the outer wall nor a new third-arm hypothesis is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GateBridge

open WangWu Lemma71I PocketJordan PocketCoord R7GapEqCorner

/-- A reverse-visited wall's earlier prefix cannot be reached before its fresh terminal
contact. This is `wall_rev` and target freshness; no first-visit parameter regularity is used. -/
theorem earlier_prefix_unvisited {R : ℝ≥0 → ℂ} {η : ℝ → ℂ} {u σ : ℝ}
    (hR : IsSimpleProper R) (hu : 0 < u) (hu1 : u ≤ 1)
    (hη0 : η 0 = 0) (hrev : IsWallReverseVisit R η)
    (hxf : cfPt (toDisc (realPath R) u) ∉ η '' Ico 0 σ) :
    ∀ t, 0 ≤ t → t < σ → ∀ v ∈ Ici (0 : ℝ),
      η t ≠ cfPt (toDisc (realPath R) (u / (1 + v))) := by
  intro t ht htσ v hv he
  have hm := div_one_add_mem hu hv
  have hx := wall_rev hR hη0 hrev ⟨hm.1, hm.2.trans hu1⟩ ⟨hu, hu1⟩ hm.2
    (show cfPt (toDisc (realPath R) (u / (1 + v))) ∈ η '' Icc 0 t from
      ⟨t, ⟨ht, le_rfl⟩, he⟩)
  obtain ⟨q, hq, hqη⟩ := hx
  exact hxf ⟨q, ⟨hq.1, hq.2.trans_lt htσ⟩, hqη⟩

/-- **The right contained wall discharges the proper-arm input.** The left wall may be
outer: its reverse visit order is not a premise. All intersection fields are proved. -/
theorem hasProperEarlierArm_right {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {η : ℝ → ℂ} {σ : ℝ} (hη0 : η 0 = 0) (hrev : IsWallReverseVisit R η)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) :
    HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ := by
  obtain ⟨hc, hi, hβ0, ht, hH⟩ := h.cfBeta_props h0
  obtain ⟨-, hh, huh, -⟩ := h.changeCorner_props
  have hxf' : cfPt (toDisc (realPath R) (rightLo R L r)) ∉ η '' Ico 0 σ := by
    simpa only [cfArcR, zero_mul, add_zero] using hxf
  exact ⟨cfBeta R L r, hc, hi, hβ0, hH, ht,
    earlier_prefix_unvisited h.right (h.rightLo_pos h0) (huh.le.trans hh.2) hη0 hrev hxf',
    fun v hv w hw => cfArcR_inter_cfBeta h h0 hv hw,
    fun v hv w hw => cfArcL_inter_cfBeta h h0 hv hw⟩

/-- **The left contained wall also discharges the proper-arm input.** This time the right
wall may be outer. The left prefix's initial point is the common opening corner. -/
theorem hasProperEarlierArm_left {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {η : ℝ → ℂ} {σ : ℝ} (hη0 : η 0 = 0) (hrev : IsWallReverseVisit L η)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) :
    HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ := by
  obtain ⟨hc, hi, hβ0, ht, hH⟩ := cfEarlierL_props h h0
  obtain ⟨-, -, -, -, hh, huh, -⟩ := h.changeCorner_props
  have hxf' : cfPt (toDisc (realPath L) (leftLo R L r)) ∉ η '' Ico 0 σ := by
    have hf : cfArcL R L r 0 ∉ η '' Ico 0 σ := by rw [(h.isCfPocket h0).junction]; exact hxf
    simpa only [cfArcL, zero_mul, add_zero] using hf
  exact ⟨cfEarlierL R L r, hc, hi, hβ0, hH, ht,
    earlier_prefix_unvisited h.left (h.leftLo_pos h0) (huh.le.trans hh.2) hη0 hrev hxf',
    fun v hv w hw => cfArcR_inter_cfEarlierL h h0 hv hw,
    fun v hv w hw => cfArcL_inter_cfEarlierL h h0 hv hw⟩

/-- The finite mixed case needs reverse visits of just its contained wall. -/
theorem hasProperEarlierArm_of_one_reverse_wall {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {η : ℝ → ℂ} {σ : ℝ} (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit R η ∨ IsWallReverseVisit L η)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) :
    HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ := by
  rcases hrev with hrev | hrev
  · exact hasProperEarlierArm_right h h0 hη0 hrev hxf
  · exact hasProperEarlierArm_left h h0 hη0 hrev hxf

end InteractingSLE.Sec7.R7GateBridge
