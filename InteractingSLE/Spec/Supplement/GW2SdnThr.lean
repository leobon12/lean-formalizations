/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VoCol

/-!
# Review defect N4, item 2 (core): a continuation threshold is a real tip at a bad point

Packet PROVE-GW2-SDE (round 13). `OpenLinesS.noThreshold` asks that no continuation threshold of the stage word occurs
along the stage driver before the cap. With NOJUMP's collision lemmas
(`Restart.FlowStopIdentLL.real_tip_of_rightImg_eq`, `rightImg_eq_iff_of_zero_collision`; `SB.Vo`), a threshold is
read off the trace, at ANY time (not only the first visit of the real line):

* **`right_threshold_real_tip`**: if the weights of the right marks (positions `≥ 0`) whose images meet the driver at
  time `t` sum to at most `−2`, the tip `p` at `t` is a real point `≥ 0`, the colliding right marks are exactly those
  at or left of `p`, and their weights sum to at most `−2`;
* **`threshold_real_tip`**: the same for the frozen `ForceWord.ThresholdCondition` of the stage driver's state (left
  images `−rightImg (−D) (−x)`): a threshold at `t` puts the tip (of `D` or of the reflected driver `−D`) at a real
  point beyond a group of marks of total weight `≤ −2`.

The remaining step of item 2 (that such a point is the chart image of a physical point of the bad set `F` of
`GW2Sdn.exists_schedVersionsA_mono_life`) reads the word map's label positions (GEOM2, D12 item 3) and BUF's
`GW2BlTrace`; see the handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Finset
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Sdn

open MartChar.RealFlow

variable {D : ℝ → ℝ} {t : ℝ} {p : ℂ}

/-- **A right threshold is a real tip beyond the colliding marks** (deterministic). -/
theorem right_threshold_real_tip (hD : Continuous D) (hD0 : D 0 = 0) (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv D t)) (htip : extendFrom H (fwdMapInv D t) 0 = p)
    {n : ℕ} {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j) {ρ : Fin n → ℝ}
    (h : ∑ j ∈ univ.filter (fun j => rightImg D (x j) t = D t), ρ j ≤ -2) :
    p.im = 0 ∧ 0 ≤ p.re ∧ ∑ j ∈ univ.filter (fun j => x j ≤ p.re), ρ j ≤ -2 := by
  classical
  have hne : (univ.filter (fun j => rightImg D (x j) t = D t)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at h
    linarith
  obtain ⟨j₀, hj₀⟩ := hne
  have hcoll : rightImg D (x j₀) t = D t := (Finset.mem_filter.1 hj₀).2
  obtain ⟨him, hxp⟩ := Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hD hD0 ht hB htip hcoll
  have hzero : rightImg D 0 t = D t :=
    le_antisymm ((rightImg_mono_index hD ht (hx j₀)).trans hcoll.le) (le_rightImg hD 0 ht)
  have hset : univ.filter (fun j => rightImg D (x j) t = D t) = univ.filter (fun j => x j ≤ p.re) :=
    Finset.filter_congr fun j _ =>
      Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hD hD0 ht hB htip hzero (x j)
  refine ⟨him, (hx j₀).trans hxp, ?_⟩
  rw [← hset]
  exact h

/-- **A continuation threshold of the stage state is a real tip beyond a bad group** (deterministic): for the frozen
`ForceWord.ThresholdCondition` at time `t` with right images `rightImg D xR` and left images
`−rightImg (−D) (−xL)` (as in `GW2Sdi.OpenLinesS.noThreshold`), either the reflected driver's tip `p'` is a real point
`≥ 0` with the left marks `−xL i ≤ p'` of total weight `≤ −2`, or the tip `p` is a real point `≥ 0` with the right marks
`xR j ≤ p` of total weight `≤ −2`. -/
theorem threshold_real_tip (hD : Continuous D) (hD0 : D 0 = 0) (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv D t)) (htip : extendFrom H (fwdMapInv D t) 0 = p) {p' : ℂ}
    (hB' : HasBdryLimits (fwdMapInv (fun v => -D v) t))
    (htip' : extendFrom H (fwdMapInv (fun v => -D v) t) 0 = p')
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (h : ForceWord.ThresholdCondition ρL ρR (D t) (fun i => -rightImg (fun v => -D v) (-xL i) t)
      (fun j => rightImg D (xR j) t)) :
    (p'.im = 0 ∧ 0 ≤ p'.re ∧ ∑ i ∈ univ.filter (fun i => -xL i ≤ p'.re), ρL i ≤ -2) ∨
      (p.im = 0 ∧ 0 ≤ p.re ∧ ∑ j ∈ univ.filter (fun j => xR j ≤ p.re), ρR j ≤ -2) := by
  classical
  rcases h with hL | hR
  · left
    have hset : univ.filter (fun i => -rightImg (fun v => -D v) (-xL i) t = D t) =
        univ.filter (fun i => rightImg (fun v => -D v) (-xL i) t = (fun v => -D v) t) :=
      Finset.filter_congr fun i _ => by constructor <;> intro h' <;> linarith
    rw [hset] at hL
    exact right_threshold_real_tip hD.neg (by simp [hD0]) ht hB' htip' (fun i => neg_nonneg.2 (hxL i)) hL
  · right
    exact right_threshold_real_tip hD hD0 ht hB htip hxR hR

end InteractingSLE.Theorem14.GW2Sdn
