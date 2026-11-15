/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsFinal
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow

/-!
# GW1's retargeting: the low connector after a completed piece of the right walk

Packet PROVE-GW1-PATH (deterministic part). After a completed piece of the right walk (instruction `2n`) followed by
another launch (instruction `2(n+1)`), the boundary continuation at instruction `2n+1` is the move along the original
real line from the new record `q` to the first later original jump `w` with high outward height (BW2, supplement
p. 615; Astra follow-up 5 §4.4, (4.8)–(4.9)), recentring the chart at `v = Re d(w)`:

* `connector_right`: `q < w`, the original data are low on `(q, w)` (`b + θχ ≤ −λ`), the next chart is the
  post-piece chart `d` recentred at `Re d(w)`, and the arc `[q, w]` is the newly recorded connector;
* `fn_low_of_rOrig`: a word that is the original word right of the record (`ROrig`, `RProf`) is low on `(0, v)`
  in the chart coordinate, `v = rProf d w`;
* `rightLim_low_of_fn_low`: the same for right limits at `[0, v)`.

These give the hypothesis of BR6 sufficiency (`lowerArcRoots`) for the post-piece word at every rational point of
`(0, v)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Connector

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The connector after a completed piece of the right walk followed by another launch.** With
`s₁ = run (2n+1)` (after the piece) and `s₂ = run (2(n+1))` (at the next launch), `w = stPt s₂`: the new point is
strictly beyond the old one, the original data are low on `(stPt s₁, w)`, the chart of `s₂` is the chart of `s₁`
recentred at `rProf (stChart s₁) w`, and the recorded connectors gain the arc `[stPt s₁, w]`. -/
theorem connector_right (hb : IsPiecewiseConstantBoundaryData b jumps) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * n + 1)).2.2.2.1 (2 * n) ≠ none)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) ≠ none)
    (hC : ClassifiedExit κ b true (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * n))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * n + 1)))
    (hang : stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * n + 1)) = θ) :
    let s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * n + 1)
    let s₂ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (2 * (n + 1))
    stPt s₁ < stPt s₂ ∧
      (∀ x, stPt s₁ < x → x < stPt s₂ → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) ∧
      stChart s₂ = (stChart s₁).recenter (rProf (stChart s₁) (stPt s₂)) ∧
      s₂.2.1 = s₁.2.1 ++ [Icc (stPt s₁) (stPt s₂)] := by
  intro s₁ s₂
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) → (R (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd D n
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch (by omega) hk hl hn
  change stStatus (R (2 * (n + 1))) = stArcM r at hstk
  -- the piece did not end the walk
  have hnd : stStatus s₁ ≠ stDone := by
    intro hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) s₁ true (Or.inr (Or.inl hd))
    change R (2 * (n + 1)) = _ at hrunk
    rw [this] at hrunk
    rw [hrunk] at hstk
    change stStatus s₁ = _ at hstk
    rw [hd] at hstk
    exact absurd hstk (by simp [stArcM])
  have hOut : OutwardThreshold κ b true s₁ := by
    rcases hC.1 with hd | ⟨-, ho⟩
    · exact absurd hd hnd
    · exact ho
  have hBad : rightLim b (stPt s₁) + stAngle s₁ * chiC κ ≤ -sleLambda κ := by
    have h := hC.2 hnd
    simpa only [BadOutwardHeight, ite_true] using h
  have heq : ExplState.contStep κ b jumps s₁ none true =
      if hC : (restartSet κ b jumps s₁).Nonempty then
        ExplState.moveAlong s₁ true ((restartSet κ b jumps s₁).min' hC) true else ExplState.moveToEnd s₁ true := by
    rcases hOut with h | ⟨h, hR⟩
    · exact contStep_thr_true' b jumps s₁ h
    · exact contStep_thr_none_right b jumps s₁ h hR
  change R (2 * (n + 1)) = ExplState.contStep κ b jumps s₁ none true at hrunk
  rw [heq] at hrunk
  split_ifs at hrunk with hCne
  swap
  · exfalso
    rw [hrunk] at hstk
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hstk (by simp [ExplState.moveToEnd, stStatus, stArcM])
  set w := (restartSet κ b jumps s₁).min' hCne with hw
  have hmem := Finset.mem_filter.1 (Finset.min'_mem _ hCne)
  have hpw : stPt s₁ < w := hmem.2.1
  have hs₂ : s₂ = ExplState.moveAlong s₁ true w true := hrunk
  have hpt₂ : stPt s₂ = w := by rw [hs₂, stPt_moveAlong]
  refine ⟨hpt₂ ▸ hpw, ?_, ?_, ?_⟩
  · intro x hx hxw hxJ
    rw [hpt₂] at hxw
    rw [← hang]
    refine add_le_neg_of_connector hb hBad (fun z hz hqz hzw => ?_) hx hxw hxJ
    by_contra hgt
    push Not at hgt
    have hz' : z ∈ restartSet κ b jumps s₁ := Finset.mem_filter.2 ⟨hz, hqz, hgt⟩
    exact absurd ((restartSet κ b jumps s₁).min'_le z hz') (not_le.2 hzw)
  · rw [hs₂, stChart_moveAlong, stPt_moveAlong]
    rfl
  · rw [hs₂, stPt_moveAlong]
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    rfl

end Connector

section Low

/-- **A word original right of the record is low on `(0, rProf w)`** when the original data are low on
`(stRecR s, w)` (deterministic; the low-side analogue of `GW1Laws.fn_bound_pos_of_rOrig`). -/
theorem fn_low_of_rOrig {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState}
    (hP : RProf s) (hO : ROrig b jumps β s) {w : ℝ} (hw : stRecR s < w)
    (hlow : ∀ x, stRecR s < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) :
    ∀ y, 0 < y → y < rProf (stChart s) w → y ∉ β.jumps → β.fn y + θ * chiC κ ≤ -sleLambda κ := by
  intro y hy hyw hyJ
  obtain ⟨x₀, hx₀, hxy⟩ := hP.exists_eq hy
  set m := rProf (stChart s) with hm
  have hx₀w : x₀ < w := by
    by_contra hge
    push Not at hge
    rcases hge.eq_or_lt with he | hlt
    · rw [he, hxy] at hyw
      exact lt_irrefl _ hyw
    · have h1 : m w < m x₀ := hP.2.1.1 hw hx₀ hlt
      rw [hxy] at h1
      linarith
  have hloc : ∀ᶠ z in 𝓝 y, β.fn z = β.fn y := β.isPiecewiseConstantBoundaryData y hyJ
  have hcont : ContinuousAt m x₀ := hP.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, stRecR s < x ∧ x < w ∧ β.fn (m x) = β.fn y := by
    refine (eventually_gt_nhds hx₀).and ((eventually_lt_nhds hx₀w).and ?_)
    have hloc' : ∀ᶠ z in 𝓝 (m x₀), β.fn z = β.fn y := by rw [hxy]; exact hloc
    exact hcont.eventually hloc'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set T : Set ℝ := {x | stRecR s < x ∧ m x ∈ β.jumps} with hTdef
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (β.jumps.finite_toSet.subset ?_) (hP.2.1.1.injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hbad : ((jumps : Set ℝ) ∪ T).Finite := jumps.finite_toSet.union hT
  obtain ⟨x, hxI, hxbad⟩ := ((Set.Ioo_infinite (by linarith : x₀ < x₀ + ε)).sdiff hbad).nonempty
  have hdist : dist x x₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxI.1, hxI.2]
  obtain ⟨hxR, hxw, hfx⟩ := hball hdist
  have hxJ : x ∉ jumps := fun h => hxbad (Or.inl h)
  have hmJ : m x ∉ β.jumps := fun h => hxbad (Or.inr ⟨hxR, h⟩)
  rw [← hfx, hO x hxR hxJ hmJ]
  exact hlow x hxR hxw hxJ

/-- **Right limits of a word low on `(0, v)`** are low at every point of `[0, v)`. -/
theorem rightLim_low_of_fn_low {κ θ : ℝ} {β : BoundaryWord} {v : ℝ}
    (hlow : ∀ y, 0 < y → y < v → y ∉ β.jumps → β.fn y + θ * chiC κ ≤ -sleLambda κ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxv : x < v) :
    rightLim β.fn x + θ * chiC κ ≤ -sleLambda κ := by
  obtain ⟨t, hxt, htv, htJ, hlim⟩ := Sec5.Aux22ChartE.exists_rightLim_eq β.isPiecewiseConstantBoundaryData hxv
  rw [hlim]
  exact hlow t (lt_of_le_of_lt hx0 hxt) htv htJ

/-- **The rational points of `(0, v)` are low-arc roots** of a word low on `(0, v)` (angle `−π/2`). -/
theorem mem_lowerArcRoots_of_fn_low {κ : ℝ} {β : BoundaryWord} {v : ℝ}
    (hlow : ∀ y, 0 < y → y < v → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ)
    (q : ℚ) (hq0 : 0 < (q : ℝ)) (hqv : (q : ℝ) < v) :
    (q : ℝ) ∈ lowerArcRoots κ β.fn β.jumps := by
  have hR : ∀ x, 0 ≤ x → x < v → rightLim β.fn x - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    intro x hx0 hxv
    have := rightLim_low_of_fn_low hlow hx0 hxv
    linarith
  unfold lowerArcRoots
  split_ifs with h0
  · exact ⟨⟨q, rfl⟩, hq0, fun x _ hx0 hxq => hR x hx0.le (lt_of_le_of_lt hxq hqv)⟩
  · exact absurd (hR 0 le_rfl (hq0.trans hqv)) h0

end Low

end InteractingSLE.Theorem14.GW1Path
