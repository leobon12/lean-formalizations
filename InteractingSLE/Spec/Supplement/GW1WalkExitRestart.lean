/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitLawL

/-! # GW1: every selected original mark is an admissible restart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

theorem admissible_min_restart {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {s : ExplState}
    (hbad : BadOutwardHeight κ b true s) (hC : (GW1W.restartSet κ b jumps s).Nonempty) :
    ExplState.IsAdmissibleSeed κ
      (leftLim b ((GW1W.restartSet κ b jumps s).min' hC))
      (rightLim b ((GW1W.restartSet κ b jumps s).min' hC)) (stAngle s) := by
  classical
  let w := (GW1W.restartSet κ b jumps s).min' hC
  have hm := Finset.mem_filter.1 ((GW1W.restartSet κ b jumps s).min'_mem hC)
  have hqw : stPt s < w := hm.2.1
  obtain ⟨x, hqx, hxw, hxJ, hlim⟩ := Sec5.Aux22ChartE.exists_leftLim_eq hb hqw
  have hlow : b x + stAngle s * chiC κ ≤ -sleLambda κ :=
    GW1W.add_le_neg_of_connector hb hbad (fun z hz hqz hzw => by
      by_contra hgt
      have hz' : z ∈ GW1W.restartSet κ b jumps s :=
        Finset.mem_filter.2 ⟨hz, hqz, lt_of_not_ge hgt⟩
      exact (not_le.2 hzw) ((GW1W.restartSet κ b jumps s).min'_le z hz')) hqx hxw hxJ
  refine ⟨?_, hm.2.2⟩
  rw [hlim]
  exact hlow.trans_lt (by linarith only [Sec4.sleLambda_pos hκ])

theorem admissible_max_restart {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {s : ExplState}
    (hbad : BadOutwardHeight κ b false s) (hC : (GW1W.restartSetL κ b jumps s).Nonempty) :
    ExplState.IsAdmissibleSeed κ
      (leftLim b ((GW1W.restartSetL κ b jumps s).max' hC))
      (rightLim b ((GW1W.restartSetL κ b jumps s).max' hC)) (stAngle s) := by
  classical
  let w := (GW1W.restartSetL κ b jumps s).max' hC
  have hm := Finset.mem_filter.1 ((GW1W.restartSetL κ b jumps s).max'_mem hC)
  have hwq : w < stPt s := hm.2.1
  obtain ⟨x, hwx, hxq, hxJ, hlim⟩ := Sec5.Aux22ChartE.exists_rightLim_eq hb hwq
  have hhigh : sleLambda κ ≤ b x + stAngle s * chiC κ :=
    GW1W.le_add_of_connector hb hbad (fun z hz hwz hzq => by
      by_contra hlt
      have hz' : z ∈ GW1W.restartSetL κ b jumps s :=
        Finset.mem_filter.2 ⟨hz, hzq, lt_of_not_ge hlt⟩
      exact (not_le.2 hwz) ((GW1W.restartSetL κ b jumps s).le_max' z hz')) hwx hxq hxJ
  refine ⟨hm.2.2, ?_⟩
  rw [hlim]
  exact (show -sleLambda κ < sleLambda κ by linarith only [Sec4.sleLambda_pos hκ]).trans_le hhigh

/-- At an even instruction a live state is the root or an admissible connector mark. -/
def LaunchReady (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) (right : Bool) (s : ExplState) : Prop :=
  stStatus s = .inl () ∨ (stStatus s = GW1W.stArcM right ∧
    ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ)

theorem contStep_launchReady_or_done {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {right : Bool} {s : ExplState} (hOut : OutwardThreshold κ b right s)
    (hBad : BadOutwardHeight κ b right s) (hAngle : stAngle s = θ) :
    stStatus (ExplState.contStep κ b jumps s none right) = stDone ∨
      LaunchReady κ b θ right (ExplState.contStep κ b jumps s none right) := by
  classical
  cases right
  · have heq : ExplState.contStep κ b jumps s none false =
        if hC : (GW1W.restartSetL κ b jumps s).Nonempty then
          ExplState.moveAlong s false ((GW1W.restartSetL κ b jumps s).max' hC) true
        else ExplState.moveToEnd s false := by
      rcases hOut with h | ⟨h, hR, hL⟩
      · exact GW1W.contStep_thr_false b jumps s h false
      · exact GW1W.contStep_thr_none_left b jumps s h hR hL
    rw [heq]
    split_ifs with hC
    · refine Or.inr (Or.inr ⟨by cases s; rfl, ?_⟩)
      rw [GW1W.stPt_moveAlong, ← hAngle]
      exact admissible_max_restart hκ hb hBad hC
    · exact Or.inl (by cases s; rfl)
  · have heq : ExplState.contStep κ b jumps s none true =
        if hC : (GW1W.restartSet κ b jumps s).Nonempty then
          ExplState.moveAlong s true ((GW1W.restartSet κ b jumps s).min' hC) true
        else ExplState.moveToEnd s true := by
      rcases hOut with h | ⟨h, hR⟩
      · exact GW1W.contStep_thr_true' b jumps s h
      · exact GW1W.contStep_thr_none_right b jumps s h hR
    rw [heq]
    split_ifs with hC
    · refine Or.inr (Or.inr ⟨by cases s; rfl, ?_⟩)
      rw [GW1W.stPt_moveAlong, ← hAngle]
      exact admissible_min_restart hκ hb hBad hC
    · exact Or.inl (by cases s; rfl)

theorem flowStep_of_launchReady {κ θ : ℝ} {b : ℝ → ℝ} {s : ExplState} {right : Bool}
    (h : LaunchReady κ b θ right s) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.flowStep κ b false s k D θ ⊤ = ExplState.launch s k D θ ⊤ := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rcases h with h | ⟨h, hadm⟩ <;> change status = _ at h <;> subst status
  · rfl
  · simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte]
    exact ite_eq_left hadm

theorem angle_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) :
    stAngle (ExplState.launch s k D θ ⊤) = θ := by
  by_cases ht : min ⊤ D.2 = ⊤
  · exact (launch_eq_of_top s k D θ ⊤ ht).2.1
  · exact (launch_eq_of_ne_top s k D θ ⊤ ht).2.1

end InteractingSLE.Theorem14.GW1WalkExit
